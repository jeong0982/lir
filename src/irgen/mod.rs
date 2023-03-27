use std::collections::{BTreeMap, HashMap};
use std::ops::Deref;

use core::fmt;
use core::mem;

use itertools::izip;
use lang_c::ast::*;
use lang_c::driver::Parse;
use lang_c::span::Node;
use thiserror::Error;

use crate::ir::{DtypeError, HasDtype, Named};
use crate::utils::*;
use crate::write_base::WriteString;
use crate::*;

#[derive(Debug)]
pub struct IrgenError {
    pub code: String,
    pub message: IrgenErrorMessage,
}

impl IrgenError {
    pub fn new(code: String, message: IrgenErrorMessage) -> Self {
        Self { code, message }
    }
}

impl fmt::Display for IrgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error: {}\r\n\r\ncode: {}", self.message, self.code)
    }
}

#[derive(Debug, PartialEq, Eq, Error)]
pub enum IrgenErrorMessage {
    #[error("{message}")]
    Misc { message: String },
    #[error("called object `{callee:?}` is not a function or function pointer")]
    NeedFunctionOrFunctionPointer { callee: ir::Operand },
    #[error("redefinition, `{name}`")]
    Redefinition { name: String },
    #[error("`{dtype}` conflicts prototype's dtype, `{protorype_dtype}`")]
    ConflictingDtype {
        dtype: ir::Dtype,
        protorype_dtype: ir::Dtype,
    },
    #[error("{dtype_error}")]
    InvalidDtype { dtype_error: DtypeError },
}

#[derive(Default, Debug)]
pub struct Irgen {
    decls: BTreeMap<String, ir::Declaration>,
}

impl Translate<Parse> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &Parse) -> Result<Self::Target, Self::Error> {
        self.translate(&source.unit)
    }
}

impl Translate<TranslationUnit> for Irgen {
    type Target = ir::TranslationUnit;
    type Error = IrgenError;

    fn translate(&mut self, source: &TranslationUnit) -> Result<Self::Target, Self::Error> {
        for ext_decl in &source.0 {
            match ext_decl.node {
                ExternalDeclaration::Declaration(ref var) => {
                    self.add_declaration(&var.node)?;
                }
                ExternalDeclaration::StaticAssert(_) => {
                    panic!("ExternalDeclaration::StaticAssert is unsupported")
                }
                ExternalDeclaration::FunctionDefinition(ref func) => {
                    self.add_function_definition(&func.node)?;
                }
            }
        }

        let decls = mem::take(&mut self.decls);
        Ok(Self::Target { decls })
    }
}

impl Irgen {
    const BID_INIT: ir::BlockId = ir::BlockId(0);
    // `0` is used to create `BID_INIT`
    const BID_COUNTER_INIT: usize = 1;
    const TEMPID_COUNTER_INIT: usize = 0;

    fn add_declaration(&mut self, source: &Declaration) -> Result<(), IrgenError> {
        let base_dtype = ir::Dtype::try_from_ast_declaration_specifiers(&source.specifiers)
            .map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;
        for init_decl in &source.declarators {
            let declarator = &init_decl.node.declarator.node;
            let name = name_of_declarator(declarator);
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .map_err(|e| {
                    IrgenError::new(
                        format!("{source:#?}"),
                        IrgenErrorMessage::InvalidDtype { dtype_error: e },
                    )
                })?
                .deref()
                .clone();
            let mut decl = ir::Declaration::try_from(dtype.clone()).map_err(|e| {
                IrgenError::new(
                    format!("{source:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;

            if let Some(initializer) = init_decl.node.initializer.as_ref() {
                match &mut decl {
                    ir::Declaration::Variable {
                        initializer: var_init,
                        ..
                    } => {
                        if var_init.is_some() {
                            return Err(IrgenError::new(
                                format!("{source:#?}"),
                                IrgenErrorMessage::Redefinition { name },
                            ));
                        }
                        *var_init = Some(initializer.node.clone());
                    }
                    ir::Declaration::Function { .. } => {
                        return Err(IrgenError::new(
                            format!("{source:#?}"),
                            IrgenErrorMessage::Misc {
                                message: "illegal initializer (only variables can be initialized)"
                                    .to_string(),
                            },
                        ));
                    }
                }
            }
            self.add_decl(&name, decl)?;
        }
        Ok(())
    }

    fn add_function_definition(&mut self, source: &FunctionDefinition) -> Result<(), IrgenError> {
        let specifiers = &source.specifiers;
        let declarator = &source.declarator.node;

        let name = name_of_declarator(declarator);

        let name_of_params = name_of_params_from_function_declarator(declarator)
            .expect("declarator is not from function definition");

        let base_dtype =
            ir::Dtype::try_from_ast_declaration_specifiers(specifiers).map_err(|e| {
                IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?;

        let dtype = base_dtype
            .with_ast_declarator(declarator)
            .map_err(|e| {
                IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::InvalidDtype { dtype_error: e },
                )
            })?
            .deref()
            .clone();

        let signature = ir::FunctionSignature::new(dtype.clone());

        let decl = ir::Declaration::try_from(dtype).unwrap();
        self.add_decl(&name, decl)?;

        let global_scope: HashMap<_, _> = self
            .decls
            .iter()
            .map(|(name, decl)| {
                let dtype = decl.dtype();
                let pointer = ir::Constant::global_variable(name.clone(), dtype);
                let operand = ir::Operand::constant(pointer);
                (name.clone(), operand)
            })
            .collect();

        // Prepares for irgen pass.
        let mut irgen = IrgenFunc {
            bid_init: Irgen::BID_INIT,
            phinodes_init: Vec::new(),
            allocations: Vec::new(),
            blocks: BTreeMap::new(),
            bid_counter: Irgen::BID_COUNTER_INIT,
            tempid_counter: Irgen::TEMPID_COUNTER_INIT,
            // Initial symbol table has scope for global variable already
            symbol_table: vec![global_scope],
        };
        let mut context = Context::new(irgen.bid_init);

        irgen.enter_scope();

        // Creates the init block that stores arguments.
        irgen
            .translate_parameter_decl(&signature, irgen.bid_init, &name_of_params, &mut context)
            .map_err(|e| {
                IrgenError::new(format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"), e)
            })?;

        // Translates statement.
        irgen.translate_stmt(&source.statement.node, &mut context, None, None)?;

        // Creates the end block
        let ret = signature.ret.clone();
        let value = if ret == ir::Dtype::unit() {
            ir::Operand::constant(ir::Constant::unit())
        } else if ret == ir::Dtype::INT {
            // If "main" function, default return value is `0` when return type is `int`
            if name == "main" {
                ir::Operand::constant(ir::Constant::int(0, ret))
            } else {
                ir::Operand::constant(ir::Constant::undef(ret))
            }
        } else {
            ir::Operand::constant(ir::Constant::undef(ret))
        };

        // Last Block of the function
        irgen.insert_block(context, ir::BlockExit::Return { value });

        // Exit variable scope created above
        irgen.exit_scope();

        let func_def = ir::FunctionDefinition {
            allocations: irgen.allocations,
            blocks: irgen.blocks,
            bid_init: irgen.bid_init,
        };

        let decl = self
            .decls
            .get_mut(&name)
            .unwrap_or_else(|| panic!("The declaration of `{name}` must exist"));
        if let ir::Declaration::Function { definition, .. } = decl {
            if definition.is_some() {
                return Err(IrgenError::new(
                    format!("specs: {specifiers:#?}\ndecl: {declarator:#?}"),
                    IrgenErrorMessage::Misc {
                        message: format!("the name `{name}` is defined multiple time"),
                    },
                ));
            }

            // Update function definition
            *definition = Some(func_def);
        } else {
            panic!("`{name}` must be function declaration")
        }

        Ok(())
    }

    fn add_decl(&mut self, name: &str, decl: ir::Declaration) -> Result<(), IrgenError> {
        let old_decl = some_or!(
            self.decls.insert(name.to_string(), decl.clone()),
            return Ok(())
        );
        if !old_decl.is_compatible(&decl) {
            return Err(IrgenError::new(
                name.to_string(),
                IrgenErrorMessage::ConflictingDtype {
                    dtype: old_decl.dtype(),
                    protorype_dtype: decl.dtype(),
                },
            ));
        }

        Ok(())
    }
}

#[derive(Debug)]
struct Context {
    /// The block id of the current context.
    bid: ir::BlockId,
    /// Current instructions of the block.
    instrs: Vec<Named<ir::Instruction>>,
}

impl Context {
    /// Create a new context with block number bid
    fn new(bid: ir::BlockId) -> Self {
        Self {
            bid,
            instrs: Vec::new(),
        }
    }

    // Adds `instr` to the current context.
    fn insert_instruction(
        &mut self,
        instr: ir::Instruction,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let dtype = instr.dtype();
        self.instrs.push(Named::new(None, instr));

        Ok(ir::Operand::register(
            ir::RegisterId::temp(self.bid, self.instrs.len() - 1),
            dtype,
        ))
    }
}

struct IrgenFunc {
    /// initial block id for the function, typically 0.
    bid_init: ir::BlockId,
    /// arguments represented as initial phinodes. Order must be the same of that given in the C
    /// function.
    phinodes_init: Vec<Named<ir::Dtype>>,
    /// local allocations.
    allocations: Vec<Named<ir::Dtype>>,
    /// Map from block id to basic blocks
    blocks: BTreeMap<ir::BlockId, ir::Block>,
    /// current block id. `blocks` must have an entry for all ids less then this
    bid_counter: usize,
    /// current temporary id. Used to create temporary names in the IR for e.g,
    tempid_counter: usize,
    /// Current symbol table. The initial symbol table has the global variables.
    symbol_table: Vec<HashMap<String, ir::Operand>>,
}

impl IrgenFunc {
    /// Allocate a new block id.
    fn alloc_bid(&mut self) -> ir::BlockId {
        let bid = self.bid_counter;
        self.bid_counter += 1;
        ir::BlockId(bid)
    }

    /// Allocate a new temporary id.
    fn alloc_tempid(&mut self) -> String {
        let tempid = self.tempid_counter;
        self.tempid_counter += 1;
        format!("t{tempid}")
    }

    /// Create a new allocation with type given by `alloc`.
    fn insert_alloc(&mut self, alloc: Named<ir::Dtype>) -> usize {
        self.allocations.push(alloc);
        self.allocations.len() - 1
    }

    /// Insert a new block `context` with exit instruction `exit`.
    ///
    /// # Panic
    ///
    /// Panics if another block with the same bid as `context` already existed.
    fn insert_block(&mut self, context: Context, exit: ir::BlockExit) {
        let block = ir::Block {
            phinodes: if context.bid == self.bid_init {
                self.phinodes_init.clone()
            } else {
                Vec::new()
            },
            instructions: context.instrs,
            exit,
        };
        if self.blocks.insert(context.bid, block).is_some() {
            panic!("the bid `{}` is defined multiple time", context.bid)
        }
    }

    /// Enter a scope and create a new symbol table entry, i.e, we are at a `{` in the function.
    fn enter_scope(&mut self) {
        self.symbol_table.push(HashMap::new());
    }

    /// Exit a scope and remove the a oldest symbol table entry. i.e, we are at a `}` in the
    /// function.
    ///
    /// # Panic
    ///
    /// Panics if there are no scopes to exit, i.e, the function has a unmatched `}`.
    fn exit_scope(&mut self) {
        let _unused = self.symbol_table.pop().unwrap();
    }

    /// Inserts `var` with `value` to the current symbol table.
    ///
    /// Returns Ok() if the current scope has no previously-stored entry for a given variable.
    fn insert_symbol_table_entry(
        &mut self,
        var: String,
        value: ir::Operand,
    ) -> Result<(), IrgenErrorMessage> {
        let cur_scope = self
            .symbol_table
            .last_mut()
            .expect("symbol table has no valid scope");
        if cur_scope.insert(var.clone(), value).is_some() {
            return Err(IrgenErrorMessage::Redefinition { name: var });
        }

        Ok(())
    }

    fn lookup_symbol_table(&mut self, identifier: &str) -> Result<ir::Operand, IrgenErrorMessage> {
        for tbl in &self.symbol_table {
            if let Some(value) = tbl.get(identifier) {
                return Ok(value.clone());
            } else {
                continue;
            }
        }
        Err(IrgenErrorMessage::Misc {
            message: format!("undefined identifier: {}", identifier),
        })
    }

    /// Transalte a C statement `stmt` under the current block `context`, with `continue` block
    /// `bid_continue` and break block `bid_break`.
    fn translate_stmt(
        &mut self,
        stmt: &Statement,
        context: &mut Context,
        bid_continue: Option<ir::BlockId>,
        bid_break: Option<ir::BlockId>,
    ) -> Result<(), IrgenError> {
        match stmt {
            Statement::Compound(items) => {
                self.enter_scope();
                for item in items {
                    match &item.node {
                        BlockItem::Declaration(decl) => {
                            self.translate_decl(&decl.node, context)
                                .map_err(|e| IrgenError::new("".to_string(), e))?;
                        }
                        BlockItem::StaticAssert(_) => {
                            panic!("BlockItem::StaticAssert is unsupported")
                        }
                        BlockItem::Statement(stmt) => {
                            self.translate_stmt(&stmt.node, context, bid_continue, bid_break)?;
                        }
                    }
                }

                self.exit_scope();

                Ok(())
            }
            Statement::Expression(expr) => {
                if let Some(expr) = expr {
                    let _ = self
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError::new(expr.write_string(), e))?;
                }
                Ok(())
            }
            Statement::If(stmt) => {
                let bid_then = self.alloc_bid();
                let bid_else = self.alloc_bid();
                let bid_end = self.alloc_bid();

                self.translate_condition(
                    &stmt.node.condition.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_then,
                    bid_else,
                )
                .map_err(|e| IrgenError::new(stmt.node.condition.write_string(), e))?;

                let mut context_then = Context::new(bid_then);
                self.translate_stmt(
                    &stmt.node.then_statement.node,
                    &mut context_then,
                    bid_continue,
                    bid_break,
                )?;
                self.insert_block(
                    context_then,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                let mut context_else = Context::new(bid_else);
                if let Some(else_stmt) = &stmt.node.else_statement {
                    self.translate_stmt(
                        &else_stmt.node,
                        &mut context_else,
                        bid_continue,
                        bid_break,
                    )?;
                }
                self.insert_block(
                    context_else,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );
                Ok(())
            }
            Statement::Return(expr) => {
                let value = match expr {
                    Some(expr) => self
                        .translate_expr_rvalue(&expr.node, context)
                        .map_err(|e| IrgenError::new(expr.write_string(), e))?,
                    None => ir::Operand::constant(ir::Constant::unit()),
                };
                let bid_end = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::Return { value },
                );
                Ok(())
            }
            Statement::For(for_stmt) => {
                let for_stmt = &for_stmt.node;

                let bid_init = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_init)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_init, Vec::new()),
                    },
                );
                self.enter_scope();
                self.translate_for_initializer(&for_stmt.initializer.node, context)
                    .map_err(|e| IrgenError::new(for_stmt.initializer.write_string(), e))?;

                let bid_cond = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );
                let bid_body = self.alloc_bid();
                let bid_step = self.alloc_bid();
                let bid_end = self.alloc_bid();
                self.translate_opt_condition(
                    &for_stmt.condition,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(for_stmt.condition.write_string(), e))?;

                self.enter_scope();

                let mut context_body = Context::new(bid_body);
                self.translate_stmt(
                    &for_stmt.statement.node,
                    &mut context_body,
                    Some(bid_step),
                    Some(bid_end),
                )?;

                self.exit_scope();
                self.insert_block(
                    context_body,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_step, Vec::new()),
                    },
                );

                let mut context_step = Context::new(bid_step);
                if let Some(step_expr) = &for_stmt.step {
                    let _ = self
                        .translate_expr_rvalue(&step_expr.node, &mut context_step)
                        .map_err(|e| IrgenError::new(for_stmt.step.write_string(), e))?;
                }
                self.insert_block(
                    context_step,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );
                self.exit_scope();
                Ok(())
            }
            Statement::While(while_stmt) => {
                let while_stmt = &while_stmt.node;

                let bid_cond = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );
                let bid_body = self.alloc_bid();
                let bid_end = self.alloc_bid();
                self.translate_condition(
                    &while_stmt.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(while_stmt.expression.write_string(), e))?;

                self.enter_scope();

                let mut context_body = Context::new(bid_body);
                self.translate_stmt(
                    &while_stmt.statement.node,
                    &mut context_body,
                    Some(bid_cond),
                    Some(bid_end),
                )?;
                self.insert_block(
                    context_body,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                self.exit_scope();
                Ok(())
            }
            Statement::DoWhile(do_while_stmt) => {
                let while_stmt = &do_while_stmt.node;

                let bid_body = self.alloc_bid();
                self.insert_block(
                    mem::replace(context, Context::new(bid_body)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_body, Vec::new()),
                    },
                );
                self.enter_scope();
                let bid_cond = self.alloc_bid();
                let bid_end = self.alloc_bid();
                self.translate_stmt(
                    &while_stmt.statement.node,
                    context,
                    Some(bid_cond),
                    Some(bid_end),
                )?;

                self.exit_scope();
                self.insert_block(
                    mem::replace(context, Context::new(bid_cond)),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_cond, Vec::new()),
                    },
                );

                self.translate_condition(
                    &while_stmt.expression.node,
                    mem::replace(context, Context::new(bid_end)),
                    bid_body,
                    bid_end,
                )
                .map_err(|e| IrgenError::new(while_stmt.expression.write_string(), e))?;
                Ok(())
            }
            Statement::Continue => {
                let bid_continue = bid_continue.ok_or_else(|| {
                    IrgenError::new(
                        "continue;".to_string(),
                        IrgenErrorMessage::Misc {
                            message: "continue statement not within a loop".to_string(),
                        },
                    )
                })?;
                let next_context = Context::new(self.alloc_bid());
                self.insert_block(
                    mem::replace(context, next_context),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_continue, Vec::new()),
                    },
                );
                Ok(())
            }
            Statement::Break => {
                let bid_break = bid_break.ok_or_else(|| {
                    IrgenError::new(
                        "break;".to_string(),
                        IrgenErrorMessage::Misc {
                            message: "break statement not within a loop or switch".to_string(),
                        },
                    )
                })?;

                let next_context = Context::new(self.alloc_bid());
                self.insert_block(
                    mem::replace(context, next_context),
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_break, Vec::new()),
                    },
                );

                Ok(())
            }
            _ => panic!("Unsupported statement"),
        }
    }

    fn translate_for_initializer(
        &mut self,
        initializer: &ForInitializer,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        match initializer {
            ForInitializer::Empty => (),
            ForInitializer::Expression(expr) => {
                let _ = self.translate_expr_rvalue(&expr.node, context)?;
            }
            ForInitializer::Declaration(decl) => {
                return self.translate_decl(&decl.node, context);
            }
            ForInitializer::StaticAssert(_) => {
                panic!("ForInitializer::StaticAssert is not supported")
            }
        }
        Ok(())
    }

    fn translate_opt_condition(
        &mut self,
        condition: &Option<Box<Node<Expression>>>,
        context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        if let Some(condition) = condition {
            self.translate_condition(&condition.node, context, bid_then, bid_else)
        } else {
            self.insert_block(
                context,
                ir::BlockExit::Jump {
                    arg: ir::JumpArg::new(bid_then, Vec::new()),
                },
            );
            Ok(())
        }
    }

    fn translate_decl(
        &mut self,
        decl: &Declaration,
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        let base_dtype = ir::Dtype::try_from_ast_declaration_specifiers(&decl.specifiers)
            .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;

        for init_decl in &decl.declarators {
            let declarator = &init_decl.node.declarator.node;
            let dtype = base_dtype
                .clone()
                .with_ast_declarator(declarator)
                .and_then(|dtype| {
                    let d = dtype.deref().clone();
                    Ok(d)
                })
                .map_err(|e| IrgenErrorMessage::InvalidDtype { dtype_error: e })?;
            let name = name_of_declarator(declarator);

            match &dtype {
                ir::Dtype::Unit { .. } => todo!(),
                ir::Dtype::Int { .. } | ir::Dtype::Pointer { .. } => {
                    let value = if let Some(initializer) = &init_decl.node.initializer {
                        Some(self.translate_initializer(&initializer.node, context)?)
                    } else {
                        None
                    };
                    let _ = self.translate_alloc(name, dtype.clone(), value, context)?;
                }
                ir::Dtype::Function { .. } => todo!("Function translation"),
            };
        }

        Ok(())
    }

    fn translate_alloc(
        &mut self,
        var: String,
        dtype: ir::Dtype,
        value: Option<ir::Operand>,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let id = self.insert_alloc(Named::new(Some(var.clone()), dtype.clone()));

        let pointer_type = ir::Dtype::pointer(dtype.clone());
        let rid = ir::RegisterId::local(id);
        let ptr = ir::Operand::register(rid, pointer_type);
        self.insert_symbol_table_entry(var, ptr.clone())?;

        if let Some(value) = value {
            return context.insert_instruction(ir::Instruction::Save { ptr, value });
        }

        Ok(ptr)
    }

    fn translate_initializer(
        &mut self,
        initializer: &Initializer,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match initializer {
            Initializer::Expression(expr) => self.translate_expr_rvalue(&expr.node, context),
            Initializer::List(_) => panic!("Initializer::List is unsupported"),
        }
    }

    fn translate_expr_rvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(identifier) => {
                let ptr = self.lookup_symbol_table(&identifier.node.name)?;
                let dtype_or_ptr = ptr.dtype();
                let ptr_inner_type = dtype_or_ptr
                    .get_pointer_inner()
                    .ok_or_else(|| panic!("Operand from symbol table must be pointer type"))?;
                if ptr_inner_type.get_function_inner().is_some() {
                    return Ok(ptr);
                }
                context.insert_instruction(ir::Instruction::Lookup { ptr })
            }
            Expression::Constant(constant) => {
                let constant = ir::Constant::try_from(&constant.node)
                    .expect("constant must be interpreted to ir::Constant value");
                Ok(ir::Operand::constant(constant))
            }
            Expression::StringLiteral(_string_lit) => panic!("string"),
            Expression::Call(call) => self.translate_func_call(&call.node, context),
            Expression::UnaryOperator(unary) => self.translate_unary_op(&unary.node, context),
            Expression::BinaryOperator(binary) => self.translate_binary_op(
                binary.node.operator.node.clone(),
                &binary.node.lhs.node,
                &binary.node.rhs.node,
                context,
            ),
            Expression::Conditional(cond) => self.translate_conditional(&cond.node, context),
            _ => panic!("is_unsupported"),
        }
    }
    fn translate_expr_lvalue(
        &mut self,
        expr: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match expr {
            Expression::Identifier(identifier) => self.lookup_symbol_table(&identifier.node.name),
            Expression::UnaryOperator(unary) => match &unary.node.operator.node {
                UnaryOperator::Indirection => {
                    self.translate_expr_rvalue(&unary.node.operand.node, context)
                }
                _ => Err(IrgenErrorMessage::Misc {
                    message: "This error occurred at 'IrgenFunc::translate_expr_lvalue'"
                        .to_string(),
                }),
            },
            Expression::Call(callexp) => self.translate_func_call(&callexp.deref().node, context),
            Expression::Conditional(_)
            | Expression::Constant(_)
            | Expression::Comma(_)
            | Expression::AlignOf(_)
            | Expression::Cast(_) => Err(IrgenErrorMessage::Misc {
                message: "occurred at 'translate_expr_lvalue'".to_string(),
            }),
            _ => panic!("unsupported in translate_expr_lvalue"),
        }
    }

    fn translate_assign(
        &mut self,
        operand: &Expression,
        assign: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let ptr = self.translate_expr_lvalue(operand, context)?;

        if ptr.dtype().get_pointer_inner().is_some() {
            let instr = ir::Instruction::Save {
                ptr,
                value: assign.clone(),
            };
            let _ = context.insert_instruction(instr);
            Ok(assign.clone())
        } else {
            panic!("store to different type")
        }
    }

    fn translate_conditional(
        &mut self,
        conditional_expr: &ConditionalExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let bid_then = self.alloc_bid();
        let bid_else = self.alloc_bid();
        let bid_end = self.alloc_bid();

        self.translate_condition(
            &conditional_expr.condition.node,
            mem::replace(context, Context::new(bid_end)),
            bid_then,
            bid_else,
        )?;

        let mut context_then = Context::new(bid_then);
        let val_then =
            self.translate_expr_rvalue(&conditional_expr.then_expression.node, &mut context_then)?;
        let mut context_else = Context::new(bid_else);
        let val_else =
            self.translate_expr_rvalue(&conditional_expr.else_expression.node, &mut context_else)?;

        let merged_dtype = self.merge_dtype(val_then.dtype(), val_else.dtype())?;
        let var = self.alloc_tempid();
        let ptr = self.translate_alloc(var, merged_dtype, None, context)?;

        let _ = context_then.insert_instruction(ir::Instruction::Save {
            ptr: ptr.clone(),
            value: val_then,
        });
        self.insert_block(
            context_then,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );

        let _ = context_else.insert_instruction(ir::Instruction::Save {
            ptr: ptr.clone(),
            value: val_else,
        });
        self.insert_block(
            context_else,
            ir::BlockExit::Jump {
                arg: ir::JumpArg::new(bid_end, Vec::new()),
            },
        );
        context.insert_instruction(ir::Instruction::Lookup { ptr })
    }

    fn merge_dtype(
        &mut self,
        dtype1: ir::Dtype,
        dtype2: ir::Dtype,
    ) -> Result<ir::Dtype, IrgenErrorMessage> {
        if dtype1 == dtype2 {
            Ok(dtype1.clone())
        } else {
            match (&dtype1, &dtype2) {
                (ir::Dtype::Unit { .. }, ir::Dtype::Unit { .. }) => Ok(dtype1.clone()),
                (
                    ir::Dtype::Int {
                        width: width1,
                        is_signed: s1,
                        ..
                    },
                    ir::Dtype::Int {
                        width: width2,
                        is_signed: s2,
                        ..
                    },
                ) => {
                    if width1.clone() > width2.clone() {
                        if width1.clone() > 4 {
                            Ok(dtype1.clone())
                        } else if width1.clone() == 4 {
                            Ok(ir::Dtype::Int {
                                width: 4,
                                is_signed: s1.clone(),
                            })
                        } else {
                            Ok(ir::Dtype::INT)
                        }
                    } else if width2.clone() > 4 {
                        Ok(dtype2.clone())
                    } else if width2.clone() == 4 {
                        Ok(ir::Dtype::Int {
                            width: 4,
                            is_signed: s2.clone(),
                        })
                    } else {
                        Ok(ir::Dtype::INT)
                    }
                }
                (ir::Dtype::Pointer { inner, .. }, _) => {
                    self.merge_dtype(inner.deref().clone(), dtype2)
                }
                (_, ir::Dtype::Pointer { inner, .. }) => {
                    self.merge_dtype(dtype1, inner.deref().clone())
                }
                _ => Ok(dtype1.clone()),
            }
        }
    }

    fn translate_binary_op(
        &mut self,
        op: BinaryOperator,
        lhs: &Expression,
        rhs: &Expression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        match op {
            BinaryOperator::Equals
            | BinaryOperator::Greater
            | BinaryOperator::GreaterOrEqual
            | BinaryOperator::Less
            | BinaryOperator::LessOrEqual
            | BinaryOperator::NotEquals => {
                let lhs = self.translate_expr_rvalue(lhs, context)?;
                let rhs = self.translate_expr_rvalue(rhs, context)?;
                let dtype = ir::Dtype::Int {
                    width: 1,
                    is_signed: false,
                };
                let instr = ir::Instruction::BinOp {
                    op,
                    lhs,
                    rhs,
                    dtype,
                };
                let operand = context.insert_instruction(instr)?;

                return Ok(operand);
            }
            BinaryOperator::LogicalAnd => {
                let bid_then = self.alloc_bid();
                let bid_else = self.alloc_bid();
                let bid_end = self.alloc_bid();

                let dtype = ir::Dtype::Int {
                    width: 1,
                    is_signed: false,
                };

                let lhs = self.translate_expr_rvalue(lhs, context)?;
                let lop = self.translate_typecast_to_bool(lhs.clone(), context)?;

                self.insert_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::ConditionalJump {
                        condition: lop.clone(),
                        arg_then: ir::JumpArg::new(bid_then, Vec::new()),
                        arg_else: ir::JumpArg::new(bid_else, Vec::new()),
                    },
                );

                let mut context_then = Context::new(bid_then);
                let mut context_else = Context::new(bid_else);

                let var = self.alloc_tempid();
                let ptr = self.translate_alloc(var, dtype, None, context)?;
                let instr = ir::Instruction::Lookup { ptr: ptr.clone() };
                let constant_zero = ir::Operand::constant(ir::Constant::int(0, ir::Dtype::BOOL));
                let operand = context.insert_instruction(instr)?;
                let alloc_instr = ir::Instruction::Save {
                    ptr: ptr.clone(),
                    value: constant_zero,
                };
                let _ = context_else.insert_instruction(alloc_instr);

                self.insert_block(
                    context_else,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                let rhs = self.translate_expr_rvalue(rhs, &mut context_then)?;
                let rop = self.translate_typecast_to_bool(rhs, &mut context_then)?;

                let alloc_instr = ir::Instruction::Save {
                    ptr: ptr.clone(),
                    value: rop,
                };
                let _ = context_then.insert_instruction(alloc_instr)?;

                self.insert_block(
                    context_then,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                return Ok(operand);
            }
            BinaryOperator::LogicalOr => {
                let bid_then = self.alloc_bid();
                let bid_else = self.alloc_bid();
                let bid_end = self.alloc_bid();

                let dtype = ir::Dtype::Int {
                    width: 1,
                    is_signed: false,
                };

                let lhs = self.translate_expr_rvalue(lhs, context)?;
                let lop = self.translate_typecast_to_bool(lhs.clone(), context)?;

                self.insert_block(
                    mem::replace(context, Context::new(bid_end)),
                    ir::BlockExit::ConditionalJump {
                        condition: lop.clone(),
                        arg_then: ir::JumpArg::new(bid_then, Vec::new()),
                        arg_else: ir::JumpArg::new(bid_else, Vec::new()),
                    },
                );

                let mut context_then = Context::new(bid_then);
                let mut context_else = Context::new(bid_else);

                let var = self.alloc_tempid();
                let ptr = self.translate_alloc(var, dtype, None, context)?;
                let instr = ir::Instruction::Lookup { ptr: ptr.clone() };
                let constant_one = ir::Operand::constant(ir::Constant::int(1, ir::Dtype::BOOL));
                let operand = context.insert_instruction(instr)?;
                let alloc_instr = ir::Instruction::Save {
                    ptr: ptr.clone(),
                    value: constant_one,
                };
                let _ = context_then.insert_instruction(alloc_instr);

                self.insert_block(
                    context_then,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                let rhs = self.translate_expr_rvalue(rhs, &mut context_else)?;
                let rop = self.translate_typecast_to_bool(rhs, &mut context_else)?;

                let alloc_instr = ir::Instruction::Save {
                    ptr: ptr.clone(),
                    value: rop,
                };
                let _ = context_else.insert_instruction(alloc_instr)?;

                self.insert_block(
                    context_else,
                    ir::BlockExit::Jump {
                        arg: ir::JumpArg::new(bid_end, Vec::new()),
                    },
                );

                return Ok(operand);
            }
            BinaryOperator::AssignBitwiseAnd
            | BinaryOperator::AssignBitwiseOr
            | BinaryOperator::AssignBitwiseXor
            | BinaryOperator::AssignDivide
            | BinaryOperator::AssignMinus
            | BinaryOperator::AssignModulo
            | BinaryOperator::AssignMultiply
            | BinaryOperator::AssignPlus
            | BinaryOperator::AssignShiftLeft => {
                let operator = bin_arith_op_of_bin_assignment_op(&op);
                let lhs_operand = self.translate_expr_rvalue(lhs, context)?;
                let rhs = self.translate_expr_rvalue(rhs, context)?;
                let lhs_dtype = lhs_operand.dtype();
                let instr = ir::Instruction::BinOp {
                    op: operator,
                    lhs: lhs_operand,
                    rhs,
                    dtype: lhs_dtype,
                };
                let operand_calculate = context.insert_instruction(instr)?;
                let operand = self.translate_assign(lhs, operand_calculate, context)?;
                return Ok(operand);
            }
            BinaryOperator::Assign => {
                let rhs = self.translate_expr_rvalue(rhs, context)?;
                let lhs = self.translate_assign(lhs, rhs.clone(), context)?;
                return Ok(lhs);
            }
            _ => (),
        };
        let lhs = self.translate_expr_rvalue(lhs, context)?;
        let rhs = self.translate_expr_rvalue(rhs, context)?;
        let lhs_dtype = lhs.dtype();
        let rhs_dtype = rhs.dtype();
        let dtype = self.merge_dtype(lhs_dtype.clone(), rhs_dtype.clone())?;
        let instr = ir::Instruction::BinOp {
            op,
            lhs,
            rhs,
            dtype,
        };
        let operand = context.insert_instruction(instr)?;

        Ok(operand)
    }

    fn translate_unary_op(
        &mut self,
        operation: &UnaryOperatorExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let operator = &operation.operator.node;
        let operand_to = &operation.operand.deref().node;
        match operator {
            UnaryOperator::PostDecrement | UnaryOperator::PostIncrement => {
                let operator = bin_op_of_unary_modify_op(operator);
                let operand = self.translate_expr_rvalue(&operand_to, context)?;
                let dtype = operand.dtype();

                let one = ir::Operand::constant(ir::Constant::int(1, ir::Dtype::INT));
                let instr = ir::Instruction::BinOp {
                    op: operator,
                    lhs: operand.clone(),
                    rhs: one,
                    dtype,
                };
                let op = context.insert_instruction(instr)?;
                self.translate_assign(operand_to, op, context)?;
                Ok(operand)
            }
            UnaryOperator::PreIncrement | UnaryOperator::PreDecrement => {
                let operator = bin_op_of_unary_modify_op(operator);
                let operand = self.translate_expr_rvalue(&operand_to, context)?;
                let dtype = operand.dtype();

                let one = ir::Operand::constant(ir::Constant::int(1, ir::Dtype::INT));
                let instr = ir::Instruction::BinOp {
                    op: operator,
                    lhs: operand,
                    rhs: one,
                    dtype,
                };
                let op = context.insert_instruction(instr)?;
                self.translate_assign(operand_to, op.clone(), context)?;
                Ok(op)
            }
            UnaryOperator::Address => self.translate_expr_lvalue(operand_to, context),
            UnaryOperator::Indirection => {
                let lv = self.translate_expr_rvalue(&operand_to, context)?;
                let instr = ir::Instruction::Lookup { ptr: lv };
                let operand = context.insert_instruction(instr)?;
                Ok(operand)
            }
            _ => {
                let operand = self.translate_expr_rvalue(&operand_to, context)?;
                let dtype = operand.dtype();
                let instr = ir::Instruction::UnaryOp {
                    op: operator.clone(),
                    operand,
                    dtype,
                };
                let operand = context.insert_instruction(instr)?;
                Ok(operand)
            }
        }
    }

    fn translate_condition(
        &mut self,
        condition: &Expression,
        mut context: Context,
        bid_then: ir::BlockId,
        bid_else: ir::BlockId,
    ) -> Result<(), IrgenErrorMessage> {
        let condition = self.translate_expr_rvalue(condition, &mut context)?;
        let condition = self.translate_typecast_to_bool(condition, &mut context)?;

        self.insert_block(
            context,
            ir::BlockExit::ConditionalJump {
                condition,
                arg_then: ir::JumpArg::new(bid_then, Vec::new()),
                arg_else: ir::JumpArg::new(bid_else, Vec::new()),
            },
        );
        Ok(())
    }

    fn translate_func_call(
        &mut self,
        call: &CallExpression,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let callee = self.translate_expr_rvalue(&call.callee.node, context)?;
        let function_pointer_type = callee.dtype();
        let function = function_pointer_type.get_pointer_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer {
                callee: callee.clone(),
            }
        })?;
        let (return_type, parameters) = function.get_function_inner().ok_or_else(|| {
            IrgenErrorMessage::NeedFunctionOrFunctionPointer {
                callee: callee.clone(),
            }
        })?;
        let args = call
            .arguments
            .iter()
            .map(|a| self.translate_expr_rvalue(&a.node, context))
            .collect::<Result<Vec<_>, _>>()?;

        if args.len() != parameters.len() {
            return Err(IrgenErrorMessage::Misc {
                message: "too few arguments to function ".to_string(),
            });
        }
        let args = izip!(args, parameters)
            .map(|(a, p)| {
                if a.dtype() == p.clone() || is_compatible_dtype(&a.dtype(), p) {
                    Ok(a)
                } else {
                    Err(IrgenErrorMessage::Misc {
                        message: format!("uncompatible types: {}, {}", a.dtype(), p),
                    })
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let return_type = return_type.clone();
        context.insert_instruction(ir::Instruction::Call {
            callee,
            args,
            return_type,
        })
    }

    fn translate_parameter_decl(
        &mut self,
        signature: &ir::FunctionSignature,
        bid_init: ir::BlockId,
        name_of_params: &[String],
        context: &mut Context,
    ) -> Result<(), IrgenErrorMessage> {
        if signature.params.len() != name_of_params.len() {
            panic!("length of 'parameters' and 'name_of_params' must be same")
        }
        for (i, (dtype, var)) in izip!(&signature.params, name_of_params).enumerate() {
            let value = Some(ir::Operand::register(
                ir::RegisterId::arg(bid_init, i),
                dtype.clone(),
            ));
            let _ = self.translate_alloc(var.clone(), dtype.clone(), value, context)?;
            self.phinodes_init
                .push(Named::new(Some(var.clone()), dtype.clone()));
        }
        Ok(())
    }

    fn translate_typecast_to_bool(
        &mut self,
        value: ir::Operand,
        context: &mut Context,
    ) -> Result<ir::Operand, IrgenErrorMessage> {
        let dtype = ir::Dtype::Int {
            width: 1,
            is_signed: false,
        };
        if value.dtype() == dtype {
            Ok(value)
        } else if value.dtype() == ir::Dtype::INT {
            let instr = ir::Instruction::BinOp {
                op: BinaryOperator::NotEquals,
                lhs: value,
                rhs: ir::Operand::constant(ir::Constant::int(0, ir::Dtype::INT)),
                dtype,
            };
            let operand = context.insert_instruction(instr)?;
            Ok(operand)
        } else {
            Err(IrgenErrorMessage::Misc {
                message: "Not a int type in condition".to_string(),
            })
        }
    }
}

#[inline]
fn name_of_declarator(declarator: &Declarator) -> String {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(identifier) => identifier.node.name.clone(),
        DeclaratorKind::Declarator(declarator) => name_of_declarator(&declarator.node),
    }
}

#[inline]
fn name_of_params_from_function_declarator(declarator: &Declarator) -> Option<Vec<String>> {
    let declarator_kind = &declarator.kind;
    match &declarator_kind.node {
        DeclaratorKind::Abstract => panic!("DeclaratorKind::Abstract is unsupported"),
        DeclaratorKind::Identifier(_) => {
            name_of_params_from_derived_declarators(&declarator.derived)
        }
        DeclaratorKind::Declarator(next_declarator) => {
            name_of_params_from_function_declarator(&next_declarator.node)
                .or_else(|| name_of_params_from_derived_declarators(&declarator.derived))
        }
    }
}

#[inline]
fn name_of_params_from_derived_declarators(
    derived_decls: &[Node<DerivedDeclarator>],
) -> Option<Vec<String>> {
    for derived_decl in derived_decls {
        match &derived_decl.node {
            DerivedDeclarator::Function(func_decl) => {
                let name_of_params = func_decl
                    .node
                    .parameters
                    .iter()
                    .map(|p| name_of_parameter_declaration(&p.node))
                    .collect::<Option<Vec<_>>>()
                    .unwrap_or_default();
                return Some(name_of_params);
            }
            DerivedDeclarator::KRFunction(_kr_func_decl) => {
                return Some(Vec::new());
            }
            _ => (),
        };
    }

    None
}

#[inline]
fn name_of_parameter_declaration(parameter_declaration: &ParameterDeclaration) -> Option<String> {
    let declarator = some_or!(parameter_declaration.declarator.as_ref(), return None);
    Some(name_of_declarator(&declarator.node))
}

fn is_compatible_dtype(dtype1: &ir::Dtype, dtype2: &ir::Dtype) -> bool {
    match (dtype1, dtype2) {
        (ir::Dtype::Pointer { inner: inner1, .. }, ir::Dtype::Pointer { inner: inner2, .. }) => {
            is_compatible_dtype(inner1.deref(), inner2.deref())
        }
        (ir::Dtype::Unit { .. }, ir::Dtype::Unit { .. }) => true,
        (
            ir::Dtype::Int {
                width: w1,
                is_signed: s1,
                ..
            },
            ir::Dtype::Int {
                width: w2,
                is_signed: s2,
                ..
            },
        ) => w1 == w2 && s1 == s2,
        _ => false,
    }
}

fn bin_arith_op_of_bin_assignment_op(op: &BinaryOperator) -> BinaryOperator {
    match &op {
        BinaryOperator::AssignMultiply => BinaryOperator::Multiply,
        BinaryOperator::AssignDivide => BinaryOperator::Divide,
        BinaryOperator::AssignModulo => BinaryOperator::Modulo,
        BinaryOperator::AssignPlus => BinaryOperator::Plus,
        BinaryOperator::AssignMinus => BinaryOperator::Minus,
        BinaryOperator::AssignShiftLeft => BinaryOperator::ShiftLeft,
        BinaryOperator::AssignShiftRight => BinaryOperator::ShiftRight,
        BinaryOperator::AssignBitwiseAnd => BinaryOperator::BitwiseAnd,
        BinaryOperator::AssignBitwiseOr => BinaryOperator::BitwiseOr,
        BinaryOperator::AssignBitwiseXor => BinaryOperator::BitwiseXor,
        _ => panic!("{:?} is not assignment operator", op),
    }
}

fn bin_op_of_unary_modify_op(op: &UnaryOperator) -> BinaryOperator {
    match &op {
        UnaryOperator::PreIncrement => BinaryOperator::Plus,
        UnaryOperator::PostIncrement => BinaryOperator::Plus,
        UnaryOperator::PreDecrement => BinaryOperator::Minus,
        UnaryOperator::PostDecrement => BinaryOperator::Minus,
        _ => panic!("{:?} is not pre-(or post-) unary operator", op),
    }
}
