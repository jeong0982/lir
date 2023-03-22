use crate::ir::*;
use crate::vm::calculate_c::*;
use crate::*;
use core::mem;
use itertools::izip;
use std::ops::Deref;
use thiserror::Error;

use crate::vm::vm_types::*;

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ExecutionError {
    #[error("current block is unreachable")]
    Unreachable,
    #[error("ir has no main function")]
    NoMainFunction,
    #[error("ir has no function definition of {} function", func_name)]
    NoFunctionDefinition { func_name: String },
    #[error("ir has no structure definition of {struct_name} structure")]
    NoStructureDefinition { struct_name: String },
    #[error("{func_name}:{pc} / {msg}")]
    Misc {
        func_name: String,
        pc: ProgramCounter,
        msg: String,
    },
}

impl<'i> State<'i> {
    fn step(&mut self) -> Result<Option<Value>, ExecutionError> {
        let block = self
            .stack_frame
            .func_def
            .blocks
            .get(&self.stack_frame.pc.bid)
            .expect("block matched with `bid` must be exist");

        if let Some(instr) = block.instructions.get(self.stack_frame.pc.iid) {
            self.execute_instruction(instr)?;
            return Ok(None);
        }

        // Execute a block exit.
        let return_value = some_or!(self.execute_block_exit(&block.exit)?, return Ok(None));

        // If it's returning from a function, pop the stack frame.

        // restore previous state
        let prev_stack_frame = some_or!(self.stack.pop(), return Ok(Some(return_value)));
        self.stack_frame = prev_stack_frame;

        // create temporary register to write return value
        let register = RegisterId::temp(self.stack_frame.pc.bid, self.stack_frame.pc.iid);
        self.stack_frame.registers.write(register, return_value);
        self.stack_frame.pc.inc();
        Ok(None)
    }

    fn run(&mut self) -> Result<Value, ExecutionError> {
        loop {
            if let Some(value) = self.step()? {
                return Ok(value);
            }
        }
    }

    fn new(ir: &'i TranslationUnit, args: Vec<Value>) -> Result<State<'_>, ExecutionError> {
        let func_name = String::from("main");
        let func = ir
            .decls
            .get(&func_name)
            .ok_or(ExecutionError::NoMainFunction)?;
        let (_, func_def) = func.get_function().ok_or(ExecutionError::NoMainFunction)?;
        let func_def = func_def
            .as_ref()
            .ok_or_else(|| ExecutionError::NoFunctionDefinition {
                func_name: func_name.clone(),
            })?;
        let mut state = State {
            global_map: GlobalMap::default(),
            stack_frame: StackFrame::new(func_def.bid_init, func_name, func_def),
            stack: Vec::new(),
            memory: Default::default(),
            ir,
        };
        state.alloc_global_variables()?;

        // Initialize state with main function and args
        state.write_args(func_def.bid_init, args)?;
        state.alloc_local_variables()?;

        Ok(state)
    }

    fn alloc_local_variables(&mut self) -> Result<(), ExecutionError> {
        // add alloc register
        for (id, allocation) in self.stack_frame.func_def.allocations.iter().enumerate() {
            let bid = self.memory.alloc(allocation)?;
            let ptr = Value::pointer(Some(bid), 0, allocation.deref().clone());
            let rid = RegisterId::local(id);

            self.stack_frame.registers.write(rid, ptr)
        }

        Ok(())
    }

    fn write_args(&mut self, bid_init: BlockId, args: Vec<Value>) -> Result<(), ExecutionError> {
        for (i, value) in args.iter().enumerate() {
            self.stack_frame
                .registers
                .write(RegisterId::arg(bid_init, i), value.clone());
        }

        Ok(())
    }

    fn execute_instruction(&mut self, instruction: &Instruction) -> Result<(), ExecutionError> {
        let result = match instruction {
            Instruction::Nop => Value::unit(),
            Instruction::BinOp { op, lhs, rhs, .. } => {
                let lhs = self.execute_operand(lhs)?;
                let rhs = self.execute_operand(rhs)?;

                calculate_binary_operator_expression(op, lhs, rhs).map_err(|_| {
                    ExecutionError::Misc {
                        func_name: self.stack_frame.func_name.clone(),
                        pc: self.stack_frame.pc,
                        msg: "calculate_binary_operator_expression".into(),
                    }
                })?
            }
            Instruction::UnaryOp { op, operand, .. } => {
                let operand = self.execute_operand(operand)?;

                calculate_unary_operator_expression(op, operand).map_err(|_| {
                    ExecutionError::Misc {
                        func_name: self.stack_frame.func_name.clone(),
                        pc: self.stack_frame.pc,
                        msg: "calculate_unary_operator_expression".into(),
                    }
                })?
            }
            Instruction::Save { ptr, value, .. } => {
                let ptr = self.execute_operand(ptr)?;
                let value = self.execute_operand(value)?;
                let (bid, offset, _) = self.execute_ptr(&ptr)?;
                self.memory
                    .store(bid, offset, &value)
                    .map_err(|_| ExecutionError::Misc {
                        func_name: self.stack_frame.func_name.clone(),
                        pc: self.stack_frame.pc,
                        msg: format!(
                            "fail to store {value:?} into memory with bid: {bid}, offset: {offset}",
                        ),
                    })?;
                Value::Unit
            }
            Instruction::Lookup { ptr, .. } => {
                let ptr = self.execute_operand(ptr)?;
                self.memory.load(ptr)?
            }
            Instruction::Call { callee, args, .. } => {
                let ptr = self.execute_operand(callee)?;

                // Get function name from pointer
                let (bid, _, _) = ptr.get_pointer().expect("`ptr` must be `Value::Pointer`");
                let bid = bid.expect("pointer for global variable must have bid value");
                let callee_name = self
                    .global_map
                    .get_var(bid)
                    .expect("bid must have relation with global variable");

                let func = self
                    .ir
                    .decls
                    .get(&callee_name)
                    .expect("function must be declared before being called");
                let (func_signature, func_def) = func
                    .get_function()
                    .expect("`func` must be function declaration");
                let func_def =
                    func_def
                        .as_ref()
                        .ok_or_else(|| ExecutionError::NoFunctionDefinition {
                            func_name: callee_name.clone(),
                        })?;

                let block_init = func_def
                    .blocks
                    .get(&func_def.bid_init)
                    .expect("init block must exists");

                let args = self.execute_args(func_signature, args)?;

                let stack_frame = StackFrame::new(func_def.bid_init, callee_name, func_def);
                let prev_stack_frame = mem::replace(&mut self.stack_frame, stack_frame);
                self.stack.push(prev_stack_frame);

                // Initialize state with function obtained by callee and args
                self.write_args(func_def.bid_init, args)?;
                self.alloc_local_variables()?;

                return Ok(());
            }
        };

        let register = RegisterId::temp(self.stack_frame.pc.bid, self.stack_frame.pc.iid);
        self.stack_frame.registers.write(register, result);
        self.stack_frame.pc.inc();

        Ok(())
    }

    fn execute_block_exit(
        &mut self,
        block_exit: &BlockExit,
    ) -> Result<Option<Value>, ExecutionError> {
        match block_exit {
            BlockExit::Jump { arg } => self.execute_jump(arg),
            BlockExit::ConditionalJump {
                condition,
                arg_else,
                arg_then,
            } => {
                let value = self.execute_operand(condition)?;
                let (value, width, _) = value.get_int().expect("`condition` must be `Value::Int`");
                // Check if it is boolean
                assert!(width == 1);

                self.execute_jump(if value == 1 { arg_then } else { arg_else })
            }
            BlockExit::Return { value } => Ok(Some(self.execute_operand(value)?)),
            BlockExit::Unreachable => Err(ExecutionError::Unreachable),
        }
    }

    fn alloc_global_variables(&mut self) -> Result<(), ExecutionError> {
        for (name, decl) in &self.ir.decls {
            // Memory allocation
            let bid = self.memory.alloc(&decl.dtype())?;
            self.global_map.insert(name.clone(), bid)?;

            // Initialize allocated memory space
            match decl {
                Declaration::Variable { dtype, initializer } => {
                    let value = if let Some(initializer) = initializer {
                        Value::try_from_initializer(initializer, dtype).map_err(
                            |_| ExecutionError::Misc {
                                func_name: self.stack_frame.func_name.clone(),
                                pc: self.stack_frame.pc,
                                msg: format!(
                                    "fail to translate `Initializer` and `{dtype}` to `Value`"
                                ),
                            },
                        )?
                    } else {
                        Value::default_from_dtype(dtype)
                            .expect("default value must be derived from `dtype`")
                    };
                    self.memory
                        .store(bid, 0, &value)
                        .map_err(|_| ExecutionError::Misc {
                            func_name: self.stack_frame.func_name.clone(),
                            pc: self.stack_frame.pc,
                            msg: format!(
                                "fail to store {:?} into memory with bid: {}, offset: {}",
                                value, bid, 0,
                            ),
                        })?
                }
                // If functin declaration, skip initialization
                Declaration::Function { .. } => (),
            }
        }

        Ok(())
    }

    fn execute_operand(&self, operand: &Operand) -> Result<Value, ExecutionError> {
        match operand {
            Operand::Constant(value) => Ok(self.execute_constant(value.clone())),
            Operand::Register { rid, .. } => Ok(self.stack_frame.registers.read(*rid).clone()),
        }
    }

    fn execute_constant(&self, value: Constant) -> Value {
        match value {
            Constant::GlobalVariable { name, dtype } => {
                let bid = self
                    .global_map
                    .get_bid(&name)
                    .expect("The name matching `bid` must exist.");

                // Generate appropriate pointer from `bid`
                Value::Pointer {
                    bid: Some(bid),
                    offset: 0,
                    dtype,
                }
            }
            constant => Value::try_from(constant).expect("constant must be transformed to value"),
        }
    }

    fn execute_ptr(&mut self, pointer: &Value) -> Result<(usize, isize, Dtype), ExecutionError> {
        let (bid, offset, dtype) = pointer.get_pointer().ok_or_else(|| ExecutionError::Misc {
            func_name: self.stack_frame.func_name.clone(),
            pc: self.stack_frame.pc,
            msg: "Accessing memory with non-pointer".into(),
        })?;

        let bid = bid.ok_or_else(|| ExecutionError::Misc {
            func_name: self.stack_frame.func_name.clone(),
            pc: self.stack_frame.pc,
            msg: "Accessing memory with constant pointer".into(),
        })?;

        Ok((bid, *offset, dtype.clone()))
    }

    fn execute_args(
        &self,
        signature: &FunctionSignature,
        args: &[Operand],
    ) -> Result<Vec<Value>, ExecutionError> {
        args.iter()
            .map(|a| self.execute_operand(a))
            .collect::<Result<Vec<_>, _>>()
    }

    fn execute_jump(&mut self, arg: &JumpArg) -> Result<Option<Value>, ExecutionError> {
        let block = self
            .stack_frame
            .func_def
            .blocks
            .get(&arg.bid)
            .expect("block matched with `arg.bid` must be exist");

        assert_eq!(arg.args.len(), block.phinodes.len());

        arg.args
            .iter()
            .map(|a| self.execute_operand(a).unwrap())
            .collect::<Vec<_>>()
            .into_iter()
            .enumerate()
            .for_each(|(i, v)| {
                self.stack_frame
                    .registers
                    .write(RegisterId::arg(arg.bid, i), v);
            });

        self.stack_frame.pc = ProgramCounter::new(arg.bid);
        Ok(None)
    }
}

#[inline]
pub fn execute(ir: &TranslationUnit, args: Vec<Value>) -> Result<Value, ExecutionError> {
    let mut init_state = State::new(ir, args)?;
    init_state.run()
}
