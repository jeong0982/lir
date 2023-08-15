mod dtype;
mod write_ir;

pub use dtype::{Dtype, DtypeError, HasDtype};

use core::ops::{Deref, DerefMut};
use itertools::Itertools;
use lang_c::ast;
use std::collections::BTreeMap;
use std::fmt;

use crate::write_base::*;

#[derive(Debug, Clone, PartialEq)]
pub struct TranslationUnit {
    pub decls: BTreeMap<String, Declaration>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Variable {
        dtype: Dtype,
        initializer: Option<ast::Initializer>,
    },
    Function {
        signature: FunctionSignature,
        definition: Option<FunctionDefinition>,
    },
}

impl TryFrom<Dtype> for Declaration {
    type Error = DtypeError;

    /// Create an appropriate declaration according to `dtype`.
    ///
    /// # Example
    ///
    /// If `int g = 0;` is declared, `dtype` is `ir::Dtype::Int{ width:32, is_signed:true,
    /// is_const:false }`.
    ///
    /// In this case, `ir::Declaration::Variable{ dtype, initializer:
    /// Some(Constant::I32(1)) }` is generated.
    ///
    /// Conversely, if `int foo();` is declared, `dtype` is `ir::Dtype::Function{ret: Scalar(Int),
    /// params: []}`. Thus, in this case, `ir::Declaration::Function` is generated.
    fn try_from(dtype: Dtype) -> Result<Self, Self::Error> {
        match &dtype {
            Dtype::Unit { .. } => Err(DtypeError::Misc {
                message: "A variable of type `void` cannot be declared".to_string(),
            }),
            Dtype::Int { .. } => Ok(Declaration::Variable {
                dtype,
                initializer: None,
            }),
            Dtype::Function { .. } => Ok(Declaration::Function {
                signature: FunctionSignature::new(dtype),
                definition: None,
            }),
        }
    }
}

impl Declaration {
    pub fn get_variable(&self) -> Option<(&Dtype, &Option<ast::Initializer>)> {
        if let Self::Variable { dtype, initializer } = self {
            Some((dtype, initializer))
        } else {
            None
        }
    }

    pub fn get_function(&self) -> Option<(&FunctionSignature, &Option<FunctionDefinition>)> {
        if let Self::Function {
            signature,
            definition,
        } = self
        {
            Some((signature, definition))
        } else {
            None
        }
    }

    pub fn is_compatible(&self, other: &Declaration) -> bool {
        match (self, other) {
            (Self::Variable { dtype, .. }, Self::Variable { dtype: other, .. }) => dtype == other,
            (
                Self::Function { signature, .. },
                Self::Function {
                    signature: other, ..
                },
            ) => signature.dtype() == other.dtype(),
            _ => false,
        }
    }

    pub fn get_function_mut(
        &mut self,
    ) -> Option<(&mut FunctionSignature, &mut Option<FunctionDefinition>)> {
        if let Self::Function {
            signature,
            definition,
        } = self
        {
            Some((signature, definition))
        } else {
            None
        }
    }
}

impl HasDtype for Declaration {
    fn dtype(&self) -> Dtype {
        match self {
            Self::Variable { dtype, .. } => dtype.clone(),
            Self::Function { signature, .. } => signature.dtype(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSignature {
    pub ret: Dtype,
    pub params: Vec<Dtype>,
}

impl FunctionSignature {
    pub fn new(dtype: Dtype) -> Self {
        let (ret, params) = dtype
            .get_function_inner()
            .expect("function signature's dtype must be function type");
        Self {
            ret: ret.clone(),
            params: params.clone(),
        }
    }
}

impl HasDtype for FunctionSignature {
    fn dtype(&self) -> Dtype {
        Dtype::function(self.ret.clone(), self.params.clone())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDefinition {
    pub starting_rid: usize,
    /// Memory allocations for local variables.  The allocation is performed at the beginning of a
    /// function invocation.
    pub allocations: Vec<Named<Dtype>>,

    /// Basic blocks.
    pub blocks: BTreeMap<BlockId, Block>,

    /// The initial block id.
    pub bid_init: BlockId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    Nop,
    BinOp {
        op: ast::BinaryOperator,
        lhs: Operand,
        rhs: Operand,
        dtype: Dtype,
    },
    UnaryOp {
        op: ast::UnaryOperator,
        operand: Operand,
        dtype: Dtype,
    },
    Lookup {
        operand: Operand,
    },
    Save {
        operand: Operand,
        value: Operand,
    },
    Call {
        callee: Operand,
        args: Vec<Operand>,
        return_type: Dtype,
    },
}

impl HasDtype for Instruction {
    fn dtype(&self) -> Dtype {
        match self {
            Self::Nop | Self::Save { .. } => Dtype::unit(),
            Self::BinOp { dtype, .. }
            | Self::UnaryOp { dtype, .. }
            | Self::Call {
                return_type: dtype, ..
            } => dtype.clone(),
            Self::Lookup { operand } => operand.dtype().clone(),
        }
    }
}

impl WriteOp for ast::BinaryOperator {
    fn write_operation(&self) -> String {
        match self {
            Self::Multiply => "mul",
            Self::Divide => "div",
            Self::Modulo => "mod",
            Self::Plus => "add",
            Self::Minus => "sub",
            Self::ShiftLeft => "shl",
            Self::ShiftRight => "shr",
            Self::Equals => "cmp eq",
            Self::NotEquals => "cmp ne",
            Self::Less => "cmp lt",
            Self::LessOrEqual => "cmp le",
            Self::Greater => "cmp gt",
            Self::GreaterOrEqual => "cmp ge",
            Self::BitwiseAnd => "and",
            Self::BitwiseXor => "xor",
            Self::BitwiseOr => "or",
            _ => todo!(
                "ast::BinaryOperator::WriteOp: write operation for {:?} is needed",
                self
            ),
        }
        .to_string()
    }
}

impl WriteOp for ast::UnaryOperator {
    fn write_operation(&self) -> String {
        match self {
            Self::Plus => "plus",
            Self::Minus => "minus",
            Self::Negate => "negate",
            _ => todo!(
                "ast::UnaryOperator::WriteOp: write operation for {:?} is needed",
                self
            ),
        }
        .to_string()
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Nop => write!(f, "nop"),
            Instruction::BinOp { op, lhs, rhs, .. } => {
                write!(f, "{} {} {}", op.write_operation(), lhs, rhs)
            }
            Instruction::UnaryOp { op, operand, .. } => {
                write!(f, "{} {}", op.write_operation(), operand)
            }
            Instruction::Save { operand, value } => write!(f, "save {value} {operand}"),
            Instruction::Lookup { operand } => write!(f, "lookup {operand}"),
            Instruction::Call { callee, args, .. } => {
                write!(
                    f,
                    "call {}({})",
                    callee,
                    args.iter()
                        .format_with(", ", |operand, f| f(&format_args!("{operand}")))
                )
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Constant(Constant),
    Register { rid: RegisterId, dtype: Dtype },
}

impl Operand {
    pub fn constant(value: Constant) -> Self {
        Self::Constant(value)
    }

    pub fn register(rid: RegisterId, dtype: Dtype) -> Self {
        Self::Register { rid, dtype }
    }

    pub fn get_constant(&self) -> Option<&Constant> {
        if let Self::Constant(constant) = self {
            Some(constant)
        } else {
            None
        }
    }

    pub fn get_register(&self) -> Option<(&RegisterId, &Dtype)> {
        if let Self::Register { rid, dtype } = self {
            Some((rid, dtype))
        } else {
            None
        }
    }

    pub fn get_register_mut(&mut self) -> Option<(&mut RegisterId, &mut Dtype)> {
        if let Self::Register { rid, dtype } = self {
            Some((rid, dtype))
        } else {
            None
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(value) => write!(f, "{}:{}", value, value.dtype()),
            Self::Register { rid, dtype } => write!(f, "{rid}:{dtype}"),
        }
    }
}

impl HasDtype for Operand {
    fn dtype(&self) -> Dtype {
        match self {
            Self::Constant(value) => value.dtype(),
            Self::Register { dtype, .. } => dtype.clone(),
        }
    }
}

#[derive(Debug, Eq, Clone, Copy, PartialEq, Hash)]
pub struct RegisterId(pub usize);

impl RegisterId {
    pub fn new(i: usize) -> Self {
        RegisterId(i)
    }
}

impl fmt::Display for RegisterId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rid = self.0;
        write!(f, "%{rid}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    Undef {
        dtype: Dtype,
    },
    Unit,
    Int {
        value: u8,
        width: usize,
        is_signed: bool,
    },
    GlobalVariable {
        name: String,
        dtype: Dtype,
    },
}

impl TryFrom<&ast::Constant> for Constant {
    type Error = ();

    fn try_from(constant: &ast::Constant) -> Result<Self, Self::Error> {
        match constant {
            ast::Constant::Integer(integer) => {
                let dtype = Dtype::INT;

                let pat = 10;

                let value = if integer.suffix.unsigned {
                    u8::from_str_radix(integer.number.deref(), pat).unwrap()
                } else {
                    i8::from_str_radix(integer.number.deref(), pat).unwrap() as u8
                };

                let is_signed = !integer.suffix.unsigned && {
                    let width = dtype.get_int_width().unwrap();
                    let threshold = 1u8 << (width as u8 - 1);
                    value < threshold
                };

                Ok(Self::int(value, dtype.set_signed(is_signed)))
            }
            ast::Constant::Float(_) => panic!("Float number is not supported"),
            ast::Constant::Character(character) => {
                let dtype = Dtype::CHAR;
                let value = character.parse::<char>().unwrap() as u8;

                Ok(Self::int(value, dtype))
            }
        }
    }
}

impl TryFrom<&ast::Expression> for Constant {
    type Error = ();

    fn try_from(expr: &ast::Expression) -> Result<Self, Self::Error> {
        match expr {
            ast::Expression::Constant(constant) => Self::try_from(&constant.node),
            ast::Expression::UnaryOperator(unary) => {
                let constant = Self::try_from(&unary.node.operand.node)?;
                match &unary.node.operator.node {
                    ast::UnaryOperator::Minus => Ok(constant.minus()),
                    ast::UnaryOperator::Plus => Ok(constant),
                    _ => Err(()),
                }
            }
            _ => Err(()),
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Undef { .. } => write!(f, "undef"),
            Self::Unit => write!(f, "unit"),
            Self::Int {
                value, is_signed, ..
            } => write!(
                f,
                "{}",
                if *is_signed {
                    (*value as i128).to_string()
                } else {
                    value.to_string()
                }
            ),
            Self::GlobalVariable { name, .. } => write!(f, "@{}", name),
        }
    }
}

impl HasDtype for Constant {
    fn dtype(&self) -> Dtype {
        match self {
            Self::Undef { dtype } => dtype.clone(),
            Self::Unit => Dtype::unit(),
            Self::Int {
                width, is_signed, ..
            } => Dtype::int(*width).set_signed(*is_signed),
            Self::GlobalVariable { dtype, .. } => dtype.clone(),
        }
    }
}

impl Constant {
    #[inline]
    pub fn undef(dtype: Dtype) -> Self {
        Self::Undef { dtype }
    }

    #[inline]
    pub fn unit() -> Self {
        Self::Unit
    }

    #[inline]
    pub fn int(value: u8, dtype: Dtype) -> Self {
        let width = dtype.get_int_width().expect("`dtype` must be `Dtype::Int`");
        let is_signed = dtype.is_int_signed();

        Self::Int {
            value,
            width,
            is_signed,
        }
    }

    #[inline]
    pub fn global_variable(name: String, dtype: Dtype) -> Self {
        Self::GlobalVariable { name, dtype }
    }

    #[inline]
    pub fn get_global_variable_name(&self) -> Option<String> {
        if let Self::GlobalVariable { name, .. } = self {
            Some(name.clone())
        } else {
            None
        }
    }

    #[inline]
    fn minus(self) -> Self {
        match self {
            Self::Int {
                value,
                width,
                is_signed,
            } => {
                assert!(is_signed);
                let minus_value = -(value as i8);
                Self::Int {
                    value: minus_value as u8,
                    width,
                    is_signed,
                }
            }
            _ => panic!("must be integer"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub usize);

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub phinodes: Vec<Named<Dtype>>,
    pub instructions: Vec<Named<Instruction>>,
    pub exit: BlockExit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockExit {
    Jump {
        arg: JumpArg,
    },
    ConditionalJump {
        condition: Operand,
        arg_then: JumpArg,
        arg_else: JumpArg,
    },
    Return {
        value: Operand,
    },
    Unreachable,
}

impl BlockExit {
    pub fn walk_jump_args<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut JumpArg),
    {
        match self {
            Self::Jump { arg } => f(arg),
            Self::ConditionalJump {
                arg_then, arg_else, ..
            } => {
                f(arg_then);
                f(arg_else);
            }
            Self::Return { .. } | Self::Unreachable => {}
        }
    }
}

impl fmt::Display for BlockExit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BlockExit::Jump { arg } => write!(f, "j {arg}"),
            BlockExit::ConditionalJump {
                condition,
                arg_then,
                arg_else,
            } => write!(f, "br {condition}, {arg_then}, {arg_else}"),
            BlockExit::Return { value } => write!(f, "ret {value}"),
            BlockExit::Unreachable => write!(f, "<unreachable>\t\t\t\t; error state"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JumpArg {
    pub bid: BlockId,
    pub args: Vec<Operand>,
}

impl JumpArg {
    pub fn new(bid: BlockId, args: Vec<Operand>) -> Self {
        Self { bid, args }
    }
}

impl fmt::Display for JumpArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.bid,
            self.args
                .iter()
                .format_with(", ", |a, f| f(&format_args!("{}:{}", a, a.dtype())))
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Named<T> {
    name: Option<String>,
    inner: T,
}

impl<T> Deref for Named<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
impl<T> DerefMut for Named<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T> Named<T> {
    pub fn new(name: Option<String>, inner: T) -> Self {
        Self { name, inner }
    }

    pub fn name(&self) -> Option<&String> {
        self.name.as_ref()
    }

    pub fn destruct(self) -> (T, Option<String>) {
        (self.inner, self.name)
    }

    pub fn into_inner(self) -> T {
        self.inner
    }
}

impl<T: fmt::Display> fmt::Display for Named<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}
