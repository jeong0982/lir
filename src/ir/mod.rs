mod dtype;
mod interp;

pub use dtype::{Dtype, DtypeError, HasDtype};

use core::ops::{Deref, DerefMut};
use lang_c::ast;
use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};

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
        ptr: Operand,
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
            Self::Nop => Dtype::unit(),
            Self::BinOp { dtype, .. }
            | Self::UnaryOp { dtype, .. }
            | Self::Call {
                return_type: dtype, ..
            } => dtype.clone(),
            Self::Lookup { ptr } => ptr.dtype().clone(),
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

#[derive(Debug, Eq, Clone, Copy)]
pub enum RegisterId {
    Local { aid: usize },
    Arg { bid: BlockId, aid: usize },
    Temp { bid: BlockId, iid: usize },
}

impl RegisterId {
    pub fn local(aid: usize) -> Self {
        Self::Local { aid }
    }

    pub fn arg(bid: BlockId, aid: usize) -> Self {
        Self::Arg { bid, aid }
    }

    pub fn temp(bid: BlockId, iid: usize) -> Self {
        Self::Temp { bid, iid }
    }

    pub fn is_const(&self, bid_init: BlockId) -> bool {
        match self {
            Self::Local { .. } => true,
            Self::Arg { bid, .. } => bid == &bid_init,
            _ => false,
        }
    }
}

impl fmt::Display for RegisterId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Local { aid } => write!(f, "%l{aid}"),
            Self::Arg { bid, aid } => write!(f, "%{bid}:p{aid}"),
            Self::Temp { bid, iid } => write!(f, "%{bid}:i{iid}"),
        }
    }
}

impl PartialEq<RegisterId> for RegisterId {
    fn eq(&self, other: &RegisterId) -> bool {
        match (self, other) {
            (Self::Local { aid }, Self::Local { aid: other_aid }) => aid == other_aid,
            (
                Self::Arg { bid, aid },
                Self::Arg {
                    bid: other_bid,
                    aid: other_aid,
                },
            ) => bid == other_bid && aid == other_aid,
            (
                Self::Temp { bid, iid },
                Self::Temp {
                    bid: other_bid,
                    iid: other_iid,
                },
            ) => bid == other_bid && iid == other_iid,
            _ => false,
        }
    }
}

impl Hash for RegisterId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Local { aid } => aid.hash(state),
            Self::Arg { bid, aid } => {
                // TODO: needs to distinguish arg/temp?
                bid.hash(state);
                aid.hash(state);
            }
            Self::Temp { bid, iid } => {
                bid.hash(state);
                iid.hash(state);
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    Unit,
    Int {
        value: u8,
        width: usize,
        is_signed: bool,
    },
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
        }
    }
}

impl HasDtype for Constant {
    fn dtype(&self) -> Dtype {
        match self {
            Self::Unit => Dtype::unit(),
            Self::Int {
                width, is_signed, ..
            } => Dtype::int(*width).set_signed(*is_signed),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JumpArg {
    pub bid: BlockId,
    pub args: Vec<Operand>,
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
