mod dtype;
use lang_c::ast;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

pub use dtype::Dtype;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSignature {
    pub ret: Dtype,
    pub params: Vec<Dtype>,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Constant(Constant),
    Register { rid: RegisterId, dtype: Dtype },
}

#[derive(Debug, Eq, Clone, Copy)]
pub enum RegisterId {
    Local { aid: usize },
    Arg { bid: BlockId, aid: usize },
    Temp { bid: BlockId, iid: usize },
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
    GlobalVariable {
        name: String,
        dtype: Dtype,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub usize);

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
