use crate::ir;
use crate::ir::{Constant, Dtype, HasDtype};
use crate::vm::execute::ExecutionError;
use lang_c::ast;
use std::ops::Deref;
use std::{collections::HashMap, fmt};

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct ProgramCounter {
    pub bid: ir::BlockId,
    pub iid: usize,
}

impl fmt::Debug for ProgramCounter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?}, {:?}", self.bid, self.iid))
    }
}

impl fmt::Display for ProgramCounter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.bid, self.iid)
    }
}

impl ProgramCounter {
    pub fn new(bid: ir::BlockId) -> ProgramCounter {
        ProgramCounter { bid, iid: 0 }
    }

    pub fn inc(&mut self) {
        self.iid += 1;
    }
    /// Increase Self by one and return the value before the increase.
    pub fn inc_pre(&mut self) -> Self {
        let pre = *self;
        self.inc();
        pre
    }
}

/// register id -> value
#[derive(Clone, Debug, Default, PartialEq)]
pub struct RegisterMap(pub HashMap<ir::RegisterId, Value>);

impl RegisterMap {
    pub fn read(&self, rid: ir::RegisterId) -> &Value {
        self.0
            .get(&rid)
            .expect("`rid` must be assigned before it can be used")
    }

    pub fn write(&mut self, rid: ir::RegisterId, value: Value) {
        let _unused = self.0.insert(rid, value);
    }
}

/// Bidirectional map between the name of a global variable and memory box id
#[derive(Default, Debug, PartialEq, Clone)]
pub struct GlobalMap {
    var_to_bid: HashMap<String, usize>,
    bid_to_var: HashMap<usize, String>,
}

impl GlobalMap {
    /// Create a bi-directional mapping between `var` and `bid`.
    pub fn insert(&mut self, var: String, bid: usize) -> Result<(), ExecutionError> {
        if self.var_to_bid.insert(var.clone(), bid).is_some() {
            panic!("variable name should be unique in IR")
        }
        if self.bid_to_var.insert(bid, var).is_some() {
            panic!("`bid` is connected to only one `var`")
        }

        Ok(())
    }

    pub fn get_bid(&self, var: &str) -> Option<usize> {
        self.var_to_bid.get(var).cloned()
    }

    pub fn get_var(&self, bid: usize) -> Option<String> {
        self.bid_to_var.get(&bid).cloned()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Undef {
        dtype: Dtype,
    },
    Unit,
    Int {
        /// it can be extended to u256
        value: u8,
        width: usize,
        is_signed: bool,
    },
    Pointer {
        bid: Option<usize>,
        offset: isize,
        dtype: Dtype,
    },
}

impl TryFrom<Constant> for Value {
    type Error = ();

    fn try_from(c: Constant) -> Result<Self, Self::Error> {
        let value = match c {
            Constant::Unit => Self::Unit,
            Constant::Undef { dtype } => Self::Undef { dtype },
            Constant::Int {
                value,
                width,
                is_signed,
            } => Self::Int {
                value,
                width,
                is_signed,
            },
            _ => panic!("Invalid constant"),
        };
        Ok(value)
    }
}

impl HasDtype for Value {
    fn dtype(&self) -> Dtype {
        match self {
            Self::Undef { dtype } => dtype.clone(),
            Self::Unit => Dtype::unit(),
            Self::Int {
                value: _,
                width,
                is_signed,
            } => Dtype::int(*width).set_signed(*is_signed),
            Self::Pointer { dtype, .. } => Dtype::pointer(dtype.clone()),
        }
    }
}

impl Value {
    #[inline]
    pub fn undef(dtype: Dtype) -> Self {
        Self::Undef { dtype }
    }

    #[inline]
    pub fn unit() -> Self {
        Self::Unit
    }

    #[inline]
    pub fn int(value: u8, width: usize, is_signed: bool) -> Self {
        Self::Int {
            value,
            width,
            is_signed,
        }
    }

    #[inline]
    pub fn pointer(bid: Option<usize>, offset: isize, dtype: Dtype) -> Self {
        Self::Pointer { bid, offset, dtype }
    }

    #[inline]
    pub fn get_int(&self) -> Option<(u8, usize, bool)> {
        if let Value::Int {
            value,
            width,
            is_signed,
        } = self
        {
            Some((*value, *width, *is_signed))
        } else {
            None
        }
    }

    #[inline]
    pub fn get_pointer(&self) -> Option<(&Option<usize>, &isize, &Dtype)> {
        if let Value::Pointer { bid, offset, dtype } = self {
            Some((bid, offset, dtype))
        } else {
            None
        }
    }

    #[inline]
    fn nullptr(dtype: Dtype) -> Self {
        Self::Pointer {
            bid: None,
            offset: 0,
            dtype,
        }
    }

    #[inline]
    pub fn default_from_dtype(dtype: &Dtype) -> Result<Self, ()> {
        let value = match dtype {
            Dtype::Unit { .. } => Self::unit(),
            Dtype::Int {
                width, is_signed, ..
            } => Self::int(u8::default(), *width, *is_signed),
            Dtype::Pointer { inner, .. } => Self::nullptr(inner.deref().clone()),
            Dtype::Function { .. } => panic!("function type does not have a default value"),
        };

        Ok(value)
    }

    #[allow(clippy::result_unit_err)]
    pub fn try_from_initializer(
        initializer: &ast::Initializer,
        dtype: &Dtype,
    ) -> Result<Self, ()> {
        match initializer {
            ast::Initializer::Expression(expr) => match dtype {
                Dtype::Int { .. } | Dtype::Pointer { .. } => {
                    let constant = Constant::try_from(&expr.node)?;
                    Self::try_from(constant)
                }
                _ => Err(()),
            },
            _ => Err(()),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct StackFrame<'i> {
    pub pc: ProgramCounter,
    pub registers: RegisterMap,
    pub func_name: String,
    pub func_def: &'i ir::FunctionDefinition,
}

impl<'i> StackFrame<'i> {
    pub fn new(bid: ir::BlockId, func_name: String, func_def: &'i ir::FunctionDefinition) -> Self {
        StackFrame {
            pc: ProgramCounter::new(bid),
            registers: Default::default(),
            func_name,
            func_def,
        }
    }
}

#[derive(Debug, Default, PartialEq)]
pub struct Memory(Vec<Vec<Value>>);

impl Memory {
    pub fn alloc(&mut self, dtype: &Dtype) -> Result<usize, ExecutionError> {
        // TODO: memory block will be handled as Vec<Byte>
        let memory_block = match dtype {
            Dtype::Unit { .. } => vec![],
            Dtype::Int { width, .. } => match width {
                8 => vec![],
                _ => todo!(),
            },
            Dtype::Pointer { .. } => vec![],
            Dtype::Function { .. } => vec![],
        };

        self.0.push(memory_block);

        Ok(self.0.len() - 1)
    }

    pub fn load(
        &self, pointer: Value
    ) -> Result<Value, ExecutionError> {
        let (bid, offset, _) = pointer
            .get_pointer()
            .expect("`pointer` must be `Value::Pointer` to access memory");

        let bid = bid.expect("read from memory using constant value address is not allowed");

        Ok(self.0[bid][*offset as usize].clone())
    }

    pub fn store(&mut self, bid: usize, offset: isize, value: &Value) -> Result<(), ()> {
        let size = value.dtype().size_align_of().unwrap().0;
        let _end = offset as usize + size;
        if offset >= 0 {
            Err(())
        } else {
            self.0[bid][offset as usize] = value.clone();
            Ok(())
        }
    }
}
#[derive(Debug, PartialEq)]
pub struct State<'i> {
    /// Maps each global variable to a pointer value.
    ///
    /// When a function call occurs, `registers` can be initialized by `global_registers`
    pub global_map: GlobalMap,
    pub stack_frame: StackFrame<'i>,
    pub stack: Vec<StackFrame<'i>>,
    pub memory: Memory,
    pub ir: &'i ir::TranslationUnit,
}
