#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Dtype {
    Unit {
        is_const: bool,
    },
    Int {
        width: usize,
        is_signed: bool,
        is_const: bool,
    },
    Function {
        ret: Box<Dtype>,
        params: Vec<Dtype>,
    },
    // Array {
    //     inner: Box<Dtype>,
    //     size: usize,
    // },
}
