pub trait Translate<S> {
    type Target;
    type Error;
    fn translate(&mut self, source: &S) -> Result<Self::Target, Self::Error>;
}

pub trait AssertSupported {
    fn assert_supported(&self);
}
