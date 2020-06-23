use std::fmt;
use serde::export::Formatter;
#[macro_export]
macro_rules! internal_error {
    () => {
        Err(Box::new(crate::error::InternalError{
            file: file!(),
            line: line!()
        }))
    };
}
#[derive(Debug)]
pub struct InternalError {
    pub file: &'static str,
    pub line: u32,
}
impl fmt::Display for InternalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "internal error originated at {}:{}", self.file, self.line)
    }
}
impl std::error::Error for InternalError {

}

pub type BoxedErrorTrait = Box<(dyn std::error::Error + 'static)>;