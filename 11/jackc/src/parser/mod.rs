use crate::lexer::JackTokenizer;
use crate::JackcError;

pub(crate) mod class;
pub(crate) mod expression;
pub(crate) mod statement;

pub trait Parse
where
    Self: Sized,
{
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Self, JackcError>;
}

pub use class::Class;
pub use class::Type;
