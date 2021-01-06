use std::borrow::Cow;
use thiserror::Error;

pub mod lexer;
pub mod parser;

#[derive(Debug, Error)]
pub enum JackcError {
    #[error("Invalid syntax")]
    InvalidSyntax,
    #[error("Expected char {0} does not appear")]
    ExpectedCharNotAppear(char),
    #[error("Expected keyword {0} does not appear")]
    ExpectedKeywordNotAppear(&'static str),
    #[error("{0} is expected but does not appear")]
    ExpectedElementNotAppear(&'static str),
    #[error(transparent)]
    IoError(#[from] std::io::Error),
    #[error(transparent)]
    FromUtf8Error(#[from] std::string::FromUtf8Error),
}

pub(crate) fn escape_xml<'a>(s: &'a str) -> Cow<'a, str> {
    if s.contains(|c| c == '<' || c == '>' || c == '&') {
        s.chars()
            .fold(String::new(), |mut acc, x| {
                match x {
                    '>' => acc.push_str("&gt;"),
                    '<' => acc.push_str("&lt;"),
                    '&' => acc.push_str("&amp;"),
                    c => acc.push(c),
                }
                acc
            })
            .into()
    } else {
        s.into()
    }
}
