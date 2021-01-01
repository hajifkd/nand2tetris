use crate::{escape_xml, JackcError};
use std::convert::{TryFrom, TryInto};
use std::io::{Bytes, Read};

macro_rules! gen_keyword {
    ($($keyword: ident),*) => {
        #[derive(Eq, PartialEq, Debug)]
        pub enum KeywordKind {
            $($keyword),*
        }

        impl TryFrom<&[u8]> for KeywordKind {
            type Error = ();

            fn try_from(keyword: &[u8]) -> Result<KeywordKind, ()> {
                $(if keyword == stringify!($keyword).to_lowercase().as_bytes() {
                    return Ok(KeywordKind::$keyword);
                });*
                return Err(());
            }
        }

        impl std::fmt::Display for KeywordKind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                $(if self == &KeywordKind::$keyword {
                    write!(f, "{}", stringify!($keyword).to_lowercase())?;
                });*

                Ok(())
            }
        }
    };
}

gen_keyword! {Class, Constructor, Function, Method, Field, Static, Var, Int,
Char, Boolean, Void, True, False, Null, This, Let, Do, If, Else,
While, Return}

#[derive(Debug, Eq, PartialEq)]
pub struct SymbolKind(pub(crate) u8);

impl TryFrom<u8> for SymbolKind {
    type Error = ();

    fn try_from(c: u8) -> Result<SymbolKind, ()> {
        match c {
            b'{' | b'}' | b'(' | b')' | b'[' | b']' | b'.' | b',' | b';' | b'+' | b'-' | b'*'
            | b'/' | b'&' | b'|' | b'<' | b'>' | b'=' | b'~' => Ok(SymbolKind(c)),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum Token {
    Keyword(KeywordKind),
    Symbol(SymbolKind),    //
    IntegerLiteral(u16),   //
    StringLiteral(String), //
    Identifier(String),
    EndOfFile,
}

impl Token {
    pub fn to_xml_element(&self) -> String {
        match &self {
            Token::EndOfFile => String::new(),
            Token::Identifier(ref ident) => {
                format!("<identifier>{}</identifier>", escape_xml(&ident))
            }
            Token::IntegerLiteral(n) => format!("<integerConstant>{}</integerConstant>", n),
            Token::Keyword(keyword) => format!("<keyword>{}</keyword>", keyword),
            Token::StringLiteral(ref s) => {
                format!("<stringConstant>{}</stringConstant>", escape_xml(&s))
            }
            Token::Symbol(SymbolKind(c)) => {
                format!("<symbol>{}</symbol>", escape_xml(&(*c as char).to_string()))
            }
        }
    }

    pub(crate) fn expect_identifier(self) -> Result<String, JackcError> {
        match self {
            Token::Identifier(ident) => Ok(ident),
            _ => Err(JackcError::ExpectedElementNotAppear("identifier")),
        }
    }

    pub(crate) fn expect_keyword(self) -> Result<KeywordKind, JackcError> {
        match self {
            Token::Keyword(keyword) => Ok(keyword),
            _ => Err(JackcError::ExpectedElementNotAppear("keyword")),
        }
    }

    pub(crate) fn expect_symbol(self) -> Result<u8, JackcError> {
        match self {
            Token::Symbol(SymbolKind(b)) => Ok(b),
            _ => Err(JackcError::ExpectedElementNotAppear("symbol")),
        }
    }

    pub(crate) fn expect_spec_symbol(self, e: u8) -> Result<(), JackcError> {
        match self {
            Token::Symbol(SymbolKind(b)) => {
                if e == b {
                    Ok(())
                } else {
                    Err(JackcError::ExpectedCharNotAppear(e as _))
                }
            }
            _ => Err(JackcError::ExpectedElementNotAppear("symbol")),
        }
    }
}

pub struct JackTokenizer<T: Read> {
    bytes: Bytes<T>,
    prev: Option<u8>,
    line: usize,
    prev_token: Option<Token>,
}

impl<T: Read> JackTokenizer<T> {
    pub fn new(reader: T) -> Self {
        JackTokenizer {
            bytes: reader.bytes(),
            prev: None,
            line: 1,
            prev_token: None,
        }
    }

    pub fn line(&self) -> usize {
        self.line
    }
    fn read(&mut self) -> Result<Option<u8>, JackcError> {
        if let Some(b) = self.prev.take() {
            Ok(Some(b))
        } else {
            if let Some(r) = self.bytes.next() {
                let r = r?;
                if r == b'\n' {
                    self.line += 1;
                }
                Ok(Some(r))
            } else {
                Ok(None)
            }
        }
    }

    fn unread(&mut self, b: u8) {
        if b == b'\n' {
            self.line -= 1;
        }
        self.prev = Some(b);
    }

    fn drop_until(&mut self, b: u8) -> Result<(), JackcError> {
        while let Some(r) = self.read()? {
            if r == b {
                return Ok(());
            }
        }

        Err(JackcError::ExpectedCharNotAppear(b.into()))
    }

    pub fn unread_token(&mut self, token: Token) {
        self.prev_token = Some(token);
    }

    pub fn advance(&mut self) -> Result<Token, JackcError> {
        if self.prev_token.is_some() {
            return Ok(self.prev_token.take().unwrap());
        }
        while let Some(b) = self.read()? {
            match b {
                b' ' | b'\x09'..=b'\x0d' => continue,
                b'/' => {
                    match self.read()? {
                        Some(b'/') => {
                            self.drop_until(b'\n')?;
                            continue;
                        }
                        Some(b'*') => {
                            loop {
                                self.drop_until(b'*')?;
                                if self.read()?.ok_or(JackcError::ExpectedCharNotAppear('/'))?
                                    == b'/'
                                {
                                    break;
                                }
                            }
                            continue;
                        }
                        Some(next) => {
                            self.unread(next);
                        }
                        None => {}
                    }
                    return Ok(Token::Symbol(b'/'.try_into().unwrap()));
                }
                b'\"' => {
                    let mut result = vec![];

                    while let Some(b) = self.read()? {
                        if b == b'\"' {
                            return Ok(Token::StringLiteral(String::from_utf8(result)?));
                        } else if b == b'\\' {
                            match self.read()?.ok_or(JackcError::InvalidSyntax)? {
                                b'n' => result.push(b'\n'),
                                b't' => result.push(b'\t'),
                                b'r' => result.push(b'\r'),
                                n => result.push(n),
                            }
                        } else {
                            result.push(b);
                        }
                    }

                    return Err(JackcError::ExpectedCharNotAppear('\"'));
                }
                b'0'..=b'9' => {
                    let mut result = vec![b];
                    while let Some(b) = self.read()? {
                        match b {
                            b'0'..=b'9' => result.push(b),
                            _ => {
                                self.unread(b);
                                return Ok(Token::IntegerLiteral(
                                    result
                                        .iter()
                                        .fold(0, |acc, x| acc * 10 + ((x - b'0') as u16)),
                                ));
                            }
                        }
                    }

                    return Err(JackcError::InvalidSyntax);
                }
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                    let mut result = vec![b];
                    while let Some(b) = self.read()? {
                        match b {
                            b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'0'..=b'9' => result.push(b),
                            _ => {
                                self.unread(b);
                                if let Ok(k) = KeywordKind::try_from(&result[..]) {
                                    return Ok(Token::Keyword(k));
                                } else {
                                    return Ok(Token::Identifier(String::from_utf8(result)?));
                                }
                            }
                        }
                    }

                    return Err(JackcError::InvalidSyntax);
                }
                _ => {
                    if let Ok(s) = SymbolKind::try_from(b) {
                        return Ok(Token::Symbol(s));
                    } else {
                        return Err(JackcError::InvalidSyntax);
                    }
                }
            }
        }

        Ok(Token::EndOfFile)
    }
}

#[test]
fn test_symbol_kind() {
    use std::convert::TryInto;
    assert_eq!((&b"class"[..]).try_into(), Ok(KeywordKind::Class));
    assert_eq!((&b"return"[..]).try_into(), Ok(KeywordKind::Return));
    assert_eq!(KeywordKind::try_from(&b"enum"[..]), Err(()));
}
