use super::Type;
use crate::codegen::{call, pop, push, Codegen, ContextInfo};
use crate::lexer::{JackTokenizer, KeywordKind, SymbolKind, Token};
use crate::parser::Parse;
use crate::{escape_xml, JackcError};
use std::convert::TryFrom;

#[derive(Debug)]
pub(crate) struct Expression {
    term: Term,
    ops: Vec<(Op, Term)>,
}

impl Codegen for Expression {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &ContextInfo,
    ) -> Result<(), JackcError> {
        self.term.generate(writer, context)?;

        for (op, term) in self.ops.iter() {
            term.generate(writer, context)?;

            match op {
                Op(b'+') => writeln!(writer, "add")?,
                Op(b'-') => writeln!(writer, "sub")?,
                Op(b'=') => writeln!(writer, "eq")?,
                Op(b'>') => writeln!(writer, "gt")?,
                Op(b'<') => writeln!(writer, "lt")?,
                Op(b'&') => writeln!(writer, "and")?,
                Op(b'|') => writeln!(writer, "or")?,
                Op(b'*') => call(writer, "Math", "multiply", 2)?,
                Op(b'/') => call(writer, "Math", "divide", 2)?,
                _ => unreachable!("never reach here..."),
            }
        }

        Ok(())
    }
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<expression>")?;
        writeln!(f, "{}", self.term)?;
        for (op, term) in self.ops.iter() {
            writeln!(f, "{}", op)?;
            writeln!(f, "{}", term)?;
        }
        write!(f, "</expression>")?;
        Ok(())
    }
}

impl Parse for Expression {
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Expression, JackcError> {
        let term = Term::parse(tokenizer)?;
        let mut next = tokenizer.advance()?;
        let mut ops = vec![];

        while let Ok(op) = Op::try_from(&next) {
            ops.push((op, Term::parse(tokenizer)?));
            next = tokenizer.advance()?;
        }

        tokenizer.unread_token(next);

        Ok(Expression { term, ops })
    }
}

impl Parse for Vec<Expression> {
    fn parse<T: std::io::Read>(
        tokenizer: &mut JackTokenizer<T>,
    ) -> Result<Vec<Expression>, JackcError> {
        tokenizer.advance()?.expect_spec_symbol(b'(')?;
        let mut next = tokenizer.advance()?;
        let mut result = vec![];

        while next != Token::Symbol(SymbolKind(b')')) {
            if next != Token::Symbol(SymbolKind(b',')) {
                tokenizer.unread_token(next);
            }
            result.push(Expression::parse(tokenizer)?);
            next = tokenizer.advance()?;
        }

        Ok(result)
    }
}

#[derive(Debug)]
enum Term {
    IntegerConstant(u16),
    StringConstant(String),
    KeywordConstant(KeywordConstantKind),
    Var(String),
    IndexedVar(String, Box<Expression>),
    SubroutineCall(SubroutineCall),
    ParenthesizedExpr(Box<Expression>),
    UnaryOpedTerm(UnaryOp, Box<Term>),
}

impl Codegen for Term {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &ContextInfo,
    ) -> Result<(), JackcError> {
        match self {
            Term::IntegerConstant(n) => {
                push(writer, "constant", *n)?;
            }
            Term::StringConstant(ref s) => {
                let bytes = s.as_bytes();
                push(writer, "constant", bytes.len() as _)?;
                call(writer, "String", "new", 1)?;

                for byte in bytes.iter() {
                    push(writer, "constant", *byte as _)?;
                    call(writer, "String", "appendChar", 2)?;
                }
            }
            Term::KeywordConstant(k) => match k {
                KeywordConstantKind::False | KeywordConstantKind::Null => {
                    push(writer, "constant", 0)?;
                }
                KeywordConstantKind::True => {
                    push(writer, "constant", 0)?;
                    writeln!(writer, "not")?;
                }
                KeywordConstantKind::This => {
                    push(writer, "pointer", 0)?;
                }
            },
            Term::Var(ref n) | Term::IndexedVar(ref n, _) => {
                if let Some((segment, _, index)) = context.find(&n) {
                    push(writer, segment, index as _)?;
                } else {
                    return Err(JackcError::ValiableNotFound(n.clone()));
                }

                if let Term::IndexedVar(_, ref expr) = self {
                    expr.generate(writer, context)?;
                    writeln!(writer, "add")?;
                    pop(writer, "pointer", 1)?;
                    push(writer, "that", 0)?;
                }
            }
            Term::SubroutineCall(s) => {
                s.generate(writer, context)?;
            }
            Term::ParenthesizedExpr(e) => {
                e.generate(writer, context)?;
            }
            Term::UnaryOpedTerm(uop, t) => {
                t.generate(writer, context)?;
                match uop {
                    UnaryOp(b'-') => {
                        writeln!(writer, "neg")?;
                    }
                    UnaryOp(b'~') => {
                        writeln!(writer, "not")?;
                    }
                    _ => {
                        unreachable!("never reach here...");
                    }
                }
            }
        }

        Ok(())
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<term>")?;
        match self {
            &Term::IntegerConstant(ref n) => {
                writeln!(f, "<integerConstant> {} </integerConstant>", n)?;
            }
            &Term::StringConstant(ref s) => {
                writeln!(f, "<stringConstant> {} </stringConstant>", escape_xml(s))?;
            }
            &Term::KeywordConstant(ref k) => {
                writeln!(f, "{}", k)?;
            }
            &Term::Var(ref n) => {
                writeln!(f, "<identifier> {} </identifier>", n)?;
            }
            &Term::IndexedVar(ref n, ref i) => {
                writeln!(f, "<identifier> {} </identifier>", n)?;
                writeln!(f, "<symbol>[</symbol>")?;
                writeln!(f, "{}", i)?;
                writeln!(f, "<symbol>]</symbol>")?;
            }
            &Term::SubroutineCall(ref s) => {
                writeln!(f, "{}", s)?;
            }
            &Term::ParenthesizedExpr(ref e) => {
                writeln!(f, "<symbol>(</symbol>")?;
                writeln!(f, "{}", e)?;
                writeln!(f, "<symbol>)</symbol>")?;
            }
            &Term::UnaryOpedTerm(ref uop, ref t) => {
                writeln!(f, "{}", uop)?;
                writeln!(f, "{}", t)?;
            }
        }
        write!(f, "</term>")?;
        Ok(())
    }
}

impl Parse for Term {
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Term, JackcError> {
        match tokenizer.advance()? {
            Token::IntegerLiteral(i) => Ok(Term::IntegerConstant(i)),
            Token::StringLiteral(s) => Ok(Term::StringConstant(s)),
            Token::Keyword(KeywordKind::True) => {
                Ok(Term::KeywordConstant(KeywordConstantKind::True))
            }
            Token::Keyword(KeywordKind::False) => {
                Ok(Term::KeywordConstant(KeywordConstantKind::False))
            }
            Token::Keyword(KeywordKind::Null) => {
                Ok(Term::KeywordConstant(KeywordConstantKind::Null))
            }
            Token::Keyword(KeywordKind::This) => {
                Ok(Term::KeywordConstant(KeywordConstantKind::This))
            }
            Token::Identifier(s) => match tokenizer.advance()? {
                Token::Symbol(SymbolKind(b'[')) => {
                    let index = Box::new(Expression::parse(tokenizer)?);
                    tokenizer.advance()?.expect_spec_symbol(b']')?;
                    Ok(Term::IndexedVar(s, index))
                }
                t @ Token::Symbol(SymbolKind(b'(')) | t @ Token::Symbol(SymbolKind(b'.')) => {
                    tokenizer.unread_token(t);
                    Ok(Term::SubroutineCall(
                        SubroutineCall::parse_with_first_ident(s, tokenizer)?,
                    ))
                }
                t => {
                    tokenizer.unread_token(t);
                    Ok(Term::Var(s))
                }
            },
            Token::Symbol(SymbolKind(b'(')) => {
                let expr = Expression::parse(tokenizer)?;
                tokenizer.advance()?.expect_spec_symbol(b')')?;
                Ok(Term::ParenthesizedExpr(Box::new(expr)))
            }
            t @ Token::Symbol(_) => {
                let unop = UnaryOp::try_from(&t).map_err(|_| JackcError::InvalidSyntax)?;
                Ok(Term::UnaryOpedTerm(unop, Box::new(Term::parse(tokenizer)?)))
            }
            _ => Err(JackcError::InvalidSyntax),
        }
    }
}

#[derive(Debug)]
enum KeywordConstantKind {
    True,
    False,
    Null,
    This,
}

impl std::fmt::Display for KeywordConstantKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &KeywordConstantKind::True => write!(f, "<keyword> true </keyword>"),
            &KeywordConstantKind::False => write!(f, "<keyword> false </keyword>"),
            &KeywordConstantKind::Null => write!(f, "<keyword> null </keyword>"),
            &KeywordConstantKind::This => write!(f, "<keyword> this </keyword>"),
        }
    }
}

#[derive(Debug)]
pub(crate) struct SubroutineCall {
    kind: SubroutineCallKind,
    name: String,
    args: Vec<Expression>,
}

impl Codegen for SubroutineCall {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &ContextInfo,
    ) -> Result<(), JackcError> {
        let (receiver, n_args) = match self.kind {
            SubroutineCallKind::SameClassCall => {
                push(writer, "pointer", 0)?;
                (&context.class_name, self.args.len() + 1)
            }
            SubroutineCallKind::AbsoluteCall(ref receiver) => {
                if let Some((segment, v_type, index)) = context.find(receiver) {
                    match v_type {
                        &Type::Class(ref name) => {
                            push(writer, segment, index as _)?;
                            (name, self.args.len() + 1)
                        }
                        _ => return Err(JackcError::PrimitiveTypeMethod),
                    }
                } else {
                    (receiver, self.args.len())
                }
            }
        };

        for expr in self.args.iter() {
            expr.generate(writer, context)?;
        }

        call(writer, receiver, &self.name, n_args as u16)?;

        Ok(())
    }
}

impl std::fmt::Display for SubroutineCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        //writeln!(f, "<subroutineCall>")?;
        match self.kind {
            SubroutineCallKind::AbsoluteCall(ref s) => {
                writeln!(f, "<identifier> {} </identifier>", s)?;
                writeln!(f, "<symbol> . </symbol>")?;
            }
            _ => (),
        }
        writeln!(f, "<identifier> {} </identifier>", self.name)?;
        writeln!(f, "<symbol> ( </symbol>")?;
        writeln!(f, "<expressionList>")?;

        for (n, arg) in self.args.iter().enumerate() {
            if n != 0 {
                writeln!(f, "<symbol> , </symbol>")?;
            }

            writeln!(f, "{}", arg)?;
        }
        writeln!(f, "</expressionList>")?;
        write!(f, "<symbol> ) </symbol>")?;
        //write!(f, "</subroutineCall>")?;
        Ok(())
    }
}

impl SubroutineCall {
    pub(crate) fn parse_with_first_ident(
        s: String,
        tokenizer: &mut JackTokenizer<impl std::io::Read>,
    ) -> Result<SubroutineCall, JackcError> {
        match tokenizer.advance()? {
            t @ Token::Symbol(SymbolKind(b'(')) => {
                tokenizer.unread_token(t);
                let args = Vec::<Expression>::parse(tokenizer)?;
                Ok(SubroutineCall {
                    kind: SubroutineCallKind::SameClassCall,
                    name: s,
                    args,
                })
            }
            Token::Symbol(SymbolKind(b'.')) => {
                let name = tokenizer.advance()?.expect_identifier()?;
                let args = Vec::<Expression>::parse(tokenizer)?;
                Ok(SubroutineCall {
                    kind: SubroutineCallKind::AbsoluteCall(s),
                    name,
                    args,
                })
            }
            _ => Err(JackcError::InvalidSyntax),
        }
    }
}

#[derive(Debug)]
enum SubroutineCallKind {
    SameClassCall,
    AbsoluteCall(String),
}

#[derive(Debug, Eq, PartialEq)]
struct UnaryOp(u8);

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<symbol> {} </symbol>", self.0 as char)
    }
}

impl TryFrom<&Token> for UnaryOp {
    type Error = ();
    fn try_from(token: &Token) -> Result<UnaryOp, ()> {
        match token {
            &Token::Symbol(ref kind) => {
                let b = kind.0;
                match b {
                    b'-' | b'~' => Ok(UnaryOp(b)),
                    _ => Err(()),
                }
            }
            _ => Err(()),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Op(u8);

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "<symbol> {} </symbol>",
            escape_xml(&((self.0 as char).to_string()))
        )
    }
}

impl TryFrom<&Token> for Op {
    type Error = ();
    fn try_from(token: &Token) -> Result<Op, ()> {
        match token {
            &Token::Symbol(ref kind) => {
                let b = kind.0;
                match b {
                    b'+' | b'-' | b'*' | b'/' | b'&' | b'|' | b'<' | b'>' | b'=' => Ok(Op(b)),
                    _ => Err(()),
                }
            }
            _ => Err(()),
        }
    }
}
