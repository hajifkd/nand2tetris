use crate::lexer::{JackTokenizer, KeywordKind, SymbolKind, Token};
use crate::{escape_xml, JackcError};
use std::convert::TryFrom;

pub trait Parse
where
    Self: Sized,
{
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Self, JackcError>;
}

#[derive(Debug)]
pub struct Class {
    name: String,
    varss: Vec<Vec<ClassVar>>, // Oops
    subroutines: Vec<Subroutine>,
}

impl std::fmt::Display for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<class>")?;
        writeln!(f, "<keyword> class </keyword>")?;
        writeln!(f, "<identifier> {} </identifier>", self.name)?;
        writeln!(f, "<symbol> {{ </symbol>")?;
        for vars in self.varss.iter() {
            ClassVar::fmt_vars(vars, f)?;
        }
        for subroutine in self.subroutines.iter() {
            writeln!(f, "{}", subroutine)?;
        }
        writeln!(f, "<symbol> }} </symbol>")?;
        write!(f, "</class>")?;
        Ok(())
    }
}

#[derive(Debug)]
struct ClassVar {
    kind: ClassVarKind,
    v_type: Type,
    name: String,
}

impl ClassVar {
    fn fmt_vars(vars: &[ClassVar], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if vars.len() == 0 {
            return Ok(());
        }

        let s = &vars[0];
        writeln!(f, "<classVarDec>")?;
        writeln!(f, "{}", s.kind)?;
        writeln!(f, "{}", s.v_type)?;
        writeln!(f, "<identifier> {} </identifier>", s.name)?;
        for n in (&vars[1..]).iter() {
            writeln!(f, "<symbol> , </symbol>")?;
            writeln!(f, "<identifier> {} </identifier>", n.name)?;
        }
        writeln!(f, "<symbol> ; </symbol>")?;
        writeln!(f, "</classVarDec>")?;
        Ok(())
    }
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
enum ClassVarKind {
    Static,
    Field,
}

impl std::fmt::Display for ClassVarKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &ClassVarKind::Static => write!(f, "<keyword> static </keyword>"),
            &ClassVarKind::Field => write!(f, "<keyword> field </keyword>"),
        }
    }
}

#[derive(Eq, PartialEq, Debug, Clone)]
enum Type {
    Int,
    Char,
    Boolean,
    Void,
    Class(String),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &Type::Int => write!(f, "<keyword> int </keyword>"),
            &Type::Char => write!(f, "<keyword> char </keyword>"),
            &Type::Boolean => write!(f, "<keyword> boolean </keyword>"),
            &Type::Void => write!(f, "<keyword> void </keyword>"),
            &Type::Class(ref s) => write!(f, "<identifier> {} </identifier>", s),
        }
    }
}

impl Parse for Type {
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Type, JackcError> {
        match tokenizer.advance()? {
            Token::Keyword(KeywordKind::Int) => Ok(Type::Int),
            Token::Keyword(KeywordKind::Char) => Ok(Type::Char),
            Token::Keyword(KeywordKind::Boolean) => Ok(Type::Boolean),
            Token::Keyword(KeywordKind::Void) => Ok(Type::Void),
            Token::Identifier(s) => Ok(Type::Class(s)),
            _ => Err(JackcError::InvalidSyntax),
        }
    }
}

impl Parse for Vec<ClassVar> {
    fn parse<T: std::io::Read>(
        tokenizer: &mut JackTokenizer<T>,
    ) -> Result<Vec<ClassVar>, JackcError> {
        let kind = match tokenizer.advance()? {
            Token::Keyword(KeywordKind::Static) => ClassVarKind::Static,
            Token::Keyword(KeywordKind::Field) => ClassVarKind::Field,
            t => {
                tokenizer.unread_token(t);
                return Ok(vec![]);
            }
        };

        let v_type = Type::parse(tokenizer)?;

        if v_type == Type::Void {
            return Err(JackcError::InvalidSyntax);
        }

        let mut idents = vec![tokenizer.advance()?.expect_identifier()?];

        loop {
            let symbol = tokenizer.advance()?.expect_symbol()?;

            match symbol {
                b';' => break,
                b',' => idents.push(tokenizer.advance()?.expect_identifier()?),
                _ => return Err(JackcError::InvalidSyntax),
            }
        }

        Ok(idents
            .into_iter()
            .map(|name| ClassVar {
                kind,
                v_type: v_type.clone(),
                name,
            })
            .collect())
    }
}

#[derive(Debug)]
struct Subroutine {
    kind: SubroutineKind,
    v_type: Type,
    name: String,
    parameters: Vec<Parameter>,
    body: SubroutineBody,
}

impl std::fmt::Display for Subroutine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<subroutineDec>")?;
        writeln!(f, "{}", self.kind)?;
        writeln!(f, "{}", self.v_type)?;
        writeln!(f, "<identifier> {} </identifier>", self.name)?;
        writeln!(f, "<symbol> ( </symbol>")?;
        writeln!(f, "<parameterList>")?;
        for (n, parameter) in self.parameters.iter().enumerate() {
            if n != 0 {
                writeln!(f, "<symbol> , </symbol>")?;
            }
            writeln!(f, "{}", parameter)?;
        }
        writeln!(f, "</parameterList>")?;
        writeln!(f, "<symbol> ) </symbol>")?;
        writeln!(f, "{}", self.body)?;
        write!(f, "</subroutineDec>")?;
        Ok(())
    }
}

impl Parse for Option<Subroutine> {
    fn parse<T: std::io::Read>(
        tokenizer: &mut JackTokenizer<T>,
    ) -> Result<Option<Subroutine>, JackcError> {
        let kind = match tokenizer.advance()? {
            Token::Keyword(KeywordKind::Constructor) => SubroutineKind::Constructor,
            Token::Keyword(KeywordKind::Function) => SubroutineKind::Function,
            Token::Keyword(KeywordKind::Method) => SubroutineKind::Method,
            t => {
                tokenizer.unread_token(t);
                return Ok(None);
            }
        };

        let v_type = Type::parse(tokenizer)?;
        let name = tokenizer.advance()?.expect_identifier()?;
        let parameters = Vec::<Parameter>::parse(tokenizer)?;
        let body = SubroutineBody::parse(tokenizer)?;

        Ok(Some(Subroutine {
            kind,
            v_type,
            name,
            parameters,
            body,
        }))
    }
}

#[derive(Debug)]
enum SubroutineKind {
    Constructor,
    Function,
    Method,
}

impl std::fmt::Display for SubroutineKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &SubroutineKind::Constructor => write!(f, "<keyword> constructor </keyword>"),
            &SubroutineKind::Function => write!(f, "<keyword> function </keyword>"),
            &SubroutineKind::Method => write!(f, "<keyword> method </keyword>"),
        }
    }
}

#[derive(Debug)]
struct Parameter {
    v_type: Type,
    name: String,
}

impl std::fmt::Display for Parameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.v_type)?;
        write!(f, "<identifier> {} </identifier>", self.name)?;
        Ok(())
    }
}

impl Parse for Vec<Parameter> {
    fn parse<T: std::io::Read>(
        tokenizer: &mut JackTokenizer<T>,
    ) -> Result<Vec<Parameter>, JackcError> {
        tokenizer.advance()?.expect_spec_symbol(b'(')?;
        let mut token = tokenizer.advance()?;
        let mut params = vec![];

        while token != Token::Symbol(SymbolKind(b')')) {
            if token != Token::Symbol(SymbolKind(b',')) {
                tokenizer.unread_token(token);
            }

            params.push(Parameter {
                v_type: Type::parse(tokenizer)?,
                name: tokenizer.advance()?.expect_identifier()?,
            });

            token = tokenizer.advance()?;
        }

        Ok(params)
    }
}

#[derive(Debug)]
struct SubroutineBody {
    varss: Vec<Vec<Var>>, // Oops
    statements: Vec<Statement>,
}

impl std::fmt::Display for SubroutineBody {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "<subroutineBody>")?;
        writeln!(f, "<symbol> {{ </symbol>")?;
        for vars in self.varss.iter() {
            Var::fmt_vars(vars, f)?;
        }
        writeln!(f, "<statements>")?;
        for statement in self.statements.iter() {
            writeln!(f, "{}", statement)?;
        }
        writeln!(f, "</statements>")?;
        writeln!(f, "<symbol> }} </symbol>")?;
        write!(f, "</subroutineBody>")?;
        Ok(())
    }
}

impl Parse for SubroutineBody {
    fn parse<T: std::io::Read>(
        tokenizer: &mut JackTokenizer<T>,
    ) -> Result<SubroutineBody, JackcError> {
        tokenizer.advance()?.expect_spec_symbol(b'{')?;
        let mut varss = vec![];
        let mut new_vars = Vec::<Var>::parse(tokenizer)?;
        while new_vars.len() != 0 {
            varss.push(new_vars);
            new_vars = Vec::<Var>::parse(tokenizer)?;
        }
        let statements = Vec::<Statement>::parse(tokenizer)?;
        tokenizer.advance()?.expect_spec_symbol(b'}')?;

        Ok(SubroutineBody { varss, statements })
    }
}

#[derive(Debug)]
struct Var {
    v_type: Type,
    name: String,
}

impl Var {
    fn fmt_vars(vars: &[Var], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if vars.len() == 0 {
            return Ok(());
        }

        let s = &vars[0];
        writeln!(f, "<varDec>")?;
        writeln!(f, "<keyword> var </keyword>")?;
        writeln!(f, "{}", s.v_type)?;
        writeln!(f, "<identifier> {} </identifier>", s.name)?;
        for n in (&vars[1..]).iter() {
            writeln!(f, "<symbol> , </symbol>")?;
            writeln!(f, "<identifier> {} </identifier>", n.name)?;
        }
        writeln!(f, "<symbol> ; </symbol>")?;
        writeln!(f, "</varDec>")?;
        Ok(())
    }
}

impl Parse for Vec<Var> {
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Vec<Var>, JackcError> {
        match tokenizer.advance()? {
            Token::Keyword(KeywordKind::Var) => (),
            t => {
                tokenizer.unread_token(t);
                return Ok(vec![]);
            }
        }

        let v_type = Type::parse(tokenizer)?;
        let mut names = vec![tokenizer.advance()?.expect_identifier()?];
        let mut delim = tokenizer.advance()?.expect_symbol()?;

        while delim != b';' {
            if delim != b',' {
                return Err(JackcError::InvalidSyntax);
            }
            names.push(tokenizer.advance()?.expect_identifier()?);
            delim = tokenizer.advance()?.expect_symbol()?;
        }

        Ok(names
            .into_iter()
            .map(|name| Var {
                v_type: v_type.clone(),
                name,
            })
            .collect())
    }
}

#[derive(Debug)]
enum Statement {
    LetStatement {
        var_name: String,
        index: Option<Expression>,
        rhs: Expression,
    },
    IfStatement {
        condition: Expression,
        if_statements: Vec<Statement>,
        else_statements: Vec<Statement>,
    },
    WhileStatement {
        condition: Expression,
        statements: Vec<Statement>,
    },
    DoStatement {
        subroutine_call: SubroutineCall,
    },
    ReturnStatement {
        value: Option<Expression>,
    },
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &Statement::LetStatement {
                ref var_name,
                ref index,
                ref rhs,
            } => {
                writeln!(f, "<letStatement>")?;
                writeln!(f, "<keyword> let </keyword>")?;
                writeln!(f, "<identifier> {} </identifier>", var_name)?;

                if let &Some(ref expr) = index {
                    writeln!(f, "<symbol> [ </symbol>")?;
                    writeln!(f, "{}", expr)?;
                    writeln!(f, "<symbol> ] </symbol>")?;
                }

                writeln!(f, "<symbol> = </symbol>")?;
                writeln!(f, "{}", rhs)?;
                writeln!(f, "<symbol> ; </symbol>")?;
                write!(f, "</letStatement>")?;
            }
            &Statement::IfStatement {
                ref condition,
                ref if_statements,
                ref else_statements,
            } => {
                writeln!(f, "<ifStatement>")?;
                writeln!(f, "<keyword> if </keyword>")?;
                writeln!(f, "<symbol> ( </symbol>")?;
                writeln!(f, "{}", condition)?;
                writeln!(f, "<symbol> ) </symbol>")?;

                writeln!(f, "<symbol> {{ </symbol>")?;
                writeln!(f, "<statements>")?;
                for statement in if_statements.iter() {
                    writeln!(f, "{}", statement)?;
                }
                writeln!(f, "</statements>")?;
                writeln!(f, "<symbol> }} </symbol>")?;

                if else_statements.len() != 0 {
                    writeln!(f, "<keyword> else </keyword>")?;
                    writeln!(f, "<symbol> {{ </symbol>")?;
                    writeln!(f, "<statements>")?;
                    for statement in else_statements.iter() {
                        writeln!(f, "{}", statement)?;
                    }
                    writeln!(f, "</statements>")?;
                    writeln!(f, "<symbol> }} </symbol>")?;
                }
                write!(f, "</ifStatement>")?;
            }
            &Statement::WhileStatement {
                ref condition,
                ref statements,
            } => {
                writeln!(f, "<whileStatement>")?;
                writeln!(f, "<keyword> while </keyword>")?;
                writeln!(f, "<symbol> ( </symbol>")?;
                writeln!(f, "{}", condition)?;
                writeln!(f, "<symbol> ) </symbol>")?;

                writeln!(f, "<symbol> {{ </symbol>")?;
                writeln!(f, "<statements>")?;
                for statement in statements.iter() {
                    writeln!(f, "{}", statement)?;
                }
                writeln!(f, "</statements>")?;
                writeln!(f, "<symbol> }} </symbol>")?;
                write!(f, "</whileStatement>")?;
            }
            &Statement::DoStatement {
                ref subroutine_call,
            } => {
                writeln!(f, "<doStatement>")?;
                writeln!(f, "<keyword> do </keyword>")?;
                writeln!(f, "{}", subroutine_call)?;
                writeln!(f, "<symbol> ; </symbol>")?;
                write!(f, "</doStatement>")?;
            }
            &Statement::ReturnStatement { ref value } => {
                writeln!(f, "<returnStatement>")?;
                writeln!(f, "<keyword> return </keyword>")?;
                if let Some(ref value) = value {
                    writeln!(f, "{}", value)?;
                }
                writeln!(f, "<symbol> ; </symbol>")?;
                write!(f, "</returnStatement>")?;
            }
        }

        Ok(())
    }
}

impl Parse for Statement {
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Statement, JackcError> {
        match tokenizer.advance()?.expect_keyword()? {
            KeywordKind::Let => {
                let var_name = tokenizer.advance()?.expect_identifier()?;
                let symbol = tokenizer.advance()?.expect_symbol()?;

                let index = match symbol {
                    b'[' => {
                        let result = Expression::parse(tokenizer)?;
                        tokenizer.advance()?.expect_spec_symbol(b']')?;
                        tokenizer.advance()?.expect_spec_symbol(b'=')?;
                        Some(result)
                    }
                    b'=' => None,
                    _ => return Err(JackcError::InvalidSyntax),
                };

                let rhs = Expression::parse(tokenizer)?;
                tokenizer.advance()?.expect_spec_symbol(b';')?;

                Ok(Statement::LetStatement {
                    var_name,
                    index,
                    rhs,
                })
            }
            KeywordKind::If => {
                tokenizer.advance()?.expect_spec_symbol(b'(')?;
                let condition = Expression::parse(tokenizer)?;
                tokenizer.advance()?.expect_spec_symbol(b')')?;
                tokenizer.advance()?.expect_spec_symbol(b'{')?;
                let if_statements = Vec::<Statement>::parse(tokenizer)?;
                tokenizer.advance()?.expect_spec_symbol(b'}')?;
                let token = tokenizer.advance()?;
                let else_statements = if token == Token::Keyword(KeywordKind::Else) {
                    tokenizer.advance()?.expect_spec_symbol(b'{')?;
                    let result = Vec::<Statement>::parse(tokenizer)?;
                    tokenizer.advance()?.expect_spec_symbol(b'}')?;
                    result
                } else {
                    tokenizer.unread_token(token);
                    vec![]
                };

                Ok(Statement::IfStatement {
                    condition,
                    if_statements,
                    else_statements,
                })
            }
            KeywordKind::While => {
                tokenizer.advance()?.expect_spec_symbol(b'(')?;
                let condition = Expression::parse(tokenizer)?;
                tokenizer.advance()?.expect_spec_symbol(b')')?;
                tokenizer.advance()?.expect_spec_symbol(b'{')?;
                let statements = Vec::<Statement>::parse(tokenizer)?;
                tokenizer.advance()?.expect_spec_symbol(b'}')?;
                Ok(Statement::WhileStatement {
                    condition,
                    statements,
                })
            }
            KeywordKind::Do => {
                let s = tokenizer.advance()?.expect_identifier()?;
                let subroutine_call = SubroutineCall::parse_with_first_ident(s, tokenizer)?;
                tokenizer.advance()?.expect_spec_symbol(b';')?;
                Ok(Statement::DoStatement { subroutine_call })
            }
            KeywordKind::Return => {
                let next = tokenizer.advance()?;

                if next == Token::Symbol(SymbolKind(b';')) {
                    Ok(Statement::ReturnStatement { value: None })
                } else {
                    tokenizer.unread_token(next);
                    let expr = Expression::parse(tokenizer)?;
                    tokenizer.advance()?.expect_spec_symbol(b';')?;
                    Ok(Statement::ReturnStatement { value: Some(expr) })
                }
            }
            _ => Err(JackcError::InvalidSyntax),
        }
    }
}

impl Parse for Vec<Statement> {
    fn parse<T: std::io::Read>(
        tokenizer: &mut JackTokenizer<T>,
    ) -> Result<Vec<Statement>, JackcError> {
        let mut result = vec![];
        let mut next = tokenizer.advance()?;

        while next != Token::Symbol(SymbolKind(b'}')) {
            tokenizer.unread_token(next);
            result.push(Statement::parse(tokenizer)?);
            next = tokenizer.advance()?;
        }

        tokenizer.unread_token(next);

        Ok(result)
    }
}

#[derive(Debug)]
struct Expression {
    term: Term,
    ops: Vec<(Op, Term)>,
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
struct SubroutineCall {
    kind: SubroutineCallKind,
    name: String,
    args: Vec<Expression>,
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
    fn parse_with_first_ident(
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

impl Parse for Class {
    fn parse<T: std::io::Read>(tokenizer: &mut JackTokenizer<T>) -> Result<Class, JackcError> {
        if tokenizer.advance()? != Token::Keyword(KeywordKind::Class) {
            return Err(JackcError::ExpectedKeywordNotAppear("class"));
        }

        let class_name = tokenizer.advance()?.expect_identifier()?;
        tokenizer.advance()?.expect_spec_symbol(b'{')?;

        let mut varss = vec![];
        let mut new_vars = Vec::<ClassVar>::parse(tokenizer)?;

        while new_vars.len() != 0 {
            varss.push(new_vars);
            new_vars = Vec::<ClassVar>::parse(tokenizer)?;
        }

        let mut subroutines = vec![];

        while let Some(s) = Option::<Subroutine>::parse(tokenizer)? {
            subroutines.push(s);
        }

        tokenizer.advance()?.expect_spec_symbol(b'}')?;

        if tokenizer.advance()? != Token::EndOfFile {
            Err(JackcError::InvalidSyntax)
        } else {
            Ok(Class {
                name: class_name,
                varss,
                subroutines,
            })
        }
    }
}
