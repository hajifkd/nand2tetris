use crate::codegen::{call, pop, push, Context, ContextInfo};
use crate::lexer::{JackTokenizer, KeywordKind, SymbolKind, Token};
use crate::parser::statement::Statement;
use crate::parser::Parse;
use crate::JackcError;

#[derive(Debug)]
pub struct Class {
    name: String,
    varss: Vec<Vec<ClassVar>>, // Oops
    subroutines: Vec<Subroutine>,
}

impl Context for Class {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &mut ContextInfo,
    ) -> Result<(), JackcError> {
        context.class_name = self.name.clone();
        context.statics.clear();
        context.fields.clear();

        let mut i_static = 0;
        let mut i_field = 0;

        for class_var in self.varss.iter().flat_map(|vars| vars.iter()) {
            match class_var.kind {
                ClassVarKind::Static => {
                    context
                        .statics
                        .insert(class_var.name.clone(), (class_var.v_type.clone(), i_static));
                    i_static += 1;
                }
                ClassVarKind::Field => {
                    context
                        .fields
                        .insert(class_var.name.clone(), (class_var.v_type.clone(), i_field));
                    i_field += 1;
                }
            }
        }

        context.memory_size = i_field as _;

        for subroutine in self.subroutines.iter() {
            subroutine.generate(writer, context)?;
        }

        Ok(())
    }
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
pub enum Type {
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

impl Context for Subroutine {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &mut ContextInfo,
    ) -> Result<(), JackcError> {
        context.arguments.clear();

        writeln!(
            writer,
            "function {}.{} {}",
            context.class_name,
            self.name,
            self.body.varss.iter().map(Vec::len).sum::<usize>() as u16
        )?;

        let arg_off = match self.kind {
            SubroutineKind::Constructor => {
                push(writer, "constant", context.memory_size)?;
                call(writer, "Memory", "alloc", 1)?;
                pop(writer, "pointer", 0)?;
                0
            }
            SubroutineKind::Method => {
                push(writer, "argument", 0)?;
                pop(writer, "pointer", 0)?;
                1
            }
            _ => 0,
        };

        for (n, parameter) in self.parameters.iter().enumerate() {
            context.arguments.insert(
                parameter.name.clone(),
                (parameter.v_type.clone(), n + arg_off),
            );
        }

        self.body.generate(writer, context)?;

        Ok(())
    }
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

#[derive(Debug, Eq, PartialEq)]
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

impl Context for SubroutineBody {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &mut ContextInfo,
    ) -> Result<(), JackcError> {
        context.vars.clear();
        for (n, var) in self.varss.iter().flat_map(|vars| vars.iter()).enumerate() {
            context
                .vars
                .insert(var.name.clone(), (var.v_type.clone(), n));
        }
        for statement in self.statements.iter() {
            statement.generate(writer, context)?;
        }

        Ok(())
    }
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
