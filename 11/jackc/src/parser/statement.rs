use crate::codegen::{goto, if_goto, label, pop, push, Codegen, Context, ContextInfo};
use crate::lexer::{JackTokenizer, KeywordKind, SymbolKind, Token};
use crate::parser::expression::{Expression, SubroutineCall};
use crate::parser::Parse;
use crate::JackcError;

#[derive(Debug)]
pub(crate) enum Statement {
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

impl Context for Statement {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &mut ContextInfo,
    ) -> Result<(), JackcError> {
        match self {
            Statement::LetStatement {
                var_name,
                index,
                rhs,
            } => {
                rhs.generate(writer, context)?;
                let (segment, _v_type, s_index) = context
                    .find(var_name)
                    .ok_or_else(|| JackcError::ValiableNotFound(var_name.to_owned()))?;
                let s_index: u16 = s_index as _;
                if let Some(index) = index {
                    push(writer, segment, s_index)?;
                    index.generate(writer, context)?;
                    writeln!(writer, "add")?;
                    pop(writer, "pointer", 1)?;
                    pop(writer, "that", 0)?;
                } else {
                    pop(writer, segment, s_index)?;
                }
            }
            Statement::IfStatement {
                condition,
                if_statements,
                else_statements,
            } => {
                let label_name = context.label();
                let then_label = format!("{}.then", label_name);
                let endif_label = format!("{}.endif", label_name);
                condition.generate(writer, context)?;
                if_goto(writer, &then_label)?;
                for statement in else_statements.iter() {
                    statement.generate(writer, context)?;
                }
                goto(writer, &endif_label)?;
                label(writer, &then_label)?;
                for statement in if_statements.iter() {
                    statement.generate(writer, context)?;
                }
                label(writer, &endif_label)?;
            }
            Statement::WhileStatement {
                condition,
                statements,
            } => {
                let label_name = context.label();
                let start_label = format!("{}.condition", label_name);
                let endwhile_label = format!("{}.endwhile", label_name);
                label(writer, &start_label)?;
                condition.generate(writer, context)?;
                push(writer, "constant", 0)?;
                writeln!(writer, "eq")?;
                if_goto(writer, &endwhile_label)?;
                for statement in statements.iter() {
                    statement.generate(writer, context)?;
                }
                goto(writer, &start_label)?;
                label(writer, &endwhile_label)?;
            }
            Statement::DoStatement { subroutine_call } => {
                subroutine_call.generate(writer, context)?;
                pop(writer, "temp", 0)?;
            }
            Statement::ReturnStatement { value } => {
                if let Some(expr) = value {
                    expr.generate(writer, context)?;
                } else {
                    push(writer, "constant", 0)?;
                }
                writeln!(writer, "return")?;
            }
        }
        Ok(())
    }
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
