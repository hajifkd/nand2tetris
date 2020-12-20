use std::borrow::Cow;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::io::BufRead;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum IlcError {
    #[error("L{0} Invalid command: {1}")]
    InvalidCommand(usize, String),
    #[error(transparent)]
    IoError(#[from] std::io::Error),
}

#[derive(Error, Debug)]
#[error("Undefined symbol: {0}")]
pub struct UndefinedSymbolError(String);

pub enum ArithmeticKind {
    Add,
    Sub,
    Neg,
    Eq,
    Gt,
    Lt,
    And,
    Or,
    Not,
}

impl ArithmeticKind {
    fn generate(&self, ip: u16) -> Vec<Cow<'static, str>> {
        let ops = match &self {
            ArithmeticKind::Add => vec!["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=D+M"],
            ArithmeticKind::Sub => vec!["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=M-D"],
            ArithmeticKind::And => vec!["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=D&M"],
            ArithmeticKind::Or => vec!["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=D|M"],
            ArithmeticKind::Neg => vec!["@SP", "A=M-1", "M=-M"],
            ArithmeticKind::Not => vec!["@SP", "A=M-1", "M=!M"],
            ArithmeticKind::Eq | ArithmeticKind::Gt | ArithmeticKind::Lt => vec![
                "@SP",
                "A=M-1",
                "D=M",
                "@SP",
                "M=M-1",
                "A=M-1",
                "D=M-D",
                "M=-1",
                "", // insert later
                match &self {
                    ArithmeticKind::Eq => "D;JEQ",
                    ArithmeticKind::Gt => "D;JGT",
                    ArithmeticKind::Lt => "D;JLT",
                    _ => unreachable!(),
                },
                "@SP",
                "A=M-1",
                "M=0",
            ],
        };
        ops.iter()
            .map(|&s| {
                if s.is_empty() {
                    Cow::from(format!("@{}", ip + ops.len() as u16))
                } else {
                    Cow::from(s)
                }
            })
            .collect()
    }
}

impl TryFrom<&[&str]> for ArithmeticKind {
    type Error = ();

    fn try_from(value: &[&str]) -> Result<Self, ()> {
        if value.len() != 1 {
            Err(())
        } else {
            Ok(match value[0] {
                "add" => ArithmeticKind::Add,
                "sub" => ArithmeticKind::Sub,
                "neg" => ArithmeticKind::Neg,
                "eq" => ArithmeticKind::Eq,
                "gt" => ArithmeticKind::Gt,
                "lt" => ArithmeticKind::Lt,
                "and" => ArithmeticKind::And,
                "or" => ArithmeticKind::Or,
                "not" => ArithmeticKind::Not,
                _ => return Err(()),
            })
        }
    }
}

#[derive(Eq, PartialEq)]
pub enum SegmentKind {
    Argument,
    Local,
    Static,
    Constant,
    This,
    That,
    Pointer,
    Temp,
}

enum Addr {
    Immediate(u16),
    Pointer(u16),
}

impl SegmentKind {
    fn address(&self) -> Option<Addr> {
        Some(match self {
            SegmentKind::Argument => Addr::Pointer(2),
            SegmentKind::Local => Addr::Pointer(1),
            SegmentKind::Static => Addr::Immediate(16),
            SegmentKind::Constant => return None,
            SegmentKind::This => Addr::Pointer(3),
            SegmentKind::That => Addr::Pointer(4),
            SegmentKind::Pointer => Addr::Immediate(3),
            SegmentKind::Temp => Addr::Immediate(5),
        })
    }
}

impl TryFrom<&str> for SegmentKind {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, ()> {
        Ok(match value {
            "argument" => SegmentKind::Argument,
            "local" => SegmentKind::Local,
            "static" => SegmentKind::Static,
            "constant" => SegmentKind::Constant,
            "this" => SegmentKind::This,
            "that" => SegmentKind::That,
            "pointer" => SegmentKind::Pointer,
            "temp" => SegmentKind::Temp,
            _ => return Err(()),
        })
    }
}

pub enum Command {
    Arithmetic(ArithmeticKind),
    Push { segment: SegmentKind, index: u16 },
    Pop { segment: SegmentKind, index: u16 },
    // Unimpl'd
    Label,
    Goto,
    If,
    Function,
    Return,
    Call,
}

impl Command {
    pub fn generate(
        &self,
        ip: u16,
        _symbol_table: &HashMap<String, u16>,
    ) -> Result<Vec<Cow<'static, str>>, UndefinedSymbolError> {
        Ok(match &self {
            Command::Arithmetic(arithm) => arithm.generate(ip),
            Command::Pop { segment, index } => {
                let addr = segment.address();
                let mut result = vec!["@SP", "A=M-1", "D=M", "@SP", "M=M-1"]
                    .into_iter()
                    .map(Cow::from)
                    .collect::<Vec<_>>(); // poped, value is at D
                match addr.unwrap() {
                    Addr::Immediate(n) => {
                        result.push(format!("@{}", n + index).into());
                        result.push("M=D".into());
                    }
                    Addr::Pointer(n) => {
                        result.push("@13".into());
                        result.push("M=D".into()); // stack val -> @13
                        result.push(format!("@{}", n).into());
                        result.push("D=M".into());
                        result.push(format!("@{}", index).into());
                        let rest = vec!["D=D+A", "@14", "M=D", "@13", "D=M", "@14", "A=M", "M=D"]
                            .into_iter()
                            .map(Cow::from);
                        result.extend(rest);
                    }
                }

                result
            }
            Command::Push { segment, index } => {
                let mut result = Vec::<Cow<'static, str>>::new();
                if segment == &SegmentKind::Constant {
                    result.push(format!("@{}", index).into());
                    let rest = vec!["D=A", "@SP", "A=M", "M=D", "D=A", "@SP", "M=D+1"]
                        .into_iter()
                        .map(Cow::from);
                    result.extend(rest);
                } else {
                    let addr = segment.address();
                    match addr.unwrap() {
                        Addr::Immediate(n) => {
                            result.push(format!("@{}", n + index).into());
                            let rest = vec!["D=M", "@SP", "A=M", "M=D", "D=A", "@SP", "M=D+1"]
                                .into_iter()
                                .map(Cow::from);
                            result.extend(rest);
                        }
                        Addr::Pointer(n) => {
                            result.push(format!("@{}", n).into());
                            result.push("D=M".into());
                            result.push(format!("@{}", index).into());
                            let rest =
                                vec!["A=D+A", "D=M", "@SP", "A=M", "M=D", "D=A", "@SP", "M=D+1"]
                                    .into_iter()
                                    .map(Cow::from);
                            result.extend(rest);
                        }
                    }
                }

                result
            }
            _ => unimplemented!(),
        })
    }
}

impl TryFrom<&[&str]> for Command {
    type Error = ();

    fn try_from(value: &[&str]) -> Result<Self, ()> {
        if value.len() == 0 || value.len() > 3 {
            Err(())
        } else {
            Ok(match value[0] {
                "push" => Command::Push {
                    segment: SegmentKind::try_from(value[1])?,
                    index: value[2].parse::<i16>().map(|i| i as u16).map_err(|_| ())?,
                },
                "pop" => Command::Pop {
                    segment: SegmentKind::try_from(value[1])?,
                    index: value[2].parse::<i16>().map(|i| i as u16).map_err(|_| ())?,
                },
                _ => Command::Arithmetic(ArithmeticKind::try_from(value)?),
            })
        }
    }
}

pub struct Parser<T: BufRead> {
    next: Option<Command>,
    reader: T,
    line: usize,
}

impl<T: BufRead> Parser<T> {
    pub fn new(reader: T) -> Result<Self, IlcError> {
        let mut result = Parser {
            reader,
            next: None,
            line: 0,
        };
        result.advance()?;
        Ok(result)
    }

    pub fn advance(&mut self) -> Result<Option<Command>, IlcError> {
        let curr = self.next.take();
        let mut line = String::new();

        while self.reader.read_line(&mut line)? != 0 {
            self.line += 1;

            let commands = line
                .trim()
                .split("//")
                .next()
                .ok_or_else(|| IlcError::InvalidCommand(self.line, line.clone()))?
                .split_whitespace()
                .collect::<Vec<&str>>();

            if commands.len() == 0 {
                line.clear();
                continue;
            }

            self.next = Some(
                Command::try_from(&commands[..])
                    .map_err(|_| IlcError::InvalidCommand(self.line, line.clone()))?,
            );
            break;
        }

        Ok(curr)
    }
}
