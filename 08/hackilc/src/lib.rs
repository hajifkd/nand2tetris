use std::borrow::Cow;
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
    fn generate(&self, line: usize) -> Vec<Cow<'static, str>> {
        match &self {
            ArithmeticKind::Add => ["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=D+M"]
                .iter()
                .map(|&s| s.into())
                .collect(),
            ArithmeticKind::Sub => ["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=M-D"]
                .iter()
                .map(|&s| s.into())
                .collect(),
            ArithmeticKind::And => ["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=D&M"]
                .iter()
                .map(|&s| s.into())
                .collect(),
            ArithmeticKind::Or => ["@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "M=D|M"]
                .iter()
                .map(|&s| s.into())
                .collect(),
            ArithmeticKind::Neg => ["@SP", "A=M-1", "M=-M"].iter().map(|&s| s.into()).collect(),
            ArithmeticKind::Not => ["@SP", "A=M-1", "M=!M"].iter().map(|&s| s.into()).collect(),
            ArithmeticKind::Eq | ArithmeticKind::Gt | ArithmeticKind::Lt => {
                let mut v = [
                    "@SP", "A=M-1", "D=M", "@SP", "M=M-1", "A=M-1", "D=M-D", "M=-1",
                ]
                .iter()
                .map(|&s| s.into())
                .collect::<Vec<_>>();
                v.push(Cow::from(format!("@$INT${}", line)));
                v.extend(
                    [
                        match &self {
                            ArithmeticKind::Eq => "D;JEQ",
                            ArithmeticKind::Gt => "D;JGT",
                            ArithmeticKind::Lt => "D;JLT",
                            _ => unreachable!(),
                        },
                        "@SP",
                        "A=M-1",
                        "M=0",
                    ]
                    .iter()
                    .map(|&s| s.into()),
                );
                v.push(Cow::from(format!("($INT${})", line)));
                v
            }
        }
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
    Internal,
    Absolute,
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
            SegmentKind::Internal => Addr::Immediate(13),
            SegmentKind::Absolute => Addr::Immediate(0),
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

pub struct Command {
    kind: CommandKind,
    line: usize,
}

impl Command {
    pub fn generate(&self) -> Vec<Cow<'static, str>> {
        self.kind.generate(self.line)
    }
}

enum CommandKind {
    Initialize,
    Arithmetic(ArithmeticKind),
    Push { segment: SegmentKind, index: u16 },
    Pop { segment: SegmentKind, index: u16 },
    Label(String),
    Goto(String),
    If(String),
    Function { name: String, n_local: u16 },
    Return,
    Call { name: String, n_arg: u16 },
}

fn generate_pop(segment: &SegmentKind, index: u16) -> Vec<Cow<'static, str>> {
    let addr = segment.address();
    let mut result = ["@SP", "M=M-1", "A=M", "D=M"]
        .iter()
        .map(|&s| s.into())
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
            result.extend(
                ["D=D+A", "@14", "M=D", "@13", "D=M", "@14", "A=M", "M=D"]
                    .iter()
                    .map(|&s| s.into()),
            );
        }
    }

    result
}

fn generate_push(segment: &SegmentKind, index: u16) -> Vec<Cow<'static, str>> {
    let mut result = Vec::<Cow<'static, str>>::new();
    if segment == &SegmentKind::Constant {
        result.push(format!("@{}", index).into());
        result.extend(
            ["D=A", "@SP", "A=M", "M=D", "D=A", "@SP", "M=D+1"]
                .iter()
                .map(|&s| s.into()),
        );
    } else {
        let addr = segment.address();
        match addr.unwrap() {
            Addr::Immediate(n) => {
                result.push(format!("@{}", n + index).into());
                result.extend(
                    ["D=M", "@SP", "A=M", "M=D", "D=A", "@SP", "M=D+1"]
                        .iter()
                        .map(|&s| s.into()),
                );
            }
            Addr::Pointer(n) => {
                result.push(format!("@{}", n).into());
                result.push("D=M".into());
                result.push(format!("@{}", index).into());
                result.extend(
                    ["A=D+A", "D=M", "@SP", "A=M", "M=D", "D=A", "@SP", "M=D+1"]
                        .iter()
                        .map(|&s| s.into()),
                );
            }
        }
    }

    result
}

fn generate_goto(label: &str) -> Vec<Cow<'static, str>> {
    vec![format!("@{}", label).into(), "0;JMP".into()]
}

impl CommandKind {
    fn generate(&self, line: usize) -> Vec<Cow<'static, str>> {
        match &self {
            CommandKind::Initialize => vec![
                "@261".into(), // 256 + 5
                "D=A".into(),
                "@SP".into(),
                "M=D".into(),
                "@Sys.init".into(),
                "0;JMP".into(),
            ],
            CommandKind::Arithmetic(arithm) => arithm.generate(line),
            CommandKind::Pop { segment, index } => generate_pop(segment, *index),
            CommandKind::Push { segment, index } => generate_push(segment, *index),
            CommandKind::Label(label) => vec![format!("({})", label).into()],
            CommandKind::Goto(label) => generate_goto(&label),
            CommandKind::If(label) => vec![
                "@SP".into(),
                "M=M-1".into(),
                "A=M".into(),
                "D=M".into(),
                format!("@{}", label).into(),
                "D;JNE".into(),
            ],
            CommandKind::Function { name, n_local } => {
                let mut codes = vec![
                    format!("({})", name).into(),
                    format!("@{}", n_local).into(),
                    "D=A".into(),
                    "@13".into(),
                    "M=D".into(),
                    format!("($INT${}$1)", line).into(),
                    "@13".into(),
                    "D=M".into(),
                    format!("@$INT${}$2", line).into(),
                    "D;JEQ".into(),
                    "@13".into(),
                    "M=D-1".into(),
                ];
                codes.extend(generate_push(&SegmentKind::Constant, 0));
                codes.extend(generate_goto(&format!("$INT${}$1", line)));
                codes.push(format!("($INT${}$2)", line).into());
                codes
            }
            CommandKind::Call { name, n_arg } => {
                let mut codes = vec![
                    format!("@$INT${}", line).into(),
                    "D=A".into(),
                    "@13".into(),
                    "M=D".into(),
                ];

                codes.extend(generate_push(&SegmentKind::Internal, 0));
                codes.extend(generate_push(&SegmentKind::Absolute, 1));
                codes.extend(generate_push(&SegmentKind::Absolute, 2));
                codes.extend(generate_push(&SegmentKind::Absolute, 3));
                codes.extend(generate_push(&SegmentKind::Absolute, 4));

                codes.extend(vec![
                    "@SP".into(),
                    "D=M".into(),
                    "@LCL".into(),
                    "M=D".into(),
                    "@ARG".into(),
                    "M=D".into(),
                    format!("@{}", n_arg + 5).into(),
                    "D=A".into(),
                    "@ARG".into(),
                    "M=M-D".into(),
                ]);

                codes.extend(generate_goto(&name));
                codes.push(format!("($INT${})", line).into());
                codes
            }
            CommandKind::Return => {
                let mut codes = vec![
                    "@SP".into(),
                    "A=M-1".into(),
                    "D=M".into(),
                    "@13".into(), // ret val
                    "M=D".into(),
                    "@ARG".into(),
                    "D=M".into(),
                    "@14".into(), // orig sp
                    "M=D+1".into(),
                    "@LCL".into(),
                    "D=M".into(),
                    "@SP".into(),
                    "M=D".into(),
                ];

                codes.extend(generate_pop(&SegmentKind::Absolute, 4)); // that
                codes.extend(generate_pop(&SegmentKind::Absolute, 3)); // this
                codes.extend(generate_pop(&SegmentKind::Absolute, 2)); // arg
                codes.extend(generate_pop(&SegmentKind::Absolute, 1)); // lcl
                codes.extend(generate_pop(&SegmentKind::Internal, 2)); // ret addr

                codes.extend(vec![
                    "@14".into(),
                    "D=M".into(),
                    "@SP".into(),
                    "M=D".into(), // orig sp
                    "@13".into(),
                    "D=M".into(),
                    "@SP".into(),
                    "A=M-1".into(),
                    "M=D".into(), // ret val
                    "@15".into(),
                    "A=M".into(),
                    "0;JMP".into(), // ret
                ]);

                codes
            }
        }
    }
}

fn is_il_symbol(symbol: &str) -> bool {
    let first = symbol.chars().next();

    if first.is_none() || first.unwrap().is_numeric() {
        false
    } else {
        symbol
            .chars()
            .all(|c| c.is_alphanumeric() || c == '.' || c == '_' || c == ':')
    }
}

impl TryFrom<&[&str]> for CommandKind {
    type Error = ();

    fn try_from(value: &[&str]) -> Result<Self, ()> {
        if value.len() == 0 || value.len() > 3 {
            Err(())
        } else {
            Ok(match value[0] {
                "push" => {
                    if value.len() == 3 {
                        CommandKind::Push {
                            segment: SegmentKind::try_from(value[1])?,
                            index: value[2].parse::<i16>().map(|i| i as u16).map_err(|_| ())?,
                        }
                    } else {
                        return Err(());
                    }
                }
                "pop" => {
                    if value.len() == 3 {
                        CommandKind::Pop {
                            segment: SegmentKind::try_from(value[1])?,
                            index: value[2].parse::<i16>().map(|i| i as u16).map_err(|_| ())?,
                        }
                    } else {
                        return Err(());
                    }
                }
                "label" => {
                    if value.len() == 2 && is_il_symbol(&value[1]) {
                        CommandKind::Label(value[1].to_owned())
                    } else {
                        return Err(());
                    }
                }
                "goto" => {
                    if value.len() == 2 && is_il_symbol(&value[1]) {
                        CommandKind::Goto(value[1].to_owned())
                    } else {
                        return Err(());
                    }
                }
                "if-goto" => {
                    if value.len() == 2 && is_il_symbol(&value[1]) {
                        CommandKind::If(value[1].to_owned())
                    } else {
                        return Err(());
                    }
                }
                "function" => {
                    if value.len() == 3 && is_il_symbol(&value[1]) {
                        CommandKind::Function {
                            name: value[1].to_owned(),
                            n_local: value[2].parse::<i16>().map(|i| i as u16).map_err(|_| ())?,
                        }
                    } else {
                        return Err(());
                    }
                }
                "call" => {
                    if value.len() == 3 && is_il_symbol(&value[1]) {
                        CommandKind::Call {
                            name: value[1].to_owned(),
                            n_arg: value[2].parse::<i16>().map(|i| i as u16).map_err(|_| ())?,
                        }
                    } else {
                        return Err(());
                    }
                }
                "return" => {
                    if value.len() == 1 {
                        CommandKind::Return
                    } else {
                        return Err(());
                    }
                }
                _ => CommandKind::Arithmetic(ArithmeticKind::try_from(value)?),
            })
        }
    }
}

pub struct Parser<T: BufRead> {
    next: Option<Command>,
    reader: T,
    line: usize,
    initialized: bool,
}

impl<T: BufRead> Parser<T> {
    pub fn new(reader: T) -> Self {
        Parser {
            reader,
            next: None,
            line: 0,
            initialized: false,
        }
    }

    pub fn advance(&mut self) -> Result<Option<Command>, IlcError> {
        if !self.initialized {
            self.initialized = true;
            self.advance()?;
            return Ok(Some(Command {
                kind: CommandKind::Initialize,
                line: 0,
            }));
        }
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

            self.next = Some(Command {
                kind: CommandKind::try_from(&commands[..])
                    .map_err(|_| IlcError::InvalidCommand(self.line, line.clone()))?,
                line: self.line,
            });
            break;
        }

        Ok(curr)
    }
}
