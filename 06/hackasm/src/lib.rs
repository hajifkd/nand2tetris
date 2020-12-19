#[macro_use]
extern crate lazy_static;

//use anyhow::Result;
use std::collections::HashMap;
use std::io::BufRead;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AsmError {
    #[error("Invalid command: {0}")]
    InvalidCommand(String),
    #[error("Undefined symbol {0}")]
    UndefinedSymbol(String),
    #[error("Invalid symbol {0}")]
    InvalidSymbol(String),
    #[error(transparent)]
    IoError(#[from] std::io::Error),
}

#[derive(Debug)]
pub enum ASymbol {
    Symbol(String),
    Literal(u16),
}

#[derive(Debug)]
pub enum Command {
    ACommand(ASymbol),
    CCommand {
        dest: String,
        comp: String,
        jump: String,
    },
    LCommand(String),
}

lazy_static! {
    static ref DEST_LIST: HashMap<String, u16> = {
        let mut map = HashMap::new();
        " M D MD A AM AD AMD"
            .split(' ')
            .enumerate()
            .for_each(|(i, s)| {
                map.insert(s.to_owned(), i as u16);
            });
        map
    };
    static ref JUMP_LIST: HashMap<String, u16> = {
        let mut map = HashMap::new();
        " JGT JEQ JGE JLT JNE JLE JMP"
            .split(' ')
            .enumerate()
            .for_each(|(i, s)| {
                map.insert(s.to_owned(), i as u16);
            });
        map
    };
    static ref COMP_LIST: HashMap<String, u16> = {
        let mut map = HashMap::new();
        map.insert("0".to_owned(), 0b0101010);
        map.insert("1".to_owned(), 0b0111111);
        map.insert("-1".to_owned(), 0b0111010);

        map.insert("D".to_owned(), 0b0001100);
        map.insert("A".to_owned(), 0b0110000);
        map.insert("M".to_owned(), 0b1110000);

        map.insert("!D".to_owned(), 0b0001101);
        map.insert("!A".to_owned(), 0b0110001);
        map.insert("!M".to_owned(), 0b1110001);

        map.insert("-D".to_owned(), 0b0001111);
        map.insert("-A".to_owned(), 0b0110001);
        map.insert("-M".to_owned(), 0b1110001);

        map.insert("D+1".to_owned(), 0b0011111);
        map.insert("A+1".to_owned(), 0b0110111);
        map.insert("M+1".to_owned(), 0b1110111);

        map.insert("D-1".to_owned(), 0b0001110);
        map.insert("A-1".to_owned(), 0b0110010);
        map.insert("M-1".to_owned(), 0b1110010);

        map.insert("D+A".to_owned(), 0b0000010);
        map.insert("D+M".to_owned(), 0b1000010);

        map.insert("D-A".to_owned(), 0b0100011);
        map.insert("D-M".to_owned(), 0b1100011);

        map.insert("A-D".to_owned(), 0b0000111);
        map.insert("M-D".to_owned(), 0b1000111);

        map.insert("D&A".to_owned(), 0b0000000);
        map.insert("D&M".to_owned(), 0b1000000);

        map.insert("D|A".to_owned(), 0b0010101);
        map.insert("D|M".to_owned(), 0b1010101);
        map
    };
}

pub struct Parser<T: BufRead> {
    reader: T,
    next: Option<Command>,
}

fn is_hack_symbol(symbol: &str) -> bool {
    let first = symbol.chars().next();

    if first.is_none() || first.unwrap().is_numeric() {
        false
    } else {
        symbol
            .chars()
            .all(|c| c.is_alphanumeric() || c == '.' || c == '_' || c == '$' || c == ':')
    }
}

impl<T: BufRead> Parser<T> {
    pub fn new(reader: T) -> Result<Self, AsmError> {
        let mut result = Parser { reader, next: None };

        result.advance()?;

        Ok(result)
    }

    pub fn advance(&mut self) -> Result<Option<Command>, AsmError> {
        let current = self.next.take();
        let mut line = String::new();

        while self.reader.read_line(&mut line)? != 0 {
            // remove space and comments
            let mut space_removed: String = line
                .trim()
                .split("//")
                .next()
                .unwrap()
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();

            if space_removed.is_empty() {
                line.clear();
                continue;
            }

            // ACommand
            if space_removed.starts_with("@") {
                let symbol = space_removed.split_off(1);

                if !is_hack_symbol(&symbol) {
                    let num = symbol.parse::<u16>();

                    if num.is_err() {
                        return Err(AsmError::InvalidSymbol(symbol));
                    }

                    self.next = Some(Command::ACommand(ASymbol::Literal(num.unwrap())));
                } else {
                    self.next = Some(Command::ACommand(ASymbol::Symbol(symbol)));
                }
            } else if space_removed.starts_with("(") {
                let mut symbol = space_removed.split_off(1);

                if symbol.pop() != Some(')') {
                    return Err(AsmError::InvalidCommand(line));
                }

                if !is_hack_symbol(&symbol) {
                    return Err(AsmError::InvalidSymbol(symbol));
                }

                self.next = Some(Command::LCommand(symbol));
            } else {
                let jump_split = space_removed.split(';').collect::<Vec<_>>();

                if jump_split.len() != 2 && jump_split.len() != 1 {
                    return Err(AsmError::InvalidCommand(line));
                }

                let compdest = jump_split[0];
                let jump = if jump_split.len() == 1 {
                    ""
                } else {
                    jump_split[1]
                };

                let dest_split = compdest.split('=').collect::<Vec<_>>();

                if dest_split.len() != 2 && dest_split.len() != 1 {
                    return Err(AsmError::InvalidCommand(line));
                }

                let (dest, comp) = if dest_split.len() == 1 {
                    ("", dest_split[0])
                } else {
                    (dest_split[0], dest_split[1])
                };

                if DEST_LIST.contains_key(dest)
                    && COMP_LIST.contains_key(comp)
                    && JUMP_LIST.contains_key(jump)
                {
                    self.next = Some(Command::CCommand {
                        dest: dest.to_owned(),
                        comp: comp.to_owned(),
                        jump: jump.to_owned(),
                    });
                } else {
                    return Err(AsmError::InvalidCommand(space_removed));
                }
            }

            break;
        }

        return Ok(current);
    }
}

pub mod code {
    use super::*;
    pub fn dest(dest: &str) -> Result<u16, AsmError> {
        DEST_LIST
            .get(dest)
            .map(|&n| n)
            .ok_or(AsmError::InvalidCommand(dest.to_owned()))
    }

    pub fn comp(dest: &str) -> Result<u16, AsmError> {
        COMP_LIST
            .get(dest)
            .map(|&n| n)
            .ok_or(AsmError::InvalidCommand(dest.to_owned()))
    }

    pub fn jump(dest: &str) -> Result<u16, AsmError> {
        JUMP_LIST
            .get(dest)
            .map(|&n| n)
            .ok_or(AsmError::InvalidCommand(dest.to_owned()))
    }
}

pub fn symbol_table() -> HashMap<String, u16> {
    let mut result = HashMap::new();
    result.insert("SP".to_owned(), 0);
    result.insert("LCL".to_owned(), 1);
    result.insert("ARG".to_owned(), 2);
    result.insert("THIS".to_owned(), 3);
    result.insert("THAT".to_owned(), 4);
    result.insert("SCREEN".to_owned(), 0x4000);
    result.insert("KBD".to_owned(), 0x6000);

    (0..16).for_each(|i| {
        result.insert(format!("R{}", i), i);
    });

    result
}
