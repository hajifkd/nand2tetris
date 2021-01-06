use crate::parser::Type;
use crate::JackcError;
use std::collections::HashMap;

pub trait Context {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &mut ContextInfo,
    ) -> Result<(), JackcError>;
}

pub(crate) trait Codegen {
    fn generate(
        &self,
        writer: &mut impl std::io::Write,
        context: &ContextInfo,
    ) -> Result<(), JackcError>;
}

pub(crate) fn pop(
    writer: &mut impl std::io::Write,
    segment: &str,
    index: u16,
) -> Result<(), std::io::Error> {
    writeln!(writer, "pop {} {}", segment, index)
}

pub(crate) fn label(writer: &mut impl std::io::Write, label: &str) -> Result<(), std::io::Error> {
    writeln!(writer, "label {}", label)
}

pub(crate) fn if_goto(writer: &mut impl std::io::Write, label: &str) -> Result<(), std::io::Error> {
    writeln!(writer, "if-goto {}", label)
}

pub(crate) fn goto(writer: &mut impl std::io::Write, label: &str) -> Result<(), std::io::Error> {
    writeln!(writer, "goto {}", label)
}

pub(crate) fn push(
    writer: &mut impl std::io::Write,
    segment: &str,
    index: u16,
) -> Result<(), std::io::Error> {
    writeln!(writer, "push {} {}", segment, index)
}

pub(crate) fn call(
    writer: &mut impl std::io::Write,
    receiver: &str,
    name: &str,
    n_args: u16,
) -> Result<(), std::io::Error> {
    writeln!(writer, "call {}.{} {}", receiver, name, n_args)
}

pub struct ContextInfo {
    pub(crate) statics: HashMap<String, (Type, usize)>,
    pub(crate) fields: HashMap<String, (Type, usize)>,
    pub(crate) arguments: HashMap<String, (Type, usize)>,
    pub(crate) vars: HashMap<String, (Type, usize)>,
    pub(crate) class_name: String,
    label_index: usize,
    pub(crate) memory_size: u16,
}

impl ContextInfo {
    pub fn new() -> Self {
        ContextInfo {
            statics: HashMap::new(),
            fields: HashMap::new(),
            arguments: HashMap::new(),
            vars: HashMap::new(),
            class_name: String::new(),
            label_index: 0,
            memory_size: 0,
        }
    }

    pub fn label(&mut self) -> String {
        let i = self.label_index;
        self.label_index += 1;
        format!("INT_{}.{}", self.class_name, i)
    }

    pub fn find<'a>(&'a self, name: &str) -> Option<(&'static str, &'a Type, usize)> {
        if let Some((t, v)) = self.vars.get(name) {
            Some(("local", t, *v))
        } else if let Some((t, v)) = self.arguments.get(name) {
            Some(("argument", t, *v))
        } else if let Some((t, v)) = self.fields.get(name) {
            Some(("this", t, *v))
        } else if let Some((t, v)) = self.statics.get(name) {
            Some(("static", t, *v))
        } else {
            None
        }
    }
}
