use anyhow::{anyhow, Context as ACont, Result};
use jackc::codegen::{Context, ContextInfo};
use jackc::lexer::JackTokenizer;
use jackc::parser::{Class, Parse};
use std::env::args;
use std::fs::File;
use std::io::{BufReader, BufWriter};

fn main() -> Result<()> {
    let args = args().collect::<Vec<_>>();
    if args.len() != 3 {
        println!("USAGE:\n  {} <src> <dst>", args[0]);
        return Err(anyhow!("Invalid argument"));
    }
    let f = File::open(&args[1])?;
    let mut tokenizer = JackTokenizer::new(BufReader::new(f));
    let mut out = BufWriter::new(File::create(&args[2])?);
    let mut context = ContextInfo::new();

    let class =
        Class::parse(&mut tokenizer).with_context(|| format!("line {}:", tokenizer.line()))?;
    class.generate(&mut out, &mut context)?;
    Ok(())
}
