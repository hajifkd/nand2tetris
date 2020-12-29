use anyhow::{anyhow, Context, Result};
use jackc::lexer::{JackTokenizer, Token};
use std::env::args;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};

fn main() -> Result<()> {
    let args = args().collect::<Vec<_>>();
    if args.len() != 3 {
        println!("USAGE:\n  {} <src> <dst>", args[0]);
        return Err(anyhow!("Invalid argument"));
    }
    let f = File::open(&args[1])?;
    let mut tokenizer = JackTokenizer::new(BufReader::new(f));
    let mut out = BufWriter::new(File::create(&args[2])?);

    writeln!(&mut out, "<tokens>")?;
    loop {
        let token = tokenizer
            .advance()
            .with_context(|| format!("line: {}", tokenizer.line()))?;

        if token == Token::EndOfFile {
            break;
        }

        writeln!(&mut out, "{}", token.to_xml_element())?;
    }
    writeln!(&mut out, "</tokens>")?;
    Ok(())
}
