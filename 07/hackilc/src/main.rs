use anyhow::{Context, Result};
use hackilc::Parser;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};

fn main() -> Result<()> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 3 {
        println!(
            "USAGE: {} <src.vm> <dst.asm>",
            if args.len() > 0 { &args[0] } else { "" }
        );

        return Ok(());
    }

    let src = File::open(&args[1]).with_context(|| format!("Failed to open {}", &args[1]))?;
    let src = BufReader::new(src);
    let dst = File::create(&args[2]).with_context(|| format!("Failed to create {}", &args[2]))?;
    let mut dst = BufWriter::new(dst);

    let table = std::collections::HashMap::new();
    let mut ops = vec![];
    let mut ip = 0;

    // first pass
    let mut parser = Parser::new(src).context("Failed to parse")?;
    loop {
        let line = parser.advance().context("Failed to parse")?;
        if line.is_none() {
            break;
        }
        let cmd = line.unwrap();
        let asms = cmd.generate(ip, &table)?;
        ip += asms.len() as u16;
        ops.extend(asms);
    }

    // second pass
    for asm in ops.into_iter() {
        writeln!(&mut dst, "{}", asm).with_context(|| format!("Failed to write {}", &args[2]))?;
    }

    Ok(())
}
