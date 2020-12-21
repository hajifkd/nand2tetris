use anyhow::{anyhow, Context, Result};
use hackilc::Parser;
use std::fs::File;
use std::io::{BufReader, BufWriter, Read, Write};

fn main() -> Result<()> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 3 {
        println!(
            "USAGE: {} <src.vm> <dst.asm>",
            if args.len() > 0 { &args[0] } else { "" }
        );

        return Ok(());
    }

    let src: Box<dyn Read> = if std::path::Path::new(&args[1]).is_dir() {
        let mut children = std::fs::read_dir(&args[1])
            .with_context(|| format!("Failed to open directory {}", &args[1]))?
            .filter_map(|e| e.ok().map(|d| d.path()))
            .filter(|p| p.extension().map(|e| e == "vm").unwrap_or(false))
            .map(File::open)
            .collect::<Result<Vec<_>, _>>()?;

        if children.len() == 0 {
            return Err(anyhow!(
                "Directory {} does not contain any vm file",
                &args[1]
            ));
        }

        let tail = children.pop().unwrap();

        children
            .into_iter()
            .fold(Box::new(tail), |acc, x| Box::new(acc.chain(x)))
    } else {
        let src =
            File::open(&args[1]).with_context(|| format!("Failed to open file {}", &args[1]))?;
        Box::new(src)
    };
    let dst = File::create(&args[2]).with_context(|| format!("Failed to create {}", &args[2]))?;
    let mut dst = BufWriter::new(dst);

    let mut parser = Parser::new(BufReader::new(src));
    loop {
        let line = parser.advance().context("Failed to parse")?;
        if line.is_none() {
            break;
        }
        let cmd = line.unwrap();
        let asms = cmd.generate();
        for asm in asms.into_iter() {
            writeln!(&mut dst, "{}", asm)
                .with_context(|| format!("Failed to write {}", &args[2]))?;
        }
    }

    Ok(())
}
