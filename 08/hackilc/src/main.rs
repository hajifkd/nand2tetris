use anyhow::{anyhow, Context, Result};
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

    let mut src: Vec<_> = if std::path::Path::new(&args[1]).is_dir() {
        let children = std::fs::read_dir(&args[1])
            .with_context(|| format!("Failed to open directory {}", &args[1]))?
            .filter_map(|e| e.ok().map(|d| d.path()))
            .filter(|p| p.extension().map(|e| e == "vm").unwrap_or(false))
            .collect::<Vec<_>>();

        if children.len() == 0 {
            return Err(anyhow!(
                "Directory {} does not contain any vm file",
                &args[1]
            ));
        }

        children
    } else {
        vec![(&args[1]).into()]
    };
    let dst = File::create(&args[2]).with_context(|| format!("Failed to create {}", &args[2]))?;
    let mut dst = BufWriter::new(dst);

    let curr_file = src.pop().unwrap();
    let mut mod_name = curr_file
        .file_stem()
        .ok_or(anyhow!("Invalid file name {}", curr_file.display()))?
        .to_string_lossy()
        .into_owned();
    let mut parser = Parser::new(BufReader::new(File::open(&curr_file)?));
    loop {
        let line = parser.advance().context("Failed to parse")?;
        if line.is_none() {
            if let Some(new_file) = src.pop() {
                mod_name = new_file
                    .file_stem()
                    .ok_or_else(|| anyhow!("Invalid file name {}", new_file.display()))?
                    .to_string_lossy()
                    .into_owned();
                parser.load(BufReader::new(File::open(&new_file)?))?;
                continue;
            } else {
                break;
            }
        }
        let cmd = line.unwrap();
        let asms = cmd.generate(&mod_name);
        for asm in asms.into_iter() {
            writeln!(&mut dst, "{}", asm)
                .with_context(|| format!("Failed to write {}", &args[2]))?;
        }
    }

    Ok(())
}
