use anyhow::{Context, Result};
use hackasm::{code, symbol_table, ASymbol, Command, Parser};
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};

fn main() -> Result<()> {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() != 3 {
        println!(
            "USAGE: {} <src.asm> <dst.hack>",
            if args.len() > 0 { &args[0] } else { "" }
        );

        return Ok(());
    }

    let src = File::open(&args[1]).with_context(|| format!("Failed to open {}", &args[1]))?;
    let src = BufReader::new(src);
    let dst = File::create(&args[2]).with_context(|| format!("Failed to create {}", &args[2]))?;
    let mut dst = BufWriter::new(dst);

    let mut table = symbol_table();
    let mut ops = vec![];
    let mut user_symbol = 15;

    // first pass
    let mut parser = Parser::new(src).context("Failed to parse")?;
    loop {
        let line = parser.advance().context("Failed to parse")?;
        if line.is_none() {
            break;
        }
        let line = line.unwrap();

        if let Command::LCommand(symbol) = line {
            table.insert(symbol, ops.len() as u16);
        } else {
            ops.push(line);
        }
    }

    // second pass
    for line in ops.into_iter() {
        let val = match line {
            Command::ACommand(symbol) => {
                let addr = match symbol {
                    ASymbol::Literal(n) => n,
                    ASymbol::Symbol(s) => {
                        if let Some(&n) = table.get(&s) {
                            n
                        } else {
                            user_symbol += 1;
                            table.insert(s, user_symbol);
                            user_symbol
                        }
                    }
                };

                addr & 0x7FFF
            }
            Command::CCommand { dest, comp, jump } => {
                let dest = code::dest(&dest)?;
                let comp = code::comp(&comp)?;
                let jump = code::jump(&jump)?;

                0xE000 | jump | (dest << 3) | (comp << 6)
            }
            _ => continue,
        };

        //dst.write_u16::<LittleEndian>(val)
        //    .with_context(|| format!("Failed to write {}", &args[2]))?;
        writeln!(&mut dst, "{:016b}", val)
            .with_context(|| format!("Failed to write {}", &args[2]))?;
    }

    Ok(())
}
