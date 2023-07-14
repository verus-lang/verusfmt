#![allow(dead_code, unused_imports)] // TEMPORARY

use std::path::PathBuf;

use anyhow::anyhow;
use clap::Parser as ClapParser;
use fs_err as fs;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use tracing::{debug, error, info, trace};

#[derive(Parser)]
#[grammar = "verus.pest"]
pub struct VerusParser;

/// An opinionated formatter for Verus code
///
/// Formats code that is inside the `verus!{}` macro. Best utilized in conjunction with rustfmt
/// which will format everything outside the verus macro.
#[derive(ClapParser)]
#[command(version, about)]
struct Args {
    /// Run in 'check' mode. Exits with 0 only if the file is formatted correctly.
    #[arg(long = "check")]
    check: bool,
    /// Input file to be formatted
    file: PathBuf,
    /// Print debugging output (can be repeated for more detail)
    #[arg(short = 'd', long = "debug", action = clap::ArgAction::Count)]
    debug_level: u8,
}

// XXX: Should we expose this to the user as a configurable option where we pick a default? I think
// even this should be opinionated, but might be useful to expose this as an unstable option or
// something.
const NUMBER_OF_COLUMNS: u32 = 120;

fn format_item(item: Pair<Rule>) -> String {
    error!("TODO: format before returning");
    item.as_str().to_owned()
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    tracing_subscriber::fmt()
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .with_level(true)
        .with_target(false)
        .with_max_level(match args.debug_level {
            0 => tracing::Level::WARN,
            1 => tracing::Level::INFO,
            2 => tracing::Level::DEBUG,
            _ => tracing::Level::TRACE,
        })
        .init();

    let unparsed_file = fs::read_to_string(&args.file)?;
    let parsed_file = VerusParser::parse(Rule::file, &unparsed_file)?
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();

    info!(file = %args.file.display(), "Parsed");
    trace!(parsed = %parsed_file, "Parsed file");

    let mut formatted_output = String::new();

    for pair in parsed_file {
        let rule = pair.as_rule();
        debug!(?rule, "Processing top-level");
        match rule {
            Rule::non_verus | Rule::COMMENT => {
                formatted_output += pair.as_str();
            }
            Rule::verus_macro_use => {
                let body = pair.into_inner().collect::<Vec<_>>();
                assert_eq!(body.len(), 1);
                let body = body.into_iter().next().unwrap();
                formatted_output += "verus! {\n\n";
                for item in body.into_inner() {
                    if item.as_rule() == Rule::COMMENT {
                        formatted_output += item.as_str();
                    } else {
                        formatted_output += &format_item(item);
                        formatted_output += "\n\n";
                    }
                }
                formatted_output += "} // verus!\n";
            }
            Rule::EOI => {
                // end of input; do nothing
            }
            _ => unreachable!("Unexpected rule: {:?}", rule),
        }
    }

    if args.check {
        if unparsed_file == formatted_output {
            info!("✨Perfectly formatted✨");
            return Ok(());
        } else {
            info!("Found some differences");
            error!("Input found not to be well formatted");
            let diff = similar::udiff::unified_diff(
                similar::Algorithm::Patience,
                &unparsed_file,
                &formatted_output,
                3,
                Some(("original", "formatted")),
            );
            println!("{diff}");
            return Err(anyhow!("invalid formatting"));
        }
    } else {
        fs::write(args.file, formatted_output)?;
        Ok(())
    }
}
