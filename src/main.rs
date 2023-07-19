#![allow(dead_code, unused_imports)] // TEMPORARY

use std::path::PathBuf;

use anyhow::anyhow;
use clap::Parser as ClapParser;
use fs_err as fs;
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use tracing::{debug, error, info, trace};
use pretty::*;

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
const NUMBER_OF_COLUMNS: usize = 120;
const INDENT_SPACES: isize = 4;

// When in doubt, we should generally try to stick to Rust style guidelines:
//   https://doc.rust-lang.org/beta/style-guide/expressions.html

fn expr_to_doc<'a>(expr: Pair<'a, Rule>, arena:&'a Arena<'a,()>) -> DocBuilder<'a,Arena<'a>> {
    arena.text(expr.as_str())
}

fn item_to_doc<'a>(item: Pair<'a, Rule>, arena:&'a Arena<'a,()>) -> RefDoc<'a,()> {
    let item = item.into_inner().next().unwrap();  // Grab the specific case of item
    let doc_builder = match item.as_rule() {
        Rule::r#const => {
            let d = item.into_inner().fold(arena.nil(), |doc, elt| {
                // Too many lifetime problems with this version
                //let default = |d:DocBuilder<'a, Arena>, e:Pair<'a, Rule>| d.append(arena.text(e.as_str()).append(arena.space()));
                let docs = match elt.as_rule() {
                    Rule::attr => vec![arena.text(elt.as_str()), arena.hardline()],
//                    Rule::visibility => default(doc, elt),
//                    Rule::default => default(doc, elt),
//                    Rule::name => default(doc, elt),
                    Rule::visibility => vec![arena.text(elt.as_str()), arena.space()],
                    Rule::default => vec![arena.text(elt.as_str()), arena.space()],
                    Rule::name => vec![arena.text(elt.as_str())],
                    Rule::r#type => vec![arena.text(":"),
                                     arena.softline().append(arena.text(elt.as_str().trim())).nest(INDENT_SPACES)],
                        // REVIEW: The type ends up with an space after it when it becomes a path_segment
                        // For now, I'm calling trim to remove it, but perhaps it should be fixed
                        // in the grammar?
//                        { 
//                            println!("##{:?}##", elt); 
//                            println!("##{}##", elt.as_str()); 
//                            doc.append(arena.text(": ".to_owned() + elt.as_str() + ">>"))
//                        },
                    Rule::expr => vec![arena.space(),
                                   arena.text("="),
                                   // Need to use this version to get actual nesting.  The next two
                                   // lines don't work
                                   arena.softline().append(expr_to_doc(elt, arena)).nest(INDENT_SPACES)],
//                                   arena.softline(),
//                                   expr_to_doc(elt, arena).nest(INDENT_SPACES)],
                    _ => unreachable!(),
                };
                doc.append(arena.concat(docs))
            });
            d.append(arena.text(";"))
        },
        _ => {
            error!("TODO: format {:?} before returning", item.as_rule());
            arena.text(item.as_str().to_owned())
        }
    };
    doc_builder.into_doc()
}


fn format_item(item: Pair<Rule>) -> String {
    let mut w = Vec::new();
    let arena = Arena::<()>::new();
    item_to_doc(item, &arena).render(NUMBER_OF_COLUMNS, &mut w).unwrap();
    String::from_utf8(w).unwrap()
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
