//! Utilities to run rustfmt in such a way that it doesn't interfere with the formatting verusfmt
//! has done.

use std::io::Write;
use std::process::{Command, Stdio};

use pest::{iterators::Pair, iterators::Pairs, Parser};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "verus-minimal.pest"]
pub struct MinimalVerusParser;

fn is_multiline_comment(pair: &Pair<Rule>) -> bool {
    matches!(&pair.as_span().as_str()[..2], "/*")
}

/// Run rustfmt, only on code outside the `verus!` macro
pub fn rustfmt(s: &str) -> Option<String> {
    let parsed_file = MinimalVerusParser::parse(Rule::file, s)
        .expect("Minimal parsing should never fail. If it did, please report this as an error.")
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();

    let mut folded_verus_macro_invocations = vec![];
    let mut collapsed_input = String::new();

    for pair in parsed_file {
        let rule = pair.as_rule();
        match rule {
            Rule::EOI => {
                // End of input, do nothing
            }
            Rule::WHITESPACE => {
                unreachable!("All whitespace should be auto-eaten")
            }
            Rule::non_verus | Rule::COMMENT => {
                collapsed_input += pair.as_str();
                if rule == Rule::COMMENT && is_multiline_comment(&pair) {
                    collapsed_input += "\n";
                }
            }
            Rule::verus_macro_use => {
                folded_verus_macro_invocations.push(pair.as_str().trim());
                collapsed_input += "verus!{}\n";
            }
            _ => {
                unreachable!("Unexpected rule: {:?}", rule)
            }
        }
    }

    let formatted = run_rustfmt(&collapsed_input)?;

    let parsed_file = MinimalVerusParser::parse(Rule::file, &formatted)
        .expect("Minimal parsing should never fail. If it did, please report this as an error.")
        .next()
        .expect("There will be exactly one `file` rule matched in a valid parsed file")
        .into_inner();

    let mut folded_verus_macro_invocations = folded_verus_macro_invocations.into_iter();
    let mut final_output = String::new();

    let mut immediately_after_verus_macro = false;
    for pair in parsed_file {
        let rule = pair.as_rule();
        match rule {
            Rule::EOI => {
                // End of input, do nothing
            }
            Rule::WHITESPACE => {
                unreachable!("All whitespace should be auto-eaten")
            }
            Rule::non_verus | Rule::COMMENT => {
                if immediately_after_verus_macro {
                    if pair.as_str().trim_start().starts_with('}') && final_output.ends_with("    ")
                    {
                        // dedent once
                        for _ in 0..4 {
                            final_output.pop();
                        }
                    }
                    immediately_after_verus_macro = false;
                }
                final_output += pair.as_str();
                if rule == Rule::COMMENT && is_multiline_comment(&pair) {
                    final_output += "\n";
                }
            }
            Rule::verus_macro_use => {
                let trailing_line = final_output
                    .rfind('\n')
                    .map(|i| &final_output[i + 1..])
                    .unwrap_or("")
                    .to_string();
                let trailing_whitespace = if trailing_line.chars().all(char::is_whitespace) {
                    trailing_line
                } else {
                    String::new()
                };
                final_output += folded_verus_macro_invocations.next().unwrap();
                final_output += "\n";
                final_output += &trailing_whitespace;
                immediately_after_verus_macro = true;
            }
            _ => {
                unreachable!("Unexpected rule: {:?}", rule)
            }
        }
    }

    // Sanity check that we haven't dropped Verus code anywhere
    assert_eq!(folded_verus_macro_invocations.next(), None);

    Some(final_output)
}

fn run_rustfmt(s: &str) -> Option<String> {
    let mut proc = Command::new("rustfmt")
        .arg("--emit=stdout")
        .arg("--edition=2021")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .ok()?;

    proc.stdin
        .as_mut()
        .unwrap()
        .write_all(s.as_bytes())
        .unwrap();

    let output = proc.wait_with_output().ok()?;
    if output.status.success() {
        Some(String::from_utf8(output.stdout).unwrap())
    } else {
        eprintln!(
            "\nrustfmt failed! {}\n\tConsider running with --verus-only\n",
            String::from_utf8(output.stderr).unwrap()
        );
        None
    }
}
