use std::path::PathBuf;

use clap::Parser as ClapParser;
use fs_err as fs;
use miette::{miette, IntoDiagnostic, NamedSource};
use tracing::{error, info}; // debug, trace
use verusfmt::{parse_and_format, rustfmt};

/// An opinionated formatter for Verus code
///
/// Formats code both inside and outside the `verus!{}` macro (using rustfmt for code outside it).
/// Use `--verus-only` to restrict formatting to only be inside the macro.
#[derive(ClapParser)]
#[command(version, about)]
struct Args {
    /// Run in 'check' mode. Exits with 0 only if the file is formatted correctly.
    #[arg(long = "check")]
    check: bool,
    /// Input files to be formatted
    files: Vec<PathBuf>,
    /// Only format code inside the Verus macro
    #[arg(long = "verus-only")]
    verus_only: bool,
    /// Print debugging output (can be repeated for more detail)
    #[arg(short = 'd', long = "debug", action = clap::ArgAction::Count)]
    debug_level: u8,
}

fn format_file(file: &PathBuf, check: bool, verus_only: bool) -> miette::Result<()> {
    let unparsed_file = fs::read_to_string(file).into_diagnostic()?;

    let verus_fmted = parse_and_format(&unparsed_file).map_err(|e| {
        e.with_source_code(NamedSource::new(
            file.to_string_lossy(),
            unparsed_file.clone(),
        ))
    })?;

    let formatted_output = if verus_only {
        verus_fmted
    } else {
        rustfmt(&verus_fmted).ok_or(miette!("rustfmt failed"))?
    };

    if check {
        if unparsed_file == formatted_output {
            info!("✨Perfectly formatted✨");
            return Ok(());
        } else {
            info!("Found some differences in {}", file.display());
            error!("Input found not to be well formatted");
            let diff = similar::udiff::unified_diff(
                similar::Algorithm::Patience,
                &unparsed_file,
                &formatted_output,
                3,
                Some((
                    &file.to_string_lossy(),
                    &format!("{}.formatted", file.to_string_lossy()),
                )),
            );
            println!("{diff}");
            return Err(miette!("invalid formatting"));
        }
    } else {
        fs::write(file, formatted_output).into_diagnostic()?;
        Ok(())
    }
}

fn main() -> miette::Result<()> {
    let args = Args::parse();
    if args.files.len() == 0 {
        return Err(miette!("No files specified"));
    }

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

    let mut errors = vec![];
    for file in args.files {
        match format_file(&file, args.check, args.verus_only) {
            Ok(()) => {}
            Err(e) => {
                errors.push(e);
            }
        }
    }

    match errors.len() {
        0 => Ok(()),
        1 => Err(errors.pop().unwrap()),
        _ => Err(miette!("Multiple errors found: {errors:?}")),
    }
}
