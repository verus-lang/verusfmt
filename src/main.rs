use std::path::PathBuf;

use clap::{Parser as ClapParser, ValueEnum};
use fs_err as fs;
use miette::{miette, IntoDiagnostic};
use tracing::{error, info}; // debug, trace, warn
use verusfmt::RustFmtConfig;

/// A collection of options that should not be relied upon existing long-term, added primarily for
/// verusfmt developers to use.
#[derive(Clone, ValueEnum)]
enum UnstableCommand {
    /// Run idempotency test. Exits with 0 only if an idempotency issue is found.
    IdempotencyTest,
}

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
    /// Use unstable CLI features
    #[arg(short = 'Z', long = "unstable")]
    unstable_command: Option<UnstableCommand>,
    /// Update verusfmt if an update is available
    #[arg(long = "update")]
    update: bool,
}

fn format_file(file: &PathBuf, args: &Args) -> miette::Result<()> {
    let unparsed_file = fs::read_to_string(file).into_diagnostic()?;

    let rustfmt_config = {
        // Repeatedly check for ancestors of `file` until we find either `rustfmt.toml` or
        // `.rustfmt.toml`; if we do, that becomes `rustfmt_toml`
        let rustfmt_toml = file
            .canonicalize()
            .unwrap()
            .ancestors()
            .flat_map(|dir| {
                // Why in this particular order? That's the order in which rustfmt checks:
                // https://github.com/rust-lang/rustfmt/blob/202fa22cee5badff77129a7bea5c90228d354ac9/src/config/mod.rs#L368-L369
                [".rustfmt.toml", "rustfmt.toml"]
                    .into_iter()
                    .map(|n| dir.join(n))
            })
            .filter_map(|p| p.exists().then(|| fs::read_to_string(p).unwrap()))
            .next();

        RustFmtConfig { rustfmt_toml }
    };

    let formatted_output = verusfmt::run(
        &unparsed_file,
        verusfmt::RunOptions {
            file_name: Some(file.to_string_lossy().into()),
            run_rustfmt: !args.verus_only,
            rustfmt_config: rustfmt_config.clone(),
        },
    )?;

    if args.check {
        if unparsed_file == formatted_output {
            info!("✨Perfectly formatted✨");
            Ok(())
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
            Err(miette!("invalid formatting"))
        }
    } else if matches!(
        args.unstable_command,
        Some(UnstableCommand::IdempotencyTest)
    ) {
        let reformatted = verusfmt::run(
            &formatted_output,
            verusfmt::RunOptions {
                file_name: Some(file.to_string_lossy().into()),
                run_rustfmt: !args.verus_only,
                rustfmt_config,
            },
        )?;
        if formatted_output == reformatted {
            return Err(miette!("✨Idempotent run✨"));
        } else {
            info!("Non-idempotency found in {}", file.display());
            error!("😱Formatting found to not be idempotent😱");
            let diff = similar::udiff::unified_diff(
                similar::Algorithm::Patience,
                &formatted_output,
                &reformatted,
                3,
                Some((
                    &format!("{}.formatted-once", file.to_string_lossy()),
                    &format!("{}.formatted-twice", file.to_string_lossy()),
                )),
            );
            println!("{diff}");
            return Ok(());
        }
    } else {
        let formatted_file_name = format!(
            "{}_formatted.rs",
            file.file_stem().unwrap().to_string_lossy()
        );
        let formatted_file_path = file.with_file_name(formatted_file_name);
        fs::write(formatted_file_path, formatted_output).into_diagnostic()?;

        Ok(())
    }
}

fn main() -> miette::Result<()> {
    let args = Args::parse();

    tracing_subscriber::fmt()
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .with_level(true)
        .with_target(false)
        .with_max_level(match args.debug_level + (args.update as u8) {
            0 => tracing::Level::WARN,
            1 => tracing::Level::INFO,
            2 => tracing::Level::DEBUG,
            _ => tracing::Level::TRACE,
        })
        .init();

    if args.update {
        info!("Attempting update");
        let mut updater = axoupdater::AxoUpdater::new_for("verusfmt");
        if let Err(e) = updater.load_receipt() {
            error!("Failed to load receipt.");
            return Err(e).into_diagnostic();
        }
        if !updater
            .check_receipt_is_for_this_executable()
            .into_diagnostic()?
        {
            error!("This verusfmt installation does not support updating.");
            info!("Consider updating using the approach you initially installed it with.");
            return Err(miette!("Incorrect receipt for executable"));
        }
        if updater.run_sync().into_diagnostic()?.is_some() {
            info!("Update installed!");
        } else {
            info!("Already up to date");
        }
        return Ok(());
    }

    if args.files.is_empty() {
        return Err(miette!("No files specified"));
    }

    let mut errors = vec![];
    for file in &args.files {
        match format_file(file, &args) {
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
