use std::{
    io::{self, Read, Write},
    path::PathBuf,
};

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
    /// Run in 'check' mode. Exits with 0 only if the input is formatted correctly.
    #[arg(long = "check")]
    check: bool,
    /// Input files to be formatted; reads from stdin when omitted
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
    /// Rust edition for parts outside the Verus macro
    #[arg(long, default_value = "2021", conflicts_with = "verus_only")]
    edition: String,
    /// Update verusfmt if an update is available
    #[arg(long = "update")]
    update: bool,
}

fn process_source(
    unparsed_file: &str,
    source_name: &str,
    rustfmt_config: RustFmtConfig,
    args: &Args,
) -> miette::Result<Option<String>> {
    let formatted_output = verusfmt::run(
        unparsed_file,
        verusfmt::RunOptions {
            file_name: Some(source_name.to_owned()),
            run_rustfmt: !args.verus_only,
            rustfmt_config: rustfmt_config.clone(),
        },
    )?;

    if args.check {
        if unparsed_file == formatted_output {
            info!("✨Perfectly formatted✨");
            Ok(None)
        } else {
            info!("Found some differences in {source_name}");
            error!("Input found not to be well formatted");
            let formatted_name = format!("{source_name}.formatted");
            let diff = similar::udiff::unified_diff(
                similar::Algorithm::Patience,
                unparsed_file,
                &formatted_output,
                3,
                Some((source_name, &formatted_name)),
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
                file_name: Some(source_name.to_owned()),
                run_rustfmt: !args.verus_only,
                rustfmt_config,
            },
        )?;
        if formatted_output == reformatted {
            return Err(miette!("✨Idempotent run✨"));
        } else {
            info!("Non-idempotency found in {source_name}");
            error!("😱Formatting found to not be idempotent😱");
            let formatted_once_name = format!("{source_name}.formatted-once");
            let formatted_twice_name = format!("{source_name}.formatted-twice");
            let diff = similar::udiff::unified_diff(
                similar::Algorithm::Patience,
                &formatted_output,
                &reformatted,
                3,
                Some((&formatted_once_name, &formatted_twice_name)),
            );
            println!("{diff}");
            return Ok(None);
        }
    } else {
        Ok(Some(formatted_output))
    }
}

fn format_file(file: &PathBuf, args: &Args) -> miette::Result<()> {
    let unparsed_file = fs::read_to_string(file).into_diagnostic()?;

    // Repeatedly check for ancestors of `file` until we find either `rustfmt.toml` or
    // `.rustfmt.toml`; if we do, that becomes `rustfmt_toml`.
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

    let source_name = file.to_string_lossy();
    if let Some(formatted_output) = process_source(
        &unparsed_file,
        &source_name,
        RustFmtConfig {
            rustfmt_toml,
            edition: args.edition.clone(),
        },
        args,
    )? {
        fs::write(file, formatted_output).into_diagnostic()?;
    }
    Ok(())
}

fn format_stdin(args: &Args) -> miette::Result<()> {
    let mut unparsed_file = String::new();
    io::stdin()
        .read_to_string(&mut unparsed_file)
        .into_diagnostic()?;

    if let Some(formatted_output) = process_source(
        &unparsed_file,
        "<stdin>",
        RustFmtConfig {
            rustfmt_toml: None,
            edition: args.edition.clone(),
        },
        args,
    )? {
        io::stdout()
            .lock()
            .write_all(formatted_output.as_bytes())
            .into_diagnostic()?;
    }
    Ok(())
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
        #[cfg(feature = "axoupdater")]
        {
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
        #[cfg(not(feature = "axoupdater"))]
        return Err(miette!(
            "Auto-updater not enabled in this build, re-compile with feature \
             `axoupdater` enabled."
        ));
    }

    if args.files.is_empty() {
        return format_stdin(&args);
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
