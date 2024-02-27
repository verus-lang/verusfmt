//! Utilities to run rustfmt in such a way that it doesn't interfere with the formatting verusfmt
//! has done.

use std::io::Write;
use std::process::{Command, Stdio};

/// Run rustfmt, only on code outside the `verus!` macro
pub fn rustfmt(value: &str) -> Option<String> {
    if let Ok(mut proc) = Command::new("rustfmt")
        .arg("--emit=stdout")
        .arg("--edition=2021")
        .arg(r#"--config=skip_macro_invocations=["verus"]"#)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        {
            let stdin = proc.stdin.as_mut().unwrap();
            stdin.write_all(value.as_bytes()).unwrap();
        }
        if let Ok(output) = proc.wait_with_output() {
            if output.status.success() {
                return Some(String::from_utf8(output.stdout).unwrap().into());
            } else {
                eprintln!(
                    "\nrustfmt failed! {}\n\tConsider running with --verus-only\n",
                    String::from_utf8(output.stderr).unwrap()
                );
            }
        }
    }
    None
}
