use std::{
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use rootcause::prelude::*;

/// Where the LLVM tools live.
#[derive(clap::Args)]
pub struct Llvm {
    /// LLVM `bin` directory, e.g. `/usr/lib/llvm-18/bin` (default: `PATH`).
    #[arg(long = "llvm-bin", env = "LLVM_BIN", global = true)]
    bin: Option<PathBuf>,
}

impl Llvm {
    /// The path of tool `name`.
    pub fn tool(&self, name: &str) -> PathBuf {
        self.bin
            .as_ref()
            .map_or_else(|| name.into(), |dir| dir.join(name))
    }

    /// A command running tool `name`.
    pub fn command(&self, name: &str) -> Command {
        Command::new(self.tool(name))
    }
}

/// The canonical path of `program`, looked up in `PATH` or relative to `dir`.
pub fn resolve(program: impl AsRef<OsStr>, dir: &Path) -> Result<PathBuf, Report> {
    let program = program.as_ref();
    let path = which::which_in(program, env::var_os("PATH"), dir)
        .context("Could not find program")
        .attach(format!("Program: {}", program.display()))?;
    Ok(fs::canonicalize(&path)
        .context("Could not canonicalize program path")
        .attach(format!("Path: {}", path.display()))?)
}

/// Runs `command`, failing with its stderr on a nonzero exit.
pub fn run(command: &mut Command) -> Result<Output, Report> {
    let output = command
        .output()
        .context("Could not spawn command")
        .attach(format!("Command: {command:?}"))?;
    if !output.status.success() {
        return Err(report!("Command failed")
            .attach(format!("Command: {command:?}"))
            .attach(format!("Status: {}", output.status))
            .attach(String::from_utf8_lossy(&output.stderr).into_owned()));
    }
    Ok(output)
}
