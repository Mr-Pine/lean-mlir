use std::{fs, path::Path, process::ExitCode};

use clap::{Parser, Subcommand};
use rootcause::prelude::*;
use serde::de::DeserializeOwned;

mod compile;
mod import;
mod llvm;
mod translate;

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    #[command(flatten)]
    llvm: llvm::Llvm,
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Compile the sources of a compilation database to LLVM IR.
    Compile(compile::Args),
    /// Translate LLVM IR to MLIR.
    Translate(translate::Args),
    /// Import translated MLIR into a Lean project.
    Import(import::Args),
}

fn read_json<T: DeserializeOwned>(path: &Path) -> Result<T, Report> {
    let contents =
        fs::read_to_string(path).context_with(|| format!("reading {}", path.display()))?;
    Ok(serde_json::from_str(&contents).context_with(|| format!("parsing {}", path.display()))?)
}

fn run() -> Result<(), Report> {
    let cli = Cli::parse();
    match cli.command {
        Command::Compile(args) => compile::run(args, &cli.llvm),
        Command::Translate(args) => translate::run(args, &cli.llvm),
        Command::Import(args) => import::run(args),
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(report) => {
            eprintln!("{report}");
            ExitCode::FAILURE
        }
    }
}
