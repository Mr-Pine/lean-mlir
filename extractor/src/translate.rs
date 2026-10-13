use std::{
    fs,
    path::{Path, PathBuf},
};

use rootcause::{option_ext::OptionExt, prelude::*};

use crate::llvm::{self, Llvm};

#[derive(clap::Args)]
pub struct Args {
    /// The `.ll` file.
    input: PathBuf,
    /// Output directory.
    output: PathBuf,
}

pub fn run(args: Args, llvm: &Llvm) -> Result<(), Report> {
    let name = args
        .input
        .file_name()
        .context("Input has no file name")
        .attach(format!("Input: {}", args.input.display()))?;
    let output = args.output.join(name).with_extension("mlir");
    translate(llvm, &args.input, &output)
        .context("Could not translate")
        .attach(format!("Input: {}", args.input.display()))?;
    Ok(())
}

/// Imports `input` into MLIR and canonicalizes it into `output`.
fn translate(llvm: &Llvm, input: &Path, output: &Path) -> Result<(), Report> {
    let imported = tempfile::Builder::new()
        .suffix(".mlir")
        .tempfile()
        .context("Could not create temporary file")?;
    llvm::run(
        llvm.command("mlir-translate")
            .arg("--import-llvm")
            .arg(input)
            .arg("-o")
            .arg(imported.path()),
    )?;

    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)
            .context("Could not create output directory")
            .attach(format!("Path: {}", parent.display()))?;
    }
    llvm::run(
        llvm.command("mlir-opt")
            .arg("--canonicalize=region-simplify=disabled")
            .arg("--mlir-print-op-generic")
            .arg(imported.path())
            .arg("-o")
            .arg(output),
    )?;
    Ok(())
}
