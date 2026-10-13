use std::{
    fs,
    path::{Path, PathBuf},
};

use compile_commands::{CompilationDatabase, CompileArgs, CompileCommand, SourceFile::File};
use rootcause::{option_ext::OptionExt, prelude::*};

use crate::{
    llvm::{self, Llvm},
    read_json,
};

#[derive(clap::Args)]
pub struct Args {
    /// The `compile_commands.json` file.
    compile_commands: PathBuf,
    /// Output directory.
    output: PathBuf,
}

pub fn run(mut args: Args, llvm: &Llvm) -> Result<(), Report> {
    // Clang runs in each command's directory, so outputs must not be relative.
    args.output = std::path::absolute(&args.output)
        .context("Could not make output path absolute")
        .attach(format!("Path: {}", args.output.display()))?;
    let db: CompilationDatabase = read_json(&args.compile_commands)?;
    let commands = db
        .into_iter()
        .filter(|command| matches!(is_not_assembly(command), Ok(true)))
        .map(|mut cmd| -> Result<_, Report> {
            to_llvm_ir_command(&mut cmd, &args.output)
                .context("Could not convert command")
                .attach(format!("Cmd: {cmd:?}"))?;
            Ok(cmd)
        })
        .collect::<Result<CompilationDatabase, _>>()
        .context("Could not convert compilation database")?;

    let clang = llvm::resolve(llvm.tool("clang"), Path::new("."))?;
    for command in &commands {
        let Some(CompileArgs::Arguments(args)) = &command.arguments else {
            bail!("Could not support args");
        };

        fs::create_dir_all(
            command
                .output
                .as_ref()
                .context("Missing output file")?
                .parent()
                .context("Output file is missing parent")?,
        )
        .context("Could not create output dir")?;

        let (program, arguments) = args.split_first().context("Empty command")?;
        if llvm::resolve(program, &command.directory)? != clang {
            return Err(report!("Command does not use the selected clang")
                .attach(format!("Program: {program}"))
                .attach(format!("Clang: {}", clang.display())));
        }
        llvm::run(
            llvm.command("clang")
                .args(arguments)
                .current_dir(&command.directory),
        )
        .context("Could not compile")?;
    }

    llvm::run(
        llvm.command("llvm-link")
            .arg("-S")
            .args(
                commands
                    .iter()
                    .map(|cmd| cmd.output.as_ref().context("Could not get cmd output"))
                    .collect::<Result<Vec<_>, _>>()
                    .context("Could not get outputs")?,
            )
            .arg("-o")
            .arg(args.output.join("module.ll")),
    )
    .context("Could not link llvm ir")?;

    Ok(())
}

fn is_not_assembly(command: &CompileCommand) -> Result<bool, Report> {
    let File(file) = &command.file else {
        return Err(report!("Could not support file")).attach(format!("File: {:?}", command.file));
    };
    let ext = file
        .extension()
        .context("Could not get file extension")
        .attach(format!("File: {file:?}"))?;
    Ok(ext != "S")
}

fn to_llvm_ir_command(command: &mut CompileCommand, output: &Path) -> Result<(), Report> {
    let CompileArgs::Arguments(args) = command
        .arguments
        .as_mut()
        .context("Could not get compile command arguments")?
    else {
        return Err(report!("Could not support args"))
            .attach(format!("Args: {:?}", command.arguments));
    };

    if let Some(c_index) = args.iter().position(|arg| arg == "-c") {
        args.remove(c_index);
    };

    let output_path = {
        let o_index = args
            .iter()
            .position(|arg| arg == "-o")
            .context("Command does not have output path")?;
        let output_path = args.remove(o_index + 1); // Output dir
        args.remove(o_index); // -o flag
        PathBuf::from(output_path)
    };

    args.push("-S".to_string());
    args.push("-emit-llvm".to_string());
    args.push("-o".to_string());

    let new_output_path = {
        let existing_extension = output_path
            .extension()
            .context("Output path without extension")
            .attach(format!("Path: {}", output_path.display()))?;
        if existing_extension != "o" {
            return Err(
                report!("Non-object extension").attach(format!("Path: {}", output_path.display()))
            );
        }
        let relative_output = output_path.with_extension("ll");
        output.join(relative_output)
    };
    args.push(new_output_path.clone().into_string().map_err(|path| {
        report!("Could not convert path to string").attach(format!("Path: {}", path.display()))
    })?);
    command.output = Some(new_output_path);

    Ok(())
}
