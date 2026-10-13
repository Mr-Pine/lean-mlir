use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap, HashSet, VecDeque},
    fs::{self, File},
    path::{Path, PathBuf},
    rc::Rc,
};

use melior::{
    Context,
    dialect::DialectRegistry,
    ir::{
        BlockLike, Module, OperationRef, RegionLike,
        attribute::StringAttribute,
        operation::{OperationLike, OperationPrintingFlags},
    },
    utility::register_all_dialects,
};
use regex::Regex;
use rootcause::{option_ext::OptionExt, prelude::*};
use serde::Deserialize;

use crate::read_json;

#[derive(clap::Args)]
pub struct Args {
    /// The `.mlir` file from `translate`.
    input: PathBuf,
    /// Root of the Lean project.
    root: PathBuf,
    /// Default target path, relative to `root`.
    target: PathBuf,
    /// Default target module, e.g. `Firedancer.Ref.Mlir`.
    target_module: String,
    /// The `func_mappings.json` file (default: no mappings).
    func_mappings: Option<PathBuf>,
    /// Root functions to import (repeatable).
    #[arg(long = "root-func")]
    root_funcs: Vec<String>,
}

/// Mapping: function name regex -> alternative subpath and module.
#[derive(Debug, Default, Deserialize)]
struct FuncMappings {
    /// Symbol regex, target path, target module; first match wins.
    functions: Vec<(String, PathBuf, String)>,
}

pub fn run(args: Args) -> Result<(), Report> {
    let mappings: FuncMappings = {
        let mut mappings = match &args.func_mappings {
            Some(path) => read_json(path)?,
            None => FuncMappings::default(),
        };
        mappings
            .functions
            .push((".*".to_string(), args.target, args.target_module));
        mappings
    };
    let context = context();
    let module = load(&context, &args.input)?;

    let mut operations = HashMap::new();
    let mut op: Option<OperationRef<'_, '_>> = module.body().first_operation();
    while let Some(o) = op {
        if let Some(name) = function_name(o)?.or(const_global_name(o)?) {
            operations.insert(name, o);
        }
        op = o.next_in_block();
    }
    let reachable = find_reachable(&operations, args.root_funcs)
        .context("Could not collect reachable operations")?;

    let paths = {
        let names = reachable.iter().map(|elem| &elem.name);
        let mappings = mappings
            .functions
            .iter()
            .map(|(reg, target, module)| -> Result<_, Report> {
                Ok((Regex::new(&format!("^{reg}$"))?, target, module))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut paths = HashMap::new();
        for name in names {
            let (_, target, module) = mappings
                .iter()
                .find(|(reg, _, _)| reg.is_match(name))
                .context("Did not find matching path")
                .attach(format!("Name: {}", name))?;
            paths.insert(name.clone(), ((*target).clone(), (*module).clone()));
        }
        paths
    };

    let files_with_content = reachable
        .into_iter()
        .map(|entry| build_file_content(entry, &paths).context("Could not build file content"))
        .collect::<Result<Vec<_>, _>>()
        .context("Could not build files")?;

    for (content, path) in files_with_content {
        let path = args.root.join(path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&path, content)
            .context("Could not write file")
            .attach(format!("Path: {}", path.display()))?;
    }

    Ok(())
}

fn build_file_content(
    entry: ReachableEntry,
    paths: &HashMap<String, (PathBuf, String)>,
) -> Result<(String, PathBuf), Report> {
    let dependency_bindings = entry
        .references
        .iter()
        .map(|reference| {
            let (_, module) = &paths[reference];
            format!("      @{reference} := {module}.{reference}")
        })
        .collect::<Vec<_>>()
        .join(",\n");
    let dependency_paths = entry
        .references
        .iter()
        .map(|reference| {
            let (path, _) = &paths[reference];
            path.to_str()
                .context("Could not convert path to string")
                .map(|str| format!("public import {}.{reference}", str.replace("/", ".")))
        })
        .collect::<Result<Vec<_>, _>>()?
        .join("\n");
    let name = entry.name;
    let (path, module) = paths[&name].clone();
    let body = entry
        .op
        .to_string_with_flags(OperationPrintingFlags::new().print_generic_operation_form().use_local_scope())
        .context("Could not print operation")?;

    let op_name = entry.op.name();
    let (semantics_import, def_keyword) = match op_name.as_string_ref().as_str()? {
        "llvm.func" => ("MLIR.Semantics.Func", "mlir_def"),
        "llvm.mlir.global" => ("MLIR.Semantics.GlobalInitializer", "mlir_const_def"),
        other => Err(report!("Unexpected top-level operation").attach(format!("Op: {other}")))?,
    };

    let content = format!(
        r#"
module

public import {semantics_import}
public import MLIR.Syntax.Elab

{dependency_paths}

namespace {module}

@[expose] public section

{def_keyword} {name} := {body}
    with
{dependency_bindings}

end

end {module}
"#
    );

    let path = path.join(format!("{name}.lean"));

    Ok((content, path))
}

#[derive(Clone)]
struct ReachableEntry<'a, 'b> {
    name: String,
    op: OperationRef<'a, 'b>,
    references: Vec<String>,
}

fn find_reachable<'a, 'b>(
    operations: &HashMap<String, OperationRef<'a, 'b>>,
    root_functions: Vec<String>,
) -> Result<Vec<ReachableEntry<'a, 'b>>, Report> {
    let mut reachable = Vec::default();

    let mut queued: HashSet<String> = Default::default();
    let mut todo: VecDeque<_> = Default::default();
    todo.extend(root_functions.clone().into_iter());
    queued.extend(root_functions.clone().into_iter());

    while let Some(elem_name) = todo.pop_front() {
        let elem = *operations
            .get(&elem_name)
            .context("Could not find element")
            .attach(format!("Name: {}", elem_name))?;
        let referenced = get_referenced(elem).context("Could not get referenced items")?;
        reachable.push(ReachableEntry {
            name: elem_name,
            op: elem,
            references: referenced.clone(),
        });
        todo.extend(referenced.clone().into_iter().filter_map(|name| {
            if queued.contains(&name) {
                None
            } else {
                Some(name)
            }
        }));
        queued.extend(referenced.into_iter())
    }

    Ok(reachable)
}

fn get_referenced<'a, 'b>(op: OperationRef<'a, 'b>) -> Result<Vec<String>, Report> {
    let mut referenced = Vec::new();
    get_referenced_inner(op, &mut referenced)?;
    Ok(referenced)
}

fn get_referenced_inner<'a, 'b>(
    op: OperationRef<'a, 'b>,
    collector: &mut Vec<String>,
) -> Result<(), Report> {
    let op_name = op.name();
    let op_name = op_name.as_string_ref().as_str()?;
    match op_name {
        "llvm.func" | "llvm.mlir.global" => {
            for region in op.regions() {
                let mut block = region.first_block();
                while let Some(blk) = block {
                    let mut operation = blk.first_operation();
                    while let Some(op) = operation {
                        get_referenced_inner(op, collector)?;
                        operation = op.next_in_block();
                    }
                    block = blk.next_in_region()
                }
            }
        }
        "llvm.call" => {
            let callee = op
                .attribute("callee")
                .context("Could not get callee of call")?;
            let callee_name = callee.to_string();
            let callee_name = callee_name
                .strip_prefix("@")
                .context("Calle did not start with '@'")?
                .to_string();
            collector.push(callee_name);
        }
        "llvm.mlir.addressof" => {
            let global = op
                .attribute("global_name")
                .context("Could not get global name")?;
            let global_name = global.to_string();
            let global_name = global_name
                .strip_prefix("@")
                .context("Global name did not start with '@'")?
                .to_string();
            collector.push(global_name);
        }
        _ => {},
    }

    Ok(())
}

fn function_name<'a, 'b>(o: OperationRef<'a, 'b>) -> Result<Option<String>, Report> {
    if o.name().as_string_ref().as_str()? == "llvm.func" {
        let name = StringAttribute::try_from(o.attribute("sym_name")?)?;
        Ok(Some(name.value().to_string()))
    } else {
        Ok(None)
    }
}

fn const_global_name<'a, 'b>(o: OperationRef<'a, 'b>) -> Result<Option<String>, Report> {
    if o.name().as_string_ref().as_str()? == "llvm.mlir.global" && o.has_attribute("constant") {
        let name = StringAttribute::try_from(o.attribute("sym_name")?)?;
        Ok(Some(name.value().to_string()))
    } else {
        Ok(None)
    }
}

/// A context with every dialect loaded.
fn context() -> Context {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    let context = Context::new();
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    context
}

/// Parses the module in `path`, failing with MLIR's diagnostics.
fn load<'c>(context: &'c Context, path: &Path) -> Result<Module<'c>, Report> {
    let source = fs::read_to_string(path)
        .context("Could not read input")
        .attach(format!("Path: {}", path.display()))?;

    let diagnostics = Rc::new(RefCell::new(Vec::new()));
    let handler = context.attach_diagnostic_handler({
        let diagnostics = diagnostics.clone();
        move |diagnostic| {
            diagnostics
                .borrow_mut()
                .push(format!("{}: {diagnostic}", diagnostic.location()));
            true
        }
    });
    let module = Module::parse(context, &source);
    context.detach_diagnostic_handler(handler);

    module.ok_or_else(|| {
        let mut report =
            report!("Could not parse input").attach(format!("Path: {}", path.display()));
        for diagnostic in diagnostics.take() {
            report = report.attach(diagnostic);
        }
        report.into_dynamic()
    })
}
