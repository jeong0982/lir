use std::ffi::OsStr;
use std::{
    fs::File,
    io::{stdout, Write},
    path::Path,
};

use clap::Parser;

use lang_c::ast::TranslationUnit;

use lir::{frontutils::Translate, ir, ok_or_exit, Parse};

#[derive(Debug, Parser)]
#[clap(name = "lir")]
struct LirCli {
    #[clap(short, long)]
    parse: bool,

    #[clap(short, long)]
    irgen: bool,

    #[clap(short, long, value_name = "FILE")]
    output: Option<String>,

    input: String,
}

fn main() {
    let matches = LirCli::parse();
    let input = Path::new(&matches.input);

    let output = matches.output.clone().unwrap_or_else(|| "-".to_string());

    let mut output: Box<dyn Write> = if output == "-" {
        Box::new(stdout())
    } else {
        Box::new(ok_or_exit!(File::create(output), 1))
    };

    let ext = input.extension();
    if ext == Some(OsStr::new("c")) {
        let input = ok_or_exit!(Parse::default().translate(&input), 1);
        compile_c(&input, &mut output, &matches);
    }
}

fn compile_c(input: &TranslationUnit, output: &mut Box<dyn Write>, matches: &LirCli) {
    if matches.parse {
        return;
    }

    let mut ir = match Irgen::default().translate(input) {
        Ok(ir) => ir,
        Err(irgen_error) => {
            println!("{irgen_error}");
            return;
        }
    };

    if matches.irgen {
        write(&ir, output).unwrap();
        return;
    }

    compile_ir(&mut ir, output, matches)
}

fn compile_ir(input: &mut ir::TranslationUnit, output: &mut dyn Write, matches: &LirCli) {}
