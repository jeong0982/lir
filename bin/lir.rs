use clap::Parser;

use lang_c::ast::TranslationUnit;
use std::ffi::OsStr;
use std::{
    fs::File,
    io::{stdout, Write},
    path::Path,
};

use lir::{
    ir, ok_or_exit, write, Deadcode, Gvn, Irgen, Mem2reg, Optimize, Parse, SimplifyCfg, Translate,
    O1,
};

#[derive(Debug, Parser)]
#[clap(name = "lir")]
struct LirCli {
    /// Parse C code
    #[clap(long)]
    parse: bool,

    /// Prints the input AST
    #[clap(short, long)]
    print: bool,

    /// Generates IR
    #[clap(short, long)]
    irgen: bool,

    /// Prints the input IR AST
    #[clap(long)]
    irprint: bool,

    /// Optimizes IR
    #[clap(short = 'O', long)]
    optimize: bool,

    /// Performs simplify-cfg
    #[clap(long = "simplify-cfg")]
    simplify_cfg: bool,

    /// Performs mem2reg
    #[clap(long)]
    mem2reg: bool,

    /// Performs deadcode elimination
    #[clap(long)]
    deadcode: bool,

    /// Performs gvn
    #[clap(long)]
    gvn: bool,

    /// Prints the output IR
    #[clap(long)]
    iroutput: bool,

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

    if matches.print {
        write(input, output).unwrap();
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

fn compile_ir(input: &mut ir::TranslationUnit, output: &mut dyn Write, matches: &LirCli) {
    if matches.irprint {
        write(input, output).unwrap();
        return;
    }

    if matches.optimize {
        O1::default().optimize(input);
    } else {
        if matches.simplify_cfg {
            SimplifyCfg::default().optimize(input);
        }

        if matches.mem2reg {
            Mem2reg::default().optimize(input);
        }

        if matches.deadcode {
            Deadcode::default().optimize(input);
        }

        if matches.gvn {
            Gvn::default().optimize(input);
        }
    }

    if matches.iroutput {
        write(input, output).unwrap();
        return;
    }
}
