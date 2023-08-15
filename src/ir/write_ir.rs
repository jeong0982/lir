use crate::ir::*;

use std::io::{Result, Write};

use crate::write_base::*;
use crate::*;

impl WriteLine for TranslationUnit {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        let mut counter: usize = 0;
        for (name, decl) in &self.decls {
            let _ = some_or!(decl.get_variable(), continue);

            match decl {
                Declaration::Variable { dtype, initializer } => {
                    writeln!(
                        write,
                        "var {} @{} = {}",
                        dtype,
                        name,
                        if let Some(init) = initializer {
                            init.write_string()
                        } else {
                            "default".to_string()
                        }
                    )?;
                }
                _ => panic!("Unreachable: write_ir"),
            }
        }

        for (name, decl) in &self.decls {
            let _ = some_or!(decl.get_function(), continue);
            writeln!(write)?;

            match decl {
                Declaration::Function {
                    signature,
                    definition,
                } => {
                    let params = signature.params.iter().format(", ");

                    if let Some(definition) = definition.as_ref() {
                        // print function definition
                        writeln!(write, "fun {} @{} ({}) {{", signature.ret, name, params)?;
                        // print meta data for function
                        writeln!(
                            write,
                            "init:\n  bid: {}\n  allocations: \n{}",
                            definition.bid_init,
                            definition.allocations.iter().format_with("\n", |a, f| {
                                let res = f(&format_args!(
                                    "    %{}:{}{}",
                                    counter,
                                    a.deref(),
                                    if let Some(name) = a.name() {
                                        format!(":{name}")
                                    } else {
                                        "".into()
                                    }
                                ));
                                counter += 1;
                                res
                            })
                        )?;

                        for (id, block) in &definition.blocks {
                            writeln!(write, "\nblock {id}:")?;
                            for phi in block.phinodes.iter() {
                                write_indent(indent + 1, write)?;
                                writeln!(
                                    write,
                                    "{}:{}{}",
                                    RegisterId::new(counter),
                                    phi.deref(),
                                    if let Some(name) = phi.name() {
                                        format!(":{name}")
                                    } else {
                                        "".into()
                                    }
                                )?;
                                counter += 1;
                            }

                            for instr in block.instructions.iter() {
                                write_indent(indent + 1, write)?;
                                writeln!(
                                    write,
                                    "{}:{}{} = {}",
                                    RegisterId::new(counter),
                                    instr.dtype(),
                                    if let Some(name) = instr.name() {
                                        format!(":{name}")
                                    } else {
                                        "".into()
                                    },
                                    instr
                                )?;
                                counter += 1;
                            }

                            write_indent(indent + 1, write)?;
                            writeln!(write, "{}", block.exit)?;
                        }

                        writeln!(write, "}}")?;
                    } else {
                        // print declaration line only
                        writeln!(write, "fun {} @{} ({})", signature.ret, name, params)?;
                        writeln!(write)?;
                    }
                }
                _ => panic!("Unreachable: write_ir"),
            }
        }

        Ok(())
    }
}

impl WriteString for Instruction {
    fn write_string(&self) -> String {
        format!("{self}")
    }
}

impl WriteString for Operand {
    fn write_string(&self) -> String {
        format!("{self}")
    }
}

impl WriteString for BlockExit {
    fn write_string(&self) -> String {
        format!("{self}")
    }
}
