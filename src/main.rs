use anchor_lang_idl::{
    convert::convert_idl,
    types::{
        Idl, IdlArrayLen, IdlDefinedFields, IdlInstructionAccountItem, IdlPda, IdlSeed, IdlType,
        IdlTypeDefTy,
    },
};
use clap::Parser;
use std::fs;

#[derive(Parser)]
#[command(name = "idl-to-rocq")]
#[command(about = "Converts Anchor IDL JSON to Rocq code")]
struct Args {
    /// Path to the IDL JSON file
    idl_path: String,
    /// Optional output file (defaults to stdout)
    #[arg(short, long)]
    output: Option<String>,
    /// List of custom type names to order before others, comma-separated
    #[arg(long)]
    custom_type_order: Option<String>,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    // Read the IDL file
    let idl_content = fs::read(&args.idl_path)?;
    let idl = convert_idl(&idl_content)?;

    // Parse custom type order if provided
    let custom_type_order: Vec<String> = args
        .custom_type_order
        .as_ref()
        .map(|s| {
            s.split(',')
                .map(|name| name.trim().to_string())
                .filter(|name| !name.is_empty())
                .collect()
        })
        .unwrap_or_default();

    // Generate Rocq code
    let rocq_code = generate_rocq(&idl, &custom_type_order);

    // Output the result
    if let Some(output_path) = &args.output {
        fs::write(output_path, rocq_code)?;
    } else {
        print!("{}", rocq_code);
    }

    Ok(())
}

fn name_to_rocq(name: &str) -> String {
    let keywords = [
        "Type",
        "Set",
        "Inductive",
        "Record",
        "End",
        "Module",
        "Parameter",
        "match",
        "end",
        "with",
    ];

    if keywords.contains(&name) {
        return format!("{}_", name);
    }

    name.to_string()
}

fn generate_rocq(idl: &Idl, custom_type_order: &[String]) -> String {
    let mut output = String::new();

    // Header
    output.push_str("(* Generated file *)\n");
    output.push_str("From Excalead Require Import Excalead Anchor_lang.\n\n");

    // Constants
    if !idl.constants.is_empty() {
        output.push_str("(** Constants *)\n");
        for constant in &idl.constants {
            let rocq_type = idl_type_to_rocq(&constant.ty);
            output.push_str(&format!("(* {} *)\n", constant.value));
            output.push_str(&format!("Parameter {} : {}.\n\n", constant.name, rocq_type));
        }
    }

    // Error codes
    if !idl.errors.is_empty() {
        output.push_str("(** Error codes *)\n");
        output.push_str("Module ErrorCode.\n");
        output.push_str("  Inductive t : Set :=\n");
        for (i, error) in idl.errors.iter().enumerate() {
            let dot = if i == idl.errors.len() - 1 { "." } else { "" };
            if let Some(msg) = &error.msg {
                output.push_str(&format!("  (** {} *)\n", msg));
            }
            output.push_str(&format!("  | {} : t{}\n", error.name, dot));
        }
        output.push_str("End ErrorCode.\n\n");
    }

    // Custom types
    if !idl.types.is_empty() {
        output.push_str("(** Custom types *)\n");

        // Sort types according to custom_type_order
        let mut sorted_types = idl.types.clone();
        if !custom_type_order.is_empty() {
            sorted_types.sort_by(|a, b| {
                let a_index = custom_type_order.iter().position(|name| name == &a.name);
                let b_index = custom_type_order.iter().position(|name| name == &b.name);

                match (a_index, b_index) {
                    (Some(a_idx), Some(b_idx)) => a_idx.cmp(&b_idx),
                    (Some(_), None) => std::cmp::Ordering::Less,
                    (None, Some(_)) => std::cmp::Ordering::Greater,
                    (None, None) => std::cmp::Ordering::Equal,
                }
            });
        }

        for ty_def in &sorted_types {
            // Split the name at each `::` and make as many sub-modules
            for module_name in ty_def.name.split("::") {
                output.push_str(&format!("Module {}.\n", module_name));
            }

            match &ty_def.ty {
                IdlTypeDefTy::Struct { fields } => match fields {
                    Some(IdlDefinedFields::Named(fields_list)) => {
                        output.push_str("  Record t : Set := {\n");
                        for field in fields_list.iter() {
                            let rocq_type = idl_type_to_rocq(&field.ty);
                            output.push_str(&format!(
                                "    {} : {};\n",
                                name_to_rocq(&field.name),
                                rocq_type
                            ));
                        }
                        output.push_str("  }.\n");
                    }
                    Some(IdlDefinedFields::Tuple(tys)) => {
                        output.push_str("  Record t : Set := {\n");
                        for ty in tys.iter() {
                            let rocq_type = idl_type_to_rocq(ty);
                            output.push_str(&format!("    _ : {};\n", rocq_type));
                        }
                        output.push_str("  }.\n");
                    }
                    None => {
                        output.push_str("  Record t : Set := {\n");
                        output.push_str("  }.\n");
                    }
                },
                IdlTypeDefTy::Enum { variants } => {
                    output.push_str("  Inductive t : Set :=\n");
                    for (i, variant) in variants.iter().enumerate() {
                        let dot = if i == variants.len() - 1 { "." } else { "" };
                        output.push_str(&format!("  | {}", variant.name));
                        match &variant.fields {
                            Some(IdlDefinedFields::Named(fields_list)) => {
                                for field in fields_list.iter() {
                                    let rocq_type = idl_type_to_rocq(&field.ty);
                                    output.push_str(&format!(" ({} : {})", field.name, rocq_type));
                                }
                            }
                            Some(IdlDefinedFields::Tuple(tys)) => {
                                for ty in tys.iter() {
                                    let rocq_type = idl_type_to_rocq(ty);
                                    output.push_str(&format!(" (_ : {})", rocq_type));
                                }
                            }
                            None => {}
                        }
                        output.push_str(&format!("{}\n", dot));
                    }
                }
                IdlTypeDefTy::Type { .. } => {
                    output.push_str(&format!(
                        "Module {}.Definition t : Set := TODO.\n",
                        ty_def.name
                    ));
                    output.push_str(&format!("End {}.\n\n", ty_def.name));
                }
            }

            // Close all opened modules
            for module_name in ty_def.name.split("::").collect::<Vec<_>>().iter().rev() {
                output.push_str(&format!("End {}.\n", module_name));
            }
            output.push('\n');
        }
    }

    // Account structures
    if !idl.accounts.is_empty() {
        output.push_str("(** Account structures *)\n");
        output.push_str("Module AccountStructure.\n");
        output.push_str("  Inductive t : Set :=\n");
        for (i, account) in idl.accounts.iter().enumerate() {
            let dot = if i == idl.accounts.len() - 1 { "." } else { "" };
            output.push_str(&format!("  | {} : t{}\n", account.name, dot));
        }
        output.push_str("End AccountStructure.\n\n");
    }

    // Instruction contexts
    if !idl.instructions.is_empty() {
        output.push_str("(** Instruction contexts *)\n");
        output.push_str("Module Instruction.\n");
        output.push_str("  Inductive t : Set -> Set :=\n");
        for (i, instruction) in idl.instructions.iter().enumerate() {
            let dot = if i == idl.instructions.len() - 1 {
                "."
            } else {
                ""
            };
            output.push_str(&format!("  | {}\n", instruction.name));
            output.push_str("    (* Accounts *)\n");
            for account in &instruction.accounts {
                match account {
                    IdlInstructionAccountItem::Single(account) => {
                        output.push_str(&format!("      ({} : Account.t", account.name));
                        output.push_str("\n       ");
                        output.push_str(if account.writable {
                            " IsWritable.Yes"
                        } else {
                            " IsWritable.No"
                        });
                        output.push_str("\n       ");
                        output.push_str(if account.signer {
                            " IsSigner.Yes"
                        } else {
                            " IsSigner.No"
                        });
                        output.push_str("\n       ");
                        output.push_str(if account.optional {
                            " IsOptional.Yes"
                        } else {
                            " IsOptional.No"
                        });
                        output.push_str("\n       ");
                        match &account.address {
                            Some(address) => {
                                output.push_str(&format!(" (Address.Constant \"{}\")", address));
                            }
                            None => {
                                output.push_str(" Address.Any");
                            }
                        }
                        output.push_str("\n       ");
                        match &account.pda {
                            Some(pda) => {
                                output.push_str(&format!(" {}", pda_to_rocq(pda)));
                            }
                            None => {
                                output.push_str(" Pda.No");
                            }
                        }
                        output.push_str("\n      )\n");
                    }
                    IdlInstructionAccountItem::Composite(_) => {
                        output.push_str("      (* TODO: composite accounts *)\n");
                    }
                }
            }
            output.push_str("    (* Arguments *)\n");
            for arg in &instruction.args {
                let rocq_type_str = idl_type_to_rocq(&arg.ty);
                output.push_str(&format!("      ({} : {})\n", arg.name, rocq_type_str));
            }
            output.push_str("    (* Return *)\n");
            match &instruction.returns {
                Some(ret) => {
                    let rocq_type_str = idl_type_to_rocq(ret);
                    output.push_str(&format!("       : t {}", rocq_type_str));
                }
                None => {
                    output.push_str("      : t unit");
                }
            }
            output.push_str(&format!("{}\n", dot));
        }
        output.push_str("End Instruction.\n\n");
    }

    output
}

fn idl_type_to_rocq(ty: &IdlType) -> String {
    match ty {
        IdlType::Bool => "bool".to_string(),
        IdlType::U8 => "u8".to_string(),
        IdlType::U16 => "u16".to_string(),
        IdlType::U32 => "u32".to_string(),
        IdlType::U64 => "u64".to_string(),
        IdlType::U128 => "u128".to_string(),
        IdlType::I8 => "i8".to_string(),
        IdlType::I16 => "i16".to_string(),
        IdlType::I32 => "i32".to_string(),
        IdlType::I64 => "i64".to_string(),
        IdlType::I128 => "i128".to_string(),
        IdlType::F32 => "f32".to_string(),
        IdlType::F64 => "f64".to_string(),
        IdlType::Bytes => "bytes.t".to_string(),
        IdlType::String => "string".to_string(),
        IdlType::Pubkey => "Pubkey.t".to_string(),
        IdlType::Option(inner) => format!("option ({})", idl_type_to_rocq(inner)),
        IdlType::Vec(inner) => format!("list ({})", idl_type_to_rocq(inner)),
        IdlType::Array(inner, len) => match len {
            IdlArrayLen::Value(n) => {
                format!("list ({}) (* [{}; {}] *)", idl_type_to_rocq(inner), n, n)
            }
            IdlArrayLen::Generic(_) => format!(
                "list ({}) (* TODO: generic length array *)",
                idl_type_to_rocq(inner)
            ),
        },
        IdlType::Defined { name, .. } => {
            // Replace `::` by `.` in the name
            let name = name.replace("::", ".");
            format!("{name}.t")
        }
        IdlType::Generic(name) => name.clone(),
        // Handle newer types if needed
        IdlType::U256 => "u128 (* TODO: u256 *)".to_string(),
        IdlType::I256 => "i128 (* TODO: i256 *)".to_string(),
        _ => format!("TODO (* {:?})", ty),
    }
}

fn pda_to_rocq(pda: &IdlPda) -> String {
    let seeds = pda.seeds.iter().map(seed_to_rocq).collect::<Vec<_>>();
    let program = optional_to_rocq(pda.program.as_ref().map(seed_to_rocq), true, true);
    format!(
        "(Pda.Yes [\n            {}\n          ]\n          {}\n        )",
        seeds.join(";\n            "),
        program
    )
}

fn seed_to_rocq(seed: &IdlSeed) -> String {
    match seed {
        IdlSeed::Const(seed) => {
            let value = seed
                .value
                .iter()
                .map(|b| b.to_string())
                .collect::<Vec<_>>()
                .join("; ");
            format!("PdaSeed.Const [{}]", value)
        }
        IdlSeed::Arg(seed) => {
            format!("PdaSeed.Arg \"{}\"", seed.path)
        }
        IdlSeed::Account(seed) => {
            format!(
                "PdaSeed.Account \"{}\" {}",
                seed.path,
                optional_to_rocq(seed.account.clone(), true, false)
            )
        }
    }
}

fn optional_to_rocq(
    optional: Option<String>,
    with_parentheses_inside: bool,
    with_parentheses_outside: bool,
) -> String {
    match optional {
        Some(optional) => {
            if with_parentheses_inside {
                if with_parentheses_outside {
                    format!("(Some ({}))", optional)
                } else {
                    format!("Some ({})", optional)
                }
            } else if with_parentheses_outside {
                format!("(Some {})", optional)
            } else {
                format!("Some {}", optional)
            }
        }
        None => "None".to_string(),
    }
}
