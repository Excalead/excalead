use anchor_lang_idl::{
    convert::convert_idl,
    types::{Idl, IdlArrayLen, IdlDefinedFields, IdlInstructionAccountItem, IdlType, IdlTypeDefTy},
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
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    // Read the IDL file
    let idl_content = fs::read(&args.idl_path)?;
    let idl = convert_idl(&idl_content)?;

    // Generate Rocq code
    let rocq_code = generate_rocq(&idl);

    // Output the result
    if let Some(output_path) = &args.output {
        fs::write(output_path, rocq_code)?;
    } else {
        print!("{}", rocq_code);
    }

    Ok(())
}

fn generate_rocq(idl: &Idl) -> String {
    let mut output = String::new();

    // Header
    output.push_str("Require Import Excalead.Excalead.\n\n");

    // Constants
    if !idl.constants.is_empty() {
        output.push_str("(** Constants *)\n");
        for constant in &idl.constants {
            let rocq_type = idl_type_to_rocq(&constant.ty);
            output.push_str(&format!("Definition {} : {} :=\n", constant.name, rocq_type));
            output.push_str(&format!("  {}.\n\n", constant.value));
        }
    }

    // Error codes
    if !idl.errors.is_empty() {
        output.push_str("(** Error codes *)\n");
        output.push_str("Module ErrorCode.\n");
        output.push_str("  Inductive t : Set :=\n");
        for (i, error) in idl.errors.iter().enumerate() {
            let comma = if i < idl.errors.len() - 1 { "," } else { "." };
            let msg = error
                .msg
                .as_ref()
                .map(|m| format!(" (* {})", m))
                .unwrap_or_default();
            output.push_str(&format!("  | {}{} : string{}\n", error.name, msg, comma));
        }
        output.push_str("End ErrorCode.\n\n");
    }

    // Custom types
    if !idl.types.is_empty() {
        output.push_str("(** Custom types *)\n");
        for ty_def in &idl.types {
            match &ty_def.ty {
                IdlTypeDefTy::Struct { fields } => {
                    if let Some(IdlDefinedFields::Named(fields_list)) = fields {
                        output.push_str(&format!("Module {}.Record t : Set :={{\n", ty_def.name));
                        for (i, field) in fields_list.iter().enumerate() {
                            let comma = if i < fields_list.len() - 1 { ";" } else { "." };
                            let rocq_type = idl_type_to_rocq(&field.ty);
                            output
                                .push_str(&format!("  {} : {} {}\n", field.name, rocq_type, comma));
                        }
                        output.push_str(&format!("}}\nEnd {}.\n\n", ty_def.name));
                    }
                }
                IdlTypeDefTy::Enum { variants } => {
                    output.push_str(&format!("Module {}.Inductive t : Set :=\n", ty_def.name));
                    for (i, variant) in variants.iter().enumerate() {
                        let comma = if i < variants.len() - 1 { " |" } else { "." };
                        output.push_str(&format!("{}{}\n", variant.name, comma));
                    }
                    output.push_str(&format!("End {}.\n\n", ty_def.name));
                }
                IdlTypeDefTy::Type { .. } => {
                    output.push_str(&format!(
                        "Module {}.Definition t : Set := TODO.\n",
                        ty_def.name
                    ));
                    output.push_str(&format!("End {}.\n\n", ty_def.name));
                }
            }
        }
    }

    // Account structures
    if !idl.accounts.is_empty() {
        output.push_str("(** Account structures *)\n");
        for account in &idl.accounts {
            output.push_str(&format!("Module {}.Record t : Set :={{\n", account.name));
            // We'll need to find the type definition for this account
            if let Some(ty_def) = idl.types.iter().find(|t| t.name == account.name) {
                if let IdlTypeDefTy::Struct { fields } = &ty_def.ty {
                    if let Some(IdlDefinedFields::Named(fields_list)) = fields {
                        for (i, field) in fields_list.iter().enumerate() {
                            let comma = if i < fields_list.len() - 1 { ";" } else { "." };
                            let rocq_type = idl_type_to_rocq(&field.ty);
                            output
                                .push_str(&format!("  {} : {} {}\n", field.name, rocq_type, comma));
                        }
                    }
                }
            }
            output.push_str(&format!("}}\nEnd {}.\n\n", account.name));
        }
    }

    // Instruction contexts
    if !idl.instructions.is_empty() {
        output.push_str("(** Instruction contexts *)\n");
        for instruction in &idl.instructions {
            output.push_str(&format!(
                "Module {}.Record t : Set :={{\n",
                instruction.name
            ));
            let mut account_idx = 0;
            for account in &instruction.accounts {
                match account {
                    IdlInstructionAccountItem::Single(acc) => {
                        let rocq_type_str = if acc.writable {
                            if acc.signer {
                                "Signer.t".to_string()
                            } else {
                                format!("Account.t TODO (* {})", acc.name)
                            }
                        } else if acc.signer {
                            "Signer.t".to_string()
                        } else {
                            format!("Account.t TODO (* {})", acc.name)
                        };
                        let comma = if account_idx < instruction.accounts.len() - 1 {
                            ";"
                        } else {
                            "."
                        };
                        output.push_str(&format!("  {} : {} {}\n", acc.name, rocq_type_str, comma));
                        account_idx += 1;
                    }
                    IdlInstructionAccountItem::Composite(_) => {
                        // Handle composite accounts
                        output.push_str("  (* TODO: composite accounts *)\n");
                    }
                }
            }
            output.push_str(&format!("}}\nEnd {}.\n\n", instruction.name));
        }
    }

    // Result type
    output.push_str("Module Result.\n");
    output.push_str("  Inductive t (A : Set) :=\n");
    output.push_str("  | Ok : A -> t A\n");
    output.push_str("  | Err : ErrorCode.t -> t A.\n");
    output.push_str("  Arguments Ok {A} _.\n");
    output.push_str("  Arguments Err {A} _.\n");
    output.push_str("End Result.\n\n");

    // Context module
    output.push_str("Module Context.\n");
    output.push_str("  Record t {Accounts Bumps : Set} : Set := {\n");
    output.push_str("    accounts : Accounts;\n");
    output.push_str("    bumps : Bumps;\n");
    output.push_str("  }.\n");
    output.push_str("  Arguments t : clear implicits.\n");
    output.push_str("End Context.\n\n");

    // Program stub
    output.push_str("Module program.\n");
    output.push_str(&format!(
        "  (* TODO: Implement instructions for {})\n",
        idl.metadata.name
    ));
    for instruction in &idl.instructions {
        output.push_str(&format!(
            "  Definition {} (ctx : Context.t {}.t {}Bumps.t) : Result.t unit :=\n",
            instruction.name, instruction.name, instruction.name
        ));
        output.push_str("    (* TODO *)\n");
        output.push_str("    Result.Ok tt.\n\n");
    }
    output.push_str("End program.\n");

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
        IdlType::Bytes => "bytes".to_string(),
        IdlType::String => "string".to_string(),
        IdlType::Pubkey => "Pubkey".to_string(),
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
        IdlType::Defined { name, .. } => name.clone(),
        IdlType::Generic(name) => name.clone(),
        // Handle newer types if needed
        IdlType::U256 => "u128 (* TODO: u256 *)".to_string(),
        IdlType::I256 => "i128 (* TODO: i256 *)".to_string(),
        _ => format!("TODO (* {:?})", ty),
    }
}
