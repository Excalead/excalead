# IDL to Rocq Converter

A Rust binary that converts Anchor IDL JSON files to Rocq code following the Excalead pattern.

## Building

From the project root:

```bash
cd src
cargo build --release
```

## Usage

### Basic usage

Convert an IDL file and print to stdout:

```bash
cargo run --manifest-path src/Cargo.toml --bin idl-to-rocq -- path/to/idl.json
```

### Save to file

Save the output to a file:

```bash
cargo run --manifest-path src/Cargo.toml --bin idl-to-rocq -- path/to/idl.json -o output.v
```

## Example

Convert the test IDL:

```bash
cargo run --manifest-path src/Cargo.toml --bin idl-to-rocq -- \
  third-parties/anchor/tests/idl/idls/new.json -o output.v
```

## Output Format

The generated Rocq code includes:

1. **Basic type definitions**: `u8`, `u16`, `u32`, `u64`, `u128`, `i8`, `i16`, `i32`, `i64`, `i128`, `bool`, `bytes`, `string`, etc.
2. **Error codes**: Enumerated type based on IDL errors
3. **Custom types**: Structs and enums from the IDL `types` field
4. **Account structures**: Records for each account type
5. **Instruction contexts**: Records for each instruction's accounts
6. **Result type**: Common `Result.t` type for error handling
7. **Context module**: Generic context wrapper with accounts and bumps
8. **Program module**: Stub definitions for each instruction

## Supported IDL Formats

- New Anchor IDL format (spec 0.1.0) - has `metadata.spec` field
- Legacy IDL format (pre Anchor v0.30) - has `isMut`/`isSigner` fields

## Notes

- The generated code includes TODO markers for fields that need manual completion
- Account types are represented as generic `Account.t TODO` and need to be replaced with actual account type names
- Instruction implementations are stubs that need to be filled in manually
- Array types are converted to Rocq `list` types with comments indicating the original array size
- Some complex types (like tuples) may need manual refinement

