#!/bin/bash

# Example usage of the IDL to Rocq converter

echo "Building the converter..."
cargo build --manifest-path src/Cargo.toml --release

echo ""
echo "Example 1: Convert a new IDL format file"
echo "=========================================="
cargo run --manifest-path src/Cargo.toml --bin idl-to-rocq -- \
  third-parties/anchor/tests/idl/idls/new.json -o /tmp/new_idl.v
echo "Output saved to /tmp/new_idl.v"
echo ""

echo "Example 2: Convert output to stdout (first 100 lines)"
echo "============================================"
cargo run --manifest-path src/Cargo.toml --bin idl-to-rocq -- \
  third-parties/anchor/tests/idl/idls/new.json | head -100

echo ""
echo "Done!"
