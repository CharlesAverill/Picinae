#!/bin/bash

if [ -z "$OBJDUMP" ]; then
    echo "Set \$OBJDUMP, this is RISC-V"
    exit 1
fi

# Check if the user has provided an input file
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <compiled_file> <coq_definition_name>"
    exit 1
fi

input_file="$1"
coq_definition_name="$2"

# Check if the input file exists
if [ ! -f "$input_file" ]; then
    echo "Error: File '$input_file' not found!"
    exit 1
fi

echo "Require Import Picinae_riscv."
echo "Require Import NArith."
echo
echo "Definition $coq_definition_name (_ : store) (a : addr) : N :="
echo "    match a with"

first_addr=""
last_addr=""

# Run objdump to disassemble the file and process the output
while read -r line; do
    if echo "$line" | grep -E '^\s*[0-9a-f]+:' > /dev/null; then
        # This is a code line
        address=$(echo "$line" | awk '{print $1}' | sed 's/://')
        binary=$(echo "$line" | awk '{print $2}')
        instruction=$(echo "$line" | awk '{for (i=3; i<=NF; i++) printf "%s ", $i; print ""}')

        echo "    | 0x$address => 0x$binary (* $instruction *)"
        if [ -z "${first_addr}" ] && [ ! -z "${address}" ]; then
            first_addr="$address"
        fi
        last_addr="$address"
    elif echo "$line" | grep -E '^[0-9a-f]+ <[^>]+>:' > /dev/null; then
        # This is a label line
        label=$(echo "$line" | awk '{print $2}' | sed 's/://')
        echo "    (* $label *)"
    fi
done < <($OBJDUMP -d "$input_file")

echo "    | _ => 0"
echo "    end."
echo ""
echo "Definition start_$coq_definition_name : N := 0x${first_addr}."
echo "Definition end_$coq_definition_name : N := 0x${last_addr}."

