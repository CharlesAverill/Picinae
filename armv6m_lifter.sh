#!/bin/bash

# ARMv6-M Thumb Binary Lifter for Picinae
# Generates Coq definitions from ARM Thumb binaries, mapping each address to
# the halfword stored there (a 32-bit instruction occupies two halfwords)

if [ -z "$OBJDUMP" ]; then
    echo "Set \$OBJDUMP to your ARM objdump (e.g., arm-none-eabi-objdump)"
    exit 1
fi

if [ "$#" -ne 2 ] && [ "$#" -ne 3 ]; then
    echo "Usage: $0 <compiled_file> <coq_definition_name> [function_name]"
    exit 1
fi

input_file="$1"
coq_definition_name="$2"
function_name="$3"

if [ ! -f "$input_file" ]; then
    echo "Error: File '$input_file' not found!"
    exit 1
fi

# Disassemble only the requested function (and its literal pool), if given
if [ -z "$function_name" ]; then
    objdump_args=(-d -r)
else
    objdump_args=(-d -r "--disassemble=$function_name")
fi

echo "(* Auto-generated from $input_file *)"
echo "From Stdlib Require Import NArith."
echo "Require Import Picinae_armv6m."
echo ""
echo "Open Scope N."
echo ""
echo "Definition $coq_definition_name (a : addr) : N :="
echo "    match a with"

first_addr=""
last_addr=""

# Emit the halfword at address $1
emit() {
    echo "    | 0x$1 => 0x$2 (* $3 *)"
    if [ -z "${first_addr}" ]; then
        first_addr="$1"
    fi
    last_addr="$1"
}

# Run objdump with Thumb disassembly
while IFS= read -r line; do
    if echo "$line" | grep -E '^\s*[0-9a-f]+: R_' > /dev/null; then
        # Relocation (e.g., a call to an external function in an object file)
        relocation=$(echo "$line" | sed -E 's/^\s*//; s/\t/ /g')
        echo "    (* relocation $relocation *)"
    elif echo "$line" | grep -E '^\s*[0-9a-f]+:' > /dev/null; then
        # Extract address, binary, and instruction (tab-separated)
        address=$(echo "$line" | awk -F'\t' '{print $1}' | sed 's/[: ]//g')
        binary=$(echo "$line" | awk -F'\t' '{print $2}')
        instruction=$(echo "$line" | awk -F'\t' '{for (i=3; i<=NF; i++) printf "%s ", $i; print ""}' | sed 's/  */ /g; s/ *$//')
        next_address=$(printf "%x" $((16#$address + 2)))
        read -r -a halves <<< "$binary"

        if [ "${#halves[@]}" -eq 2 ]; then
            # ARM Thumb can be 32-bit: first halfword, then second halfword
            emit "$address" "${halves[0]}" "$instruction"
            emit "$next_address" "${halves[1]}" "(second halfword)"
        elif [ "${#halves[0]}" -eq 8 ]; then
            # Literal pool word, little-endian: low halfword first
            emit "$address" "${halves[0]:4:4}" "$instruction"
            emit "$next_address" "${halves[0]:0:4}" "(high halfword)"
        else
            emit "$address" "${halves[0]}" "$instruction"
        fi
    elif echo "$line" | grep -E '^[0-9a-f]+ <[^>]+>:' > /dev/null; then
        # Function label
        label=$(echo "$line" | awk '{print $2}' | sed 's/://')
        echo "    (* $label *)"
    fi
done < <($OBJDUMP "${objdump_args[@]}" "$input_file")

echo "    | _ => 0"
echo "    end."
echo ""
echo "Definition start_$coq_definition_name : N := 0x${first_addr}."
echo "Definition end_$coq_definition_name : N := 0x${last_addr}."
