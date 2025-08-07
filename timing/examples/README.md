# Timing Proofs and Experiments

This directory contains both timing proofs and experiment results from their execution
on an instantiation of the NEORV32 soft-core CPU on a Terasic Cyclone V GX Starter Kit.

- `data_structures` contains programs involving standard data structures such as arrays and linked lists
- `FreeRTOS` contains a FreeRTOS demo
- `neorv32` contains a set of measurements of physical properties of the CPU, such as clock speed and memory latency.
    - `neorv32/latencies.json` is utilized by comparison scripts in `data_structures` and `FreeRTOS`

This directory is a Python project for good reason, don't worry about it.

## Compiling proofs

Make sure you've compiled the files in the `timing` directory (the parent of this one) with `make`. Then you're good to start stepping through these proofs.

## Compiling/running programs

See `neorv32/readme.txt`.

## Example

See `riscv_addloop_proof.v` for a rudimentary timing proof.
