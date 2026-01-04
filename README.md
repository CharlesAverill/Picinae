# Picinae

## Examples

See [examples](./examples/) for a showcase of Picinae's reasoning capabilities.

| Program | Proof | Category | Platform |
|---|---|---|---|
| [`strcmp`](./examples/i386/strcmp.v) | [`strcmp_proof.v`](./examples/i386/strcmp_proof.v) | Partial Correctness | x86-64 |
| [`strlen`](./examples/i386/strlen.v) | [`strlen_proof.v`](./examples/i386/strlen_proof.v) | Partial Correctness | x86-64 |
| [`wcsspn`](./examples/i386/wcsspn.v) | [`wcsspn_proof.v`](./examples/i386/wcsspn_proof.v) | Partial Correctness | x86-64 |
| [`memset`](./examples/arm/arm7_memset.v) | [`arm7_memset_proof.v`](./examples/arm/arm7_memset_proof.v) | Partial Correctness | ARMv7 |
| [`strlen`](./examples/arm/arm7_strlen.v) | [`arm7_strlen_proof.v`](./examples/arm/arm7_strlen_proof.v) | Partial Correctness | ARMv7 |
| [`strcasecmp`](./examples/arm/arm8_strcasecmp.v) | [`arm8_strcasecmp_proof.v`](./examples/arm/arm8_strcasecmp_proof.v) | Partial Correctness | ARMv8 |

## Installation

1. Install [opam](https://opam.ocaml.org/doc/Install.html)
2. Create and activate a [switch](https://ocaml.org/docs/opam-switch-introduction) for Picinae
2. Install [dune](https://dune.build/install)
3. Clone the [Picinae](https://github.com/CharlesAverill/Picinae) repo
    ```bash
    git clone https://github.com/CharlesAverill/Picinae.git && cd Picinae
    ```
4. Install dependencies
    ```bash
    opam install . --deps-only
    ```

## Building

```bash
dune build
```
