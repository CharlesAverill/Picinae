---
name: picinae-sleigh
description: Write and validate Ghidra SLEIGH processor specifications whose p-code can be lifted to finite, semantically meaningful Picinae IL.
---

# Picinae-compatible SLEIGH specifications

Use this process when creating or extending a Ghidra processor module for use with the Ghidra-to-Picinae lifter. A SLEIGH specification that disassembles correctly is not necessarily suitable for Picinae: its p-code must also terminate on every path and preserve the instruction's architectural semantics.

## Core requirements

A suitable specification must satisfy all of these:

- Each machine instruction has finite p-code control flow. Picinae does not represent unbounded loops within an instruction.
- Constant-space `BRANCH`, `CBRANCH`, and `CALL` offsets are positive and land within the instruction's p-code operation list or exactly at its end.
- No silent placeholders hide missing semantics. `Nop`, an ignored `CALLOTHER`, or a wrong condition code is not a valid substitute for an instruction's behavior.
- Registers, subregisters, memory widths, endianness, condition codes, and operand overlap behavior match the architecture manual.
- Validation exercises semantics as well as decoding and Coq typechecking.

Machine-address branches to other instructions are normal and do not have the same restriction as constant-space p-code-relative branches.

## 1. Establish the reference and current baseline

1. Use the newest architecture manual available and record its document number and edition date. Do not assume that an older manual contains newer instructions or current control-bit layouts.
2. Read the detailed semantics, not only the opcode table. Check condition codes, reserved bits, alignment rules, address arithmetic, and behavior when operands overlap.
3. Inspect all existing `.slaspec` and included `.sinc` files. Inventory constructors, shared macros, register declarations, generated `.sla` files, and current validation results.
4. Compare complete instruction families rather than adding only the mnemonic seen in one binary. Include architectural variants when they fit the module's existing categories.
5. Identify every semantic loop, including loops hidden in shared macros. Search for labels and `goto` statements, then determine whether each target is forward or backward in the emitted p-code.

Do not treat generated `.sla` files as the human-readable source of truth. Edit the SLEIGH sources and regenerate them.

## 2. Map encodings carefully

SLEIGH token bit numbering and architecture-manual bit numbering may run in opposite directions. SLEIGH labels the least-significant token bit as bit 0, with endianness affecting multi-byte tokens. IBM manuals commonly number instruction bits from most significant to least significant.

For a big-endian token, map each field from its manual bit positions explicitly rather than copying the numbers. For example, a six-bit field in the low six bits of a byte needs a different token range from a six-bit field occupying the high six bits.

Also check:

- Control bits embedded in immediate fields, such as zero-remaining-bits and test-results controls.
- Reserved bits that should be constrained separately from semantic operands.
- Whether a value is signed, unsigned, scaled, or a register number.
- Whether register zero means the architectural zero register or an absent base/index component.
- Whether the third tuple value in printed p-code is bytes. In `(const, 0xfffffff9, 4)`, the `4` means four bytes, so the constant is a 32-bit signed `-7`, not an oversized four-bit value.

Use explicit temporary widths when SLEIGH cannot infer them. In particular, watch shifts, comparisons, macro arguments, arithmetic on narrow token fields, and exported computed values. A warning that a table exports size zero must be fixed, not ignored.

## 3. Preserve architectural semantics

Follow the manual's operation order and use temporaries when an instruction reads and writes the same register.

- Compute addresses before changing registers used by an address expression.
- Preserve the unrotated first operand when required by rotate-and-select instructions.
- Handle `R1 == R2` and register-pair aliasing deliberately.
- Use signed condition-code results where required; a Boolean zero/nonzero result is not interchangeable with zero/negative/positive condition codes.
- Preserve unaffected register halves and condition codes exactly.
- Do not read or write extra memory to simplify an implementation. Additional accesses can fault or alter memory beyond the architectural operand range.

When adding a new instruction family, test representative values for zero, all ones, one-hot masks, overlapping operands, wrapping ranges, and sign-extension boundaries.

### Capability and compressed-ISAs: CHERIoT lessons

- Model each CHERIoT general capability as a 64-bit packed register plus a separate tag register. Integer registers overlay the low 32 bits at eight-byte strides; in particular, `a0` overlays `ca0` and `a1` overlays `ca1`. Declaring independent integer and capability registers breaks mixed integer/capability code even when each instruction looks correct alone.
- Keep PCC, MTCC, MTDC, MScratchC, and MEPCC tagged as well. Preserve the source capability until all trap and representability checks finish. For example, a faulting `cjalr` must not perform link, PCC, or interrupt-status writes, and `cd == cs1` must still read the original source capability.
- Capability tops need 33 bits. A SLEIGH slice such as `:5` denotes five **bytes**, so explicitly mask decoded tops with `0x1ffffffff`; do not confuse a byte width with a 33-bit field. Truncate encoded B/T fields to their architectural nine bits before bounds decoding.
- Test address representability by re-decoding the updated capability and comparing its bounds with the original. Exercise exact bounds, round-down cases, overlapping operands, clearing tags, capability-load permission attenuation, revocation, and capability stores in addition to arithmetic.
- Auxiliary address spaces such as CHERIoT `tagram`, `revocation`, and CSR memory are architecturally distinct. Keep them distinct in SLEIGH and account for them explicitly in the Picinae architecture/lifter; never silently alias their loads or stores to main RAM.
- For a compressed ISA, enumerate every 16-bit encoding whose low bits select a compressed instruction, not just hand-written examples. Check constructor overlap and special exclusions directly: for example, CHERIoT `c.cjr` must exclude the `cra` encoding used by `cret`.
- Enumerate structured 32-bit opcode/function fields and register selectors as a separate decoding sweep. Require every decoded instruction to have nonzero length, no `CALLOTHER`, and no non-positive constant-space branch. Decoding coverage still needs targeted execution tests for semantics.

## 4. Eliminate p-code-relative loops

Prefer arithmetic or bounded straight-line encodings.

### Inclusive bit-range masks

For IBM bit numbers `start` and `end` in the range 0-63:

```text
low  = 0xffffffffffffffff >> start
high = 0xffffffffffffffff << (63 - end)
mask = low & high                 when start <= end
mask = low | high                 when start > end
```

`start == end` selects one bit, not the entire register. The `start > end` case wraps through bit 63 to bit 0.

### Rotates

A 64-bit left rotate can use:

```text
rotated = (value << amount) | (value >> (64 - amount))
```

Confirm the target p-code's behavior for shifts equal to or greater than the operand width. Do not introduce a special loop for the zero-amount case without checking whether it is needed.

### Leading and trailing zeros

Use `lzcount` where available. For trailing zeros, isolate the lowest set bit and account for zero explicitly:

```text
lowBit = value & (0 - value)
count  = 63 - lzcount(lowBit) + 65 * zext(value == 0)
```

This returns 64 for zero and the correct trailing-zero count otherwise. Do not confuse `lzcount(~lowBit)` with the trailing-zero count.

### Deposit and extract

A bounded arithmetic implementation can avoid both loops and conditionals:

- Deposit: scan the mask left to right, append the next source bit only when the mask bit is one, and advance the source only for selected positions.
- Extract: scan the mask left to right, append selected source bits, then left-justify by `64 - popcount(mask)` for a 64-bit result.

The source supplies the first `popcount(mask)` **bit positions**, not the first `popcount(mask)` set bits.

### Multiple-register operations

When the architecture defines a bounded register range, unroll at most the architectural maximum and use forward-only exits. Preserve wraparound register numbering and precompute disjoint source addresses.

Avoid large chains of conditional paths when a straightforward arithmetic encoding exists. Even with structured lifting, complex control flow increases output and typechecking cost.

### Branches inside an instruction

For a constant p-code-relative destination `n`, the target is the current operation index plus `n`, interpreted using the destination varnode's signed width.

- A direct relative `BRANCH` resumes at that target.
- For a properly nested forward `CBRANCH`, lift the taken path as `Nop`, lift the fall-through operations up to the target in the `else` arm, and place the shared continuation after the `If`. This is equivalent to copying both continuations but avoids exponential output growth on CHERIoT capability checks.
- No explicit jump to the next machine instruction is needed for this structured form because the taken continuation is not duplicated. If using a copied-path encoding instead, a copied taken path that reaches the end must jump to the next instruction.
- For a non-nested branch that escapes the current structured region, fall back to the copied-path encoding for that instruction. Restore any mutable lifter type state before fallback. Copied taken paths that reach the end must jump to the next machine instruction.
- Reject backward and self-relative branches unless the lifter has a separate finite representation for them.

Do not replace such branches with `Nop`.

## 5. Keep Picinae and the lifter aligned

For a new architecture, also provide:

- A Picinae architecture definition with every modeled register and its bit width.
- Memory width and endianness.
- Architecture-specific variable names that do not collide with existing Picinae architectures.
- Register/type-context and byte/bit-register mappings in `translationConstants.py`.
- Language-ID dispatch in `pcode2coq_lib.py`.

If the language is already recognized, check that new SLEIGH temporaries and p-code operators have lifter support. Picinae typechecking catches width and well-formedness errors, not incorrect instruction semantics.

Check memory operations against actual p-code rather than assuming their shape:

- A direct memory destination can appear on `COPY` or an arithmetic operation, not only `STORE`. It must become a Picinae `Store`; `Move V_MEM (...)` is ill-typed and loses the address.
- A SLEIGH space with `wordsize=4` has word offsets, while Picinae memories are byte-addressed. Scale offsets by the word size and widen the scaled address as needed, or consecutive word-sized CSR accesses will overlap.
- A p-code `COPY` destination takes its own width. When the input temporary is wider, emit `CAST_LOW`; do not type the destination from the input. CHERIoT capability bounds exposed this as a 64-bit temporary copied into a 32-bit base local, followed by a failed conditional join.
- If typechecking fails on a large instruction, binary-search statement prefixes with `typchk_stmt` to locate the first invalid operation. Inspect actual widths and conditional context meets instead of treating all leftover goals as tactic limitations.

## 6. Validate in layers

Run every layer after a semantic change. Do not stop after a successful SLEIGH build.

### A. Compile the actual deliverable

From the Ghidra installation:

```bash
support/sleigh Ghidra/Processors/<MODULE>/data/languages/<ARCH>.slaspec
```

Investigate every new warning, especially unresolved sizes, size-zero exports, constructor conflicts, and unexpected NOP constructors. Confirm that the generated `.sla` was rebuilt.

### B. Decode targeted instruction encodings

Create raw binaries covering each new constructor and important control-bit combinations. Disassemble them through the real language module and verify:

- Mnemonic and instruction length.
- Register and immediate operands.
- Control-bit variants and aliases.
- No non-positive constant-space relative branches.

Do not rely on hand-written expected p-code alone; compare raw bytes with the manual's instruction diagram.

### C. Check arithmetic independently

Compare closed forms against a simple reference implementation over edge cases and randomized 64-bit inputs. Include:

- `start < end`, `start == end`, and `start > end` mask ranges.
- Zero and all-ones masks.
- Single-bit masks at both ends.
- Sources with more one bits than the mask and fewer one bits than the mask.
- Zero, one, the top bit, and values requiring sign extension.

If an independent check fails, establish whether the specification or the reference is wrong before changing either.

### D. Analyze a substantial real binary

Run full Ghidra analysis on representative libraries and audit every decoded instruction for:

- Unsupported or incorrectly sized instructions.
- Bad function entry points.
- Non-positive constant-space relative branches.

Compare instruction and function counts with earlier runs when available. A type-correct lift of one function does not establish whole-library coverage.

### E. Exercise end-to-end lifting

Lift representative functions using `pyghidraRun` and `pcode2coq_headless.py`, using global addressing. Then compile the generated program and its well-typedness theorem:

```bash
rocq c -R /path/to/picinae Picinae /path/to/output/function_arch.v
```

Include instructions with forward conditionals and any newly added operations. Confirm that no relative branch was silently converted to `Nop`.

### F. Diagnose Java and PyGhidra failures honestly

A Ghidra scripting failure is not necessarily a missing or incompatible JVM. Start by checking `java -version` and `javac -version`. In the S390x validation, OpenJDK and `javac` 21 were available and both `sleigh` and `pyghidraRun` could start; Java itself was not the problem.

Distinguish these failure modes:

- **Java compilation failed:** diagnostics such as `cannot find symbol` followed by `ClassNotFoundException` usually mean the class was never produced. Fix the source, imports, or API usage first; clearing caches will not fix a compiler error.
- **Java bundle activation failed:** `Failed to get OSGi bundle containing script` can occur even when `.class` files exist. Inspect `~/.config/ghidra/<version>/osgi/compiled-bundles/` and check for a usable `META-INF/MANIFEST.MF`. In the S390x run, generated script bundles had incomplete or empty metadata.
- **The headless command continued:** Ghidra can print `Post-analysis succeeded` after a script-load error. Search the complete log for `ERROR`, exceptions, and tracebacks, and verify that expected output files were actually created.

For a suspected stale script cache, use a fresh `-scriptPath` first. If cache surgery is unavoidable, stop other Ghidra processes and **move** only the generated Felix or incomplete bundle directories aside rather than deleting the entire Ghidra configuration. Retry once and restore the moved directories if the experiment does not help. In the S390x investigation, resetting Felix and moving the incomplete compiled bundles aside did **not** repair activation, so cache deletion was not the fix.

The working fix was to port the Java audit and function-creation scripts to PyGhidra scripts with `#@runtime PyGhidra`, then run them through `support/pyghidraRun` as `-preScript` or `-postScript`. This uses the same Ghidra program, instruction, and p-code APIs without relying on the broken Java-script bundle loader. It repaired the validation pipeline, but did not repair the underlying OSGi loader; do not claim otherwise.

A subsequent attempt to add emulator-based semantic tests also failed. JPype reported ambiguous `AbstractPcodeExecutorState.setVar` overloads, and attempts to pass an address or coerced Java value produced `ClassCastException` or argument-type errors because this byte-state API expects byte-array state values. A local variable named `state` additionally collided with PyGhidra's script-state global. Those experiments did not produce a working emulator test. Do not report emulation as passed: use independent arithmetic reference tests plus real decoding, lifting, and Rocq compilation until the exact state API and JPype overloads are understood.

For CHERIoT, the successful alternative was `ghidra.pcode.emu.PcodeEmulator` with `SleighProgramCompiler`. Compile small SLEIGH setup programs to assign registers and memory, call `thread.stepInstruction(1)`, and read results with a compiled SLEIGH expression. This avoids the failing byte-state `setVar` overloads. Keep this distinction clear: the older state-API experiments failed, while the later CHERIoT `PcodeEmulator` suites did run and pass.

## 7. Final review

Before declaring completion:

- Re-read the newest manual's detailed sections for changed instructions.
- Search sources again for backward semantic branches and stale comments describing old behavior.
- Check generated files and repository status; remove incidental logs and test artifacts from the deliverable.
- Report any remaining unmodeled operations, unsupported instructions, or unverified semantics plainly.
- Leave unrelated source and user configuration changes untouched.

## Common mistakes to avoid

- Using an old manual when a newer edition is available.
- Copying IBM bit positions directly into SLEIGH token ranges.
- Treating p-code varnode sizes as bits instead of bytes.
- Assuming `start == end` means all bits.
- Encoding an instruction with a backward p-code-relative loop and merely teaching the lifter to ignore it.
- Replacing unsupported semantics with `Nop` or an unexamined `CALLOTHER`.
- Performing extra memory accesses that the architecture does not define.
- Reusing a generic address helper when the instruction specifies special index arithmetic.
- Forgetting condition-code side effects or zero/test controls.
- Accepting a successful disassembly or Rocq typecheck as proof of semantic correctness.
- Adding only the instruction observed in one binary and missing the rest of its family.
