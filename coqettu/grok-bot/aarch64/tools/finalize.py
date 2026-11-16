#!/usr/bin/env python3
"""Turn a working scratch proof into proofs/<fn>_proof.v (Grok Bot / coqettu).

usage: finalize.py <fn> <scratch.v> <header.txt> [--noframe]
  header.txt holds SEMANTICS / SPECIFICATION / INPUT-OUTPUT sections;
  {PROVENANCE} in it is replaced by the standard provenance block.
The scratch must use names: welltyped', <fn>_correct, exits, invs0.
"""
import sys, subprocess, re
fn, scratch, header = sys.argv[1:4]
noframe = '--noframe' in sys.argv
body = open(scratch).read()
hdr = open(header).read()
m = re.search(r"\| (0x[0-9a-f]+) => Inv 0", body)
entry = int(m.group(1), 16)
elf = entry - 0x100000
prov = f"""PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            {fn} at {elf:#x} (ELF vaddr); {entry:#x} in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            BOOL_NEGATE fix, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/{fn}_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq."""
hdr = hdr.replace("{PROVENANCE}", prov)
inner = hdr.rstrip()
assert inner.endswith("*)"), "header must end with *)"
inner = inner[:-2]
for bad in ("*)", "(*"):
    if bad in inner[2:]:
        sys.exit(f"header contains {bad!r} inside the comment; rewrite it")
frame = f"""
(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem {fn}_nwc: ∀ s2 s1, {fn}_armv8 s1 = {fn}_armv8 s2.
Proof. reflexivity. Qed.

Theorem {fn}_welltyped: welltyped_prog arm8typctx {fn}_armv8.
Proof. Picinae_typecheck. Qed.
"""
if not noframe:
    frame += f"""
Theorem {fn}_preserves_memory:
  forall_endstates {fn}_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem {fn}_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates {fn}_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem {fn}_preserves_x30:
  forall_endstates {fn}_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.
"""
frame += """
(* ---------------------------------------------------------------------- *)
(* Specification and invariants                                            *)
"""
body = body.replace("Open Scope N.\n", "Open Scope N.\n" + frame, 1)
body = re.sub(r"Theorem welltyped': welltyped_prog arm8typctx \w+\.\nProof\. Picinae_typecheck\. Qed\.\n", "", body)
body = body.replace("welltyped'", f"{fn}_welltyped")
body = body.replace(f"Theorem {fn}_correct:", f"Theorem {fn}_partial_correctness:")
body = body.replace("Definition exits :=", f"Definition {fn}_exits :=").replace("Definition invs0 :=", f"Definition {fn}_invs :=")
body = re.sub(r"\(invs0 ", f"({fn}_invs ", body)
body = re.sub(r"\(exits ", f"({fn}_exits ", body)
body = body.replace("unfold invs0, make_invs", f"unfold {fn}_invs, make_invs")
open(f"proofs/{fn}_proof.v", "w").write(hdr.rstrip() + "\n\n" + body)
print("wrote", f"proofs/{fn}_proof.v")
