---
name: verification-target-finding
description: Find binary targets and functions therein amenable and useful for deductive partial correctness verification.
---

This skill finds function verification targets in two phases:

  1.  The first phase finds binary executables from which to draw the functions targeted for verification.

  2.  The second phase selects functions from the selected binaries.

== Phase 1


== Phase 2

**Constraints:**  Functions must adhere to these constraints to be valid verification targets.

  1.  They must be OS-independent.  Any calls to the OS means the OS must be verified or at least axiomatized.  This is currently beyond scope.

  2.  They must not rely on self-modifying code.

  3.  Ghidra must be able to lift all of their instructions to pcode.  If it cannot, then update the sleigh spec, and make the update Picinae compatible.  See the picinae-sleigh skill for more details.

  4.  They must not rely on cpu mode switches, e.g. switching between ARM and Thumb modes in ARM architectures.

**Priority:**  Functions are prioritized by the list of traits below.  The more traits they meet, the higher their priority.

  1.  Function uses handwritten/inlined assembly code directly or transitively.

  2.  Function has a clear formal specification.

  3.  Function is less than 200 instructions (excluding its callees).

  4.  Function is a leaf function.

  5.  Function is used in a security or reliability critical execution path.

  6.  Function has associated CVEs.

Some of these priorities are harder to assess than others.  For example, whether it is used in a security or reliability critical execution path is difficult.  You should base this on a persuasive argument rather than a deep analysis of the binary and its usage.  Similar for "clear formal specification".  For associated CVEs, something about nvd.nist.gov or mitre.org TODO: finish this.
