# e01-x86-inventory

Complete binary/source inventory for the exact Ubuntu amd64 glibc
`2.35-0ubuntu3.12` used by the existing copy proofs. No function proof,
lift, ISA change, or theorem was added or adapted. Theorem checking and
`Print Assumptions`: **N/A**. Dune: **N/A** for this inventory-only assignment.

## Charles's environment rule (unchanged)

> install NOTHING directly on the host. All dependencies (Rocq/opam/OCaml/dune, cross compilers like arm-none-eabi-gcc, glibc 2.35 Ubuntu packages/binaries, QEMU, Python tools) go in virtual/isolated environments only: opam local switches, Python venvs, or Docker containers (e.g. an ubuntu:22.04 container to pull the exact glibc 2.35 binaries). No sudo, no apt on the host, no global pip/npm, no shell rc edits. Keep envs under /home/charles/code/friends/.toolchains/. Reuse /home/charles/code/friends/.toolchains/arm-validation/picinae-env read-only if compatible (verified Rocq 9.1.1, OCaml 4.14.2, Dune 3.22.2). Additional dependencies use a distinct isolated per-unit environment under that toolchains root; do not alter shared envs.

All downloaded packages, debug symbols, patched source, and the stdlib-only
Python venv are under
`/home/charles/code/friends/.toolchains/e01-x86-inventory/`.
No packages were installed on the host or into shared environments. Existing
host binutils, GnuPG, and Debian archive extraction tools only inspect data.
The target ELF was never executed or loaded as a library.

## Reproduce

From the repository root, run:

```sh
Examples/claude/inventory/e01-x86-inventory/run.sh
PYTHONDONTWRITEBYTECODE=1 /home/charles/code/friends/.toolchains/e01-x86-inventory/venv/bin/python3 Examples/claude/inventory/e01-x86-inventory/verify.py
```

The first command creates a venv with `--without-pip` if needed, retrieves
locked snapshot URLs, checks all download hashes, authenticates the Ubuntu
archive signature and index-to-package/source hash chain, extracts the two
binary packages without maintainer scripts, applies the exact source package
patch series with `dpkg-source`, verifies the runtime hash and matching debug
build ID, and generates the inventory. Use `run.sh --offline` once downloads
are cached. Nothing builds or executes glibc. The shell wrapper caps virtual
memory at 8,000,000 KiB; there are no parallel build jobs.

Prerequisites already present during validation: `/usr/bin/python3`, `gpgv`,
`dpkg-deb`, `dpkg-source`, `readelf`, `objdump`, `nm`, `objcopy`, and the Ubuntu
archive keyring. The scripts install no dependencies. A machine missing these
must provide them in an isolated environment, in accordance with Charles's
rule. Network or filesystem sandbox permission may be needed to retrieve and
write the dedicated toolchain directory.

`downloads.lock.json` pins URLs, sizes and SHA256 values. Python's standard
library handles downloads and metadata; no third-party Python packages are
needed. `retrieve.py --root` permits only this unit's directory or its children.
Its `--offline` mode still performs signature and checksum verification.

## Exact provenance

- Runtime package: `libc6_2.35-0ubuntu3.12_amd64.deb`, SHA256
  `d869a972aadd92883cfbef152a13e2a6084e82149575055b9c8a19336aef1f6e`.
- Extracted `runtime/lib/x86_64-linux-gnu/libc.so.6`: SHA256
  `9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`.
- GNU build ID: `085164b7e9093b36e3be17226f0d94a35b818c55`.
- Matching `libc6-dbg_2.35-0ubuntu3.12_amd64.deb`: SHA256
  `58078a980a3ababac41b8756e620da09fcb0f8f64f4e50db7bbcbeac82a8a505`;
  debug file `debug/usr/lib/debug/.build-id/08/5164b7e9093b36e3be17226f0d94a35b818c55.debug`.
- Source: `glibc_2.35-0ubuntu3.12.dsc` and its upstream tarball, upstream
  signature, and Ubuntu Debian patch tarball. All hashes are locked and checked
  against the archive-signed Sources index. `source/` is the **patched Ubuntu
  package source**, not just upstream glibc 2.35.
- Retrieval root:
  `https://snapshot.ubuntu.com/ubuntu/20251001T000000Z/`.
  Authentication indexes: `dists/jammy-proposed/InRelease`,
  `main/binary-amd64/Packages.xz`, and `main/source/Sources.xz`.
  InRelease signer: Ubuntu Archive Automatic Signing Key (2018),
  fingerprint `F6ECB3762474EDA9D21B7022871920D1991BC93C`.
  This is a historical authenticity check, not a freshness claim.
- Live `archive.ubuntu.com` returned HTTP 404 for the old runtime and dsc.
  Snapshot `jammy-updates` indexes at 2025-10-01 and 2026-01-01 contained
  `.11`, so they were rejected for package authentication. The dated
  `jammy-proposed` indexes contain and authenticate `.12`; no target change
  or mirror substitution was made.

`generated/target-manifest.json` hashes downloads and both ELF files.
`generated/package-provenance.json` preserves the exact authenticated binary
and source package index records.
`generated/source-files.sha256` hashes relevant patched multiarch sources,
CPU/cache initialization sources, the changelog and patch list.
`generated/SHA256SUMS` covers every generated report.

## Inventory and address conventions

The scan reads both the runtime dynamic symbol table and the matching debug
symbol table, including local implementations, versioned compatibility
entries, hidden aliases, checked wrappers and helper labels. There are
**398 symbol records, 242 distinct (address,size) extents**, and **210 source
IFUNC implementation-list entries**, all corroborated by actual debug symbols.
The extra families intentionally extend beyond the minimum requested set.

See [generated/variants.md](generated/variants.md) for the 14-by-6 copy entry
matrix and all subsequent-wave string suffixes. See
[generated/symbols.tsv](generated/symbols.tsv) for exact names, versions, symbol
types, binding, table provenance, addresses and sizes. Internals without an
ELF symbol version have a null version; resolver aliases are not additional
implementations.

The ELF is `ET_DYN`, `EM_X86_64`. Its lowest PT_LOAD virtual address is zero.
For this original Ghidra import:

```text
Ghidra address = ELF virtual address + 0x100000
runtime address = ELF virtual address + process load bias
memcpy_amd64.v IL address = Ghidra address
memmove_avx_amd64.v IL code address = ELF address - 0x1a0840
```

Memmove's IL static-data addresses retain the Ghidra base. File offsets are
computed from the recorded PT_LOAD segments, never assumed equal to a virtual
address. `elf-header.txt`, `notes.txt` and `relocations.txt` preserve ELF evidence.

`inventory.json` records half-open symbol extents, exact runtime-byte hashes,
file offsets, aliases at the same entry, contained entries, identical bytes at
other extents, external direct branches/calls, alignment fallthroughs, and
RIP-relative references. Each external edge lists the extents owning its
target. `disassembly.txt` contains bytes and decoded instructions for every
inventoried extent plus `__libc_ifunc_impl_list`.

A symbol's `st_size` can cover only an entry stub or a prefix of a larger
shared body. It is **not** asserted to be a complete reachable function body.
For example, a successful checked stub falls through alignment into its copy
entry; mempcpy sets `RAX = destination + length` and branches into a shared
body after the destination-only return setup. The reports preserve those
edges instead of treating a 12- or 13-byte stub as a whole copy routine.
The direct-edge inventory is not a verified CFG or a functional proof.

## Dispatch and shared code

All six requested APIs have 14 source-listed implementations: `erms`,
`sse2_unaligned`, `sse2_unaligned_erms`, `ssse3`, `ssse3_back`,
`avx_unaligned`, `avx_unaligned_erms`, `avx_unaligned_rtm`,
`avx_unaligned_erms_rtm`, `evex_unaligned`, `evex_unaligned_erms`,
`avx512_unaligned`, `avx512_unaligned_erms`, `avx512_no_vzeroupper`.
Every one of the **84 entries** occurs in its actual IFUNC resolver's
RIP-relative target references, independently checked by `verify.py`.

For 12 suffixes, memcpy and memmove share the same entry and exact extent;
the corresponding checked memcpy/memmove entries also alias. **SSSE3 and
SSSE3-back have distinct memcpy and memmove entries/bodies and distinct
checked entries.** Mempcpy and checked mempcpy need their own entry/return
adapters. `__mempcpy_small@GLIBC_2.2.5` is a separate compatibility routine.

`ifunc-implementations.json` records each source enumerator's CPU eligibility
expression and source line. This diagnostic enumerator is different from the
runtime selector. `source-selectors.json` preserves the exact selector header
texts and hashes; `resolvers.json` and disassembly corroborate actual selected
target addresses. For the copy family, the selector order is:

1. Prefer_ERMS or Prefer_FSRM selects ERMS.
2. Usable AVX512F without Prefer_No_AVX512 selects an AVX512VL unaligned
   variant (ERMS if usable), or AVX512-no-vzeroupper without VL.
3. AVX_Fast_Unaligned_Load prefers EVEX when AVX512VL is usable, otherwise an
   RTM AVX variant if RTM is usable, otherwise an AVX variant unless
   Prefer_No_VZEROUPPER; ERMS chooses the paired suffix in each case.
4. Without usable SSSE3, or with Fast_Unaligned_Copy, choose SSE2 with/without
   ERMS; otherwise Fast_Copy_Backward chooses SSSE3-back, else SSSE3.

The resolver load at ELF `0x219ec8` has a GLOB_DAT relocation for
`_rtld_global_ro@GLIBC_PRIVATE`, which supplies loader CPU-feature state.
`dispatch-data.json` records ELF/Ghidra addresses and file/BSS initial values
for all `__x86_*` data symbols. In particular `__x86_rep_movsb_threshold` is
ELF `0x21a3f8` / Ghidra `0x31a3f8`; the initial value is 2048.
`__x86_shared_non_temporal_threshold` is ELF `0x2215a8` / Ghidra `0x3215a8`;
its BSS initial value is zero. Cache initialization, tunables and CPU features
can change these values before calls. Do not turn file initializers or the
host CPU's choices into universal proof preconditions.

## Existing lift comparison and lifter availability

`generated/existing-lifts.json` records every lifted instruction's address,
length, exact bytes, source annotation and independent objdump disassembly,
plus contiguous range hashes and direct targets outside the lift.

- `memcpy_amd64.v`: **313/313** boundaries and lengths match. The entry at
  ELF `0xc4870` / Ghidra `0x1c4870` is
  `memcpy@GLIBC_2.2.5 = __memcpy_sse2_unaligned = __memmove_sse2_unaligned`,
  a 44-byte prefix. The separately lifted `FUN_001c4980` is the
  `__memmove_sse2_unaligned_erms` shared body (1362-byte symbol extent,
  SHA256 `4bad378a2c97d7f0d8fca84201f2fdaaafe3974536247a0d0cf40e0b713e049b`).
  The existing proof header's broad ERMS label should be refined in e06.
- `memmove_avx_amd64.v`: **351/351** boundaries and lengths match. ELF
  `0x1a0840` / Ghidra `0x2a0840` is exactly
  `__memmove_avx_unaligned_erms = __memcpy_avx_unaligned_erms`, extent 1758,
  SHA256 `8c825128391f37a74176f64fec68c4e6ebaab5da629c076cb838cd9985983fc8`.
- After normalizing syntax/prefix/branch synonyms, the only mnemonic
  discrepancies are **12 SSE2 and 24 AVX prefetch instructions** annotated as
  `NOP` by the existing Ghidra output. They remain explicit discrepancies;
  the comparison does not validate their IL semantics or justify dropping
  architectural effects. Neither lift has a direct branch/call target
  outside its listed instructions.

The tracked `Examples/claude/lifter/lift.sh` and `pcode2coq_headless.py` exist.
Their default Flatpak Ghidra executable, `~/Desktop/pcode2coq`, and the default
Ghidra project are absent here. The README describes Ghidra 11.4.2 plus an
uncommitted `claude/amd64-fixes` checkout; the driver comment gives upstream
`b7f0122` but does not pin those modifications. No old lifter installation or
uncommitted changes were reconstructed by this inventory unit.

`Picinae_amd64.v` currently models YMM0–15 at 256 bits, with no ZMM/opmask
registers. The repository README describes dropping upper-ZMM writes for
AVX-era instructions. AVX512/EVEX copy/string variants must therefore be
checked instruction by instruction for required 512-bit/opmask semantics;
existing AVX lifts cannot establish coverage. RTM and prefetch behavior also
need explicit treatment. e06/e07 must restore an isolated pinned lifter and
use strict failure, not silently substitute instructions. This is a follow-on
engineering blocker, not a blocker to the completed ELF inventory.

## Resolved follow-on work

`unit-suggestions.json` / `.tsv` supply **242 unique suggested IDs**, exact
symbols and entry addresses, kinds, external targets and e06/e07 extraction
prerequisites. These are per distinct symbol extent, not claims of independent
complete proof bodies. Final proof dependencies must include the listed
shared-body adapters, failure callees and path support units; imported
assumptions still require their own audit.

- Keep every planned copy suffix: none of those copy-family candidates is
  absent. Add `ssse3_back`. Split both SSSE3 suffixes into actual memcpy and
  memmove body units; do not alias them by suffix.
- Map `x-copy-*` rows to exact `x-memmove-<suffix>` entries where memcpy aliases;
  SSSE3 requires both `x-memcpy-ssse3[-back]` and
  `x-memmove-ssse3[-back]`. Existing x05/x06 work can discharge paths of the
  matching SSE2/AVX bodies after e06's full provenance/semantic check.
- Split mempcpy, checked mempcpy and checked memcpy/memmove rows per actual
  entry. Use one checked-entry proof for an actual alias, while keeping
  distinct SSSE3 checked implementations and their failure paths.
- Expand family-only planned names: replace hypothetical `__memset_sse2`
  and `__memset_evex` targets with observed `*_unaligned`,
  `*_unaligned_erms` and internal helper entries. Replace hypothetical
  `__memcmp_avx2` / `__memcmp_evex` targets with `__memcmp_avx2_movbe` /
  `__memcmp_evex_movbe`, and include RTM where present. No proof unit should
  retain those absent bare spellings.
- Preserve all additional RTM, SSE2-unaligned, SSSE3, SSE4.1/SSE4.2,
  EVEX and AVX512 string entries from the generated table. `__memchr_evex_rtm`
  and rawmemchr's EVEX-RTM helper are present even though the diagnostic
  implementation list alone does not enumerate all internal helpers.
- Additional relevant hot strings confirmed from the existing Firefox
  profile include strchr, strchrnul, strpbrk, strspn, strcspn and strstr.
  They are inventoried, along with memrchr, memcmpeq, rawmemchr, stpncpy,
  strncat, bcmp/bcopy/bzero, memccpy, memmem and strcasestr. The profile is
  existing workload provenance, not a new performance measurement. Its
  pthread mutex/stdio hotspots remain separate non-string campaigns.

## Validation and ancestry

Exact commands, exit codes and log paths are in
[evidence/commands.md](evidence/commands.md). Validation passed authentication,
fresh extraction including the Ubuntu source patches, deterministic replay,
independent `nm` symbol comparison, independent `objcopy` extent hashing, all
six actual copy resolvers, and both existing lifts' boundary checks.

The prepared branch was clean at the pinned origin base before rename.
The fork branch collision check returned exit 0 and no refs. Only the new
prepared local branch was renamed; no fork branch was used as a base.
See `evidence/ancestry-before.txt`; the final post-commit audit is retained
in the allowed external unit directory and reported with the final commit.
No remote writes, pushes, PRs, or shared campaign plan/status changes occurred.
