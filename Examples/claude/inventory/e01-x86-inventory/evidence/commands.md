# Verification commands and exits

Working directory for all repository commands:
`/home/charles/.t3/worktrees/Picinae/t3-82f6e4d5`.
Commands were run on 2026-11-03. Tool versions are in `tool-versions.txt`.
`PYTHONDONTWRITEBYTECODE=1` prevents repository bytecode artifacts. The unit
venv is stdlib-only; nothing was installed globally. No glibc target execution,
Rocq proof checking, or Dune build is part of this binary-inventory unit.

## Authenticated workflow

```sh
Examples/claude/inventory/e01-x86-inventory/run.sh --offline > Examples/claude/inventory/e01-x86-inventory/evidence/run.log 2>&1
```

Exit **0**. Log: `run.log`. All nine downloads pass their locked size/SHA256
checks. GnuPG verifies the historical Ubuntu archive signature; the signed
release authenticates Packages/Sources, which authenticate the two binary
packages, the dsc and its source members. Runtime SHA256 and debug build ID
match exactly. Generation reports 398 symbol records, 242 extents and 210
source-listed implementation entries, all present.

The downloader itself was also tested with an **empty download cache**:

```sh
PYTHONDONTWRITEBYTECODE=1 /home/charles/code/friends/.toolchains/e01-x86-inventory/venv/bin/python3 Examples/claude/inventory/e01-x86-inventory/retrieve.py --root /home/charles/code/friends/.toolchains/e01-x86-inventory/network-check > Examples/claude/inventory/e01-x86-inventory/evidence/network-retrieval.log 2>&1
```

Exit **0**. The new `network-check/` directory had no downloads; its runtime,
debug and source paths were links to already extracted data within the same
per-unit directory. The log records all nine actual GET requests, download
checksum checks and successful signature/index/package authentication. The
fresh extraction check below independently tests package/source extraction.
Persistent provenance manifests are kept in the repository generated reports.

Exploratory online package retrieval was performed with `curl -fsSL --retry 2 --max-time
120` against the exact URLs now recorded in `downloads.lock.json`, with
outputs exclusively under the per-unit `downloads/` directory; every final
URL returned exit **0**. The same downloads can be repeated by `run.sh` with
an empty per-unit cache. No host libc path is an input to either script.

## Fresh extraction and source patching

A fresh child environment was prepared using:

```sh
mkdir -p /home/charles/code/friends/.toolchains/e01-x86-inventory/replay
ln -s ../downloads /home/charles/code/friends/.toolchains/e01-x86-inventory/replay/downloads
PYTHONDONTWRITEBYTECODE=1 /home/charles/code/friends/.toolchains/e01-x86-inventory/venv/bin/python3 Examples/claude/inventory/e01-x86-inventory/retrieve.py --offline --root /home/charles/code/friends/.toolchains/e01-x86-inventory/replay > Examples/claude/inventory/e01-x86-inventory/evidence/fresh-extraction.log 2>&1
```

Exit **0** for each. Log: `fresh-extraction.log`, including the exact executed
`dpkg-deb -x` and `dpkg-source --no-check -x` commands and every applied source
patch. `--no-check` suppresses the separate uploader-key dsc signature check;
the dsc and all members have already been authenticated through Ubuntu's
archive-signed Sources index. No configure/build scripts run.

```sh
PYTHONDONTWRITEBYTECODE=1 /home/charles/code/friends/.toolchains/e01-x86-inventory/venv/bin/python3 Examples/claude/inventory/e01-x86-inventory/inventory.py --root /home/charles/code/friends/.toolchains/e01-x86-inventory/replay --output /home/charles/code/friends/.refs/picinae-llm-proofs/units/e01-x86-inventory/replay-generated > Examples/claude/inventory/e01-x86-inventory/evidence/replay-inventory.log 2>&1
diff -r Examples/claude/inventory/e01-x86-inventory/generated /home/charles/code/friends/.refs/picinae-llm-proofs/units/e01-x86-inventory/replay-generated > Examples/claude/inventory/e01-x86-inventory/evidence/replay-diff.log
```

Both exits **0**. Logs: `replay-inventory.log`, `replay-diff.log` (empty:
byte-identical reports after independent extraction of runtime, debug and
patched Ubuntu source).

## Independent verification

```sh
PYTHONDONTWRITEBYTECODE=1 /home/charles/code/friends/.toolchains/e01-x86-inventory/venv/bin/python3 Examples/claude/inventory/e01-x86-inventory/verify.py > Examples/claude/inventory/e01-x86-inventory/evidence/verify.log 2>&1
```

Exit **0**. Log: `verify.log`. Checks the output checksum manifest; compares
all selected debug symbols against the independent `nm -a -S --defined-only`
reader; checks all 242 extent hashes against an independent `objcopy
--dump-section` extraction of `.text`; checks all 84 copy entries against both
source eligibility lists and the six runtime resolver target references;
preserves the distinct SSSE3 copy/check bodies; and checks both lifts' complete
instruction-boundary/length matches and the explicit prefetch discrepancies.
The objcopy output ELF copy and section data are written only in a temporary
`/tmp/e01-section-*` directory, which is removed on exit.

## Repository checks

```sh
sh -n Examples/claude/inventory/e01-x86-inventory/run.sh
(cd Examples/claude/inventory/e01-x86-inventory/generated && sha256sum -c SHA256SUMS)
git diff --check
git diff --cached --check
```

All exits **0**. Log: `repository-checks.log`. Syntax compilation of Python
sources used `compile(source, path, 'exec')`, without writing pycache.
`lifter-assessment.log` records tracked driver blob provenance, missing default
external lifter paths/Flatpak executable, and current SIMD register widths.

## Resolved exploratory failures and remaining limits

- Sandbox DNS failed for the initial fork collision check. The authorized
  network retry returned exit **0** and no matching refs. The first local
  branch rename hit read-only Git metadata; its filesystem-authorized retry
  returned exit **0**.
- The live Ubuntu runtime/dsc URLs returned HTTP **404** (`curl` exit **22**).
  Snapshot pool URLs succeeded with the exact required SHA256. The first
  authentication attempt with a jammy-updates index stopped with Python exit
  **1**, because that index contained `.11`. The final jammy-proposed index
  authenticates `.12`; both target version and binary hash remain unchanged.
- `/usr/bin/python3 -m venv` initially exited **1** because ensurepip is absent.
  `--without-pip` works and installs nothing; no external Python packages are
  needed or used.
- The first independent verification exited **1** because objcopy, when given
  no output ELF argument, attempted a temporary write beside the input ELF
  and the sandbox refused it. The fixed command supplies an explicit `/tmp`
  output ELF; the check now exits **0**, and the target hash is unchanged.
- The initial staged whitespace check flagged trailing spaces emitted by
  readelf. The generator now strips trailing spaces from the ELF-header
  report; deterministic replay and the staged whitespace check pass.
- The existing lift annotations have 12 SSE2 and 24 AVX NOP/prefetch mnemonic
  discrepancies. Those are recorded findings, not hidden by normalization.
  IL semantics and original lifter reproducibility are not certified.

Theorem checks / `Print Assumptions`: **N/A**. Dune: **N/A**, as assigned.
There is no new function correctness claim. Follow-on lifter availability and
AVX512/EVEX semantic coverage are described in the unit README.
