# CoqEtTu

Note: Project name is a placeholder that is unlikely to conflict with any other symbols, useful for renaming.

This directory hosts the LLM-generated correctness theorems and proofs for musl-1.2.6-r6 downloaded from the Alpine Linux repository.
These files are not checked into this git repo, each file's sha256sum is in ./sha256sums.

Each LLM is to work in its own directory and not peek in nor write to the other directories.
We have the following directories:

  * claude/ for Claude models (e.g., Opus 5.5)
  * kimi/ for Kimi models (e.g., Kimi 3.1)
  * codex/ for Codex models (e.g., GPT-6.1-Sol)
  * grok-bot/ for Grok models

When verifying a musl library, place all of its Rocq artifiacts in `<llm-dir>/<ISA name>/`.
For example, for Claude verifying `alpine_musl/x86/lib/libc.musl-x86.so.1`, the artifacts would go in `claude/x86/`.
Kimi verifying `alpine_musl/armv7/lib/libc.musl-armv7.so.1` would place its artifacts in `kimi/armv7`.

Function definitions should be separate from the proof artifacts, and generally useful tactics and theorems should go in a shared library (again, isolated to the LLM so there is no cross-LLM reuse).

Each proof file should contain a proof header modeled after the one in `proof_header_template.v`.

The following are the LLM-to-architecture assignments:

  * Claude-x86_64 (alpine_musl/x86_64/lib/libc.musl-x86_64.so.1)
  * Codex-x86 (alpine_musl/x86/lib/libc.musl-x86.so.1)
  * Kimi-armv7 (alpine_musl/armv7/lib/libc.musl-armv7.so.1)
  * Grok-aarch64

Useful Picinae-related skills for lifting and verifying are located in `../skills/`.

Each LLM should maintain a ROADMAP.md in its directory.  It should list open problems, next steps, solved problems, and useful lessons learned.
