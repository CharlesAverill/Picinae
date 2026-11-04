# Official FreeRTOS V11.1.0 Cortex-M0 extractions

These are finite per-function instruction maps from the official kernel fixture
in `../freertos/cortex-m0`. See [coverage.md](coverage.md) for all 41 actual
entries and their call-closure blockers. **Full e05 is partial**: all planned
bodies extract, but 24 call closures reach helpers rejected by the strict e03
frontend. No function correctness proof is included.

The exact ELF SHA256 is
`5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`;
kernel release V11.1.0 is commit
`dbf70559b27d39c1fdb68dfb9a32140b6a6777a0`. Compiler, config, link map and
source provenance are pinned by the e04 fixture. `abi.json` includes all
compiled field offsets and object/global addresses. Each `<fn>.json` records
absolute instruction addresses and opcodes, symbol/Thumb metadata, source and
body hashes, all PC-relative literal words, globals resolved from literals,
return candidates, direct/indirect control edges, and transitive prerequisites.
Mapped data inside the symbol extent is retained, including complete literal
words outside the extent when a PC-relative load needs them.

`<fn>_armv6m.v` is generated. Future manually authored function proofs belong in
`armv6m_<fn>_proof.v`, separate from these artifacts. Use `<fn>_armv6m_prog`:
it returns `None` outside the listed instruction starts. `<fn>_armv6m` is a
halfword lookup, with zero as its default; the default is not executable code.
The generated `end_...` follows e03's convention: last included halfword
address, not an exclusive code bound. The JSON `end_exclusive` is the symbol
extent; executable starts are explicitly listed.

Each generated file checks decoder acceptance, program typing, Thumb entry
metadata, and every resolved literal load with `Qed`. These facts establish
properties of the IL extraction; they do not establish execution safety,
functional behavior, callee preservation, termination, interrupt stability,
or a refinement of ARM hardware. Literal folding assumes immutable pool bytes.
Finite maps do not include callees. Whole-call proofs must compose actual maps
and proved contracts; they cannot execute an absent callee as a no-op.

Return candidates record `BX LR` or `POP {..., PC}` instruction sites, not a
return theorem: the caller must supply valid stack memory, an odd Thumb return
address and appropriate register/stack invariants. Ordinary instruction
fallthrough is implicit in each instruction's width. Conditional branches list
their fallthrough; BL lists its return site. No feasible-path analysis is
claimed. The closure inventory includes assertion-failure paths even if a
future precondition might exclude them.

Build all 41 full `.vo` files, using the existing isolated environment:

```bash
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c '
    ulimit -v 2000000
    ulimit -s 65536
    dune build --cache=disabled -j1 --display short @Examples/FreeRTOS/freertos-lifts
  '
```

Each function also has an alias, for example
`@Examples/FreeRTOS/freertos-vListInitialiseItem`, or request
`Examples/FreeRTOS/vListInitialiseItem_armv6m.vo` directly. Dune uses the root
explicit module selection and e00's single recursive Picinae mapping. Nothing
is added to `@smoke`.

Regeneration and verification commands, exact exits, assumptions output and
ancestry evidence are in [the e05 notes](../../notes/e05-freertos-lifts/README.md).
The extraction driver consumes the e04 ELF read-only and calls the unchanged
strict e03 frontend individually. Rejected helper diagnostics are in
`helper-rejections.json`; `helpers.json` inventories the 33 reached unextracted
helper bodies. Diagnostic instruction analysis never emits a program for a
rejected helper and does not modify the ISA's inherited system approximations.

Remaining engineering models should be small and explicit: PRIMASK/CPS and
nesting; barriers and NVIC/PendSV side effects; exception/context-switch entry
and return; assertion-failure WFI behavior or proved path exclusion; and finite
call-map composition. Ordinary helper functions and newlib dependencies need
their own extractions and proved functional/ABI/frame contracts. No IRQ
contract is assumed by this unit.
