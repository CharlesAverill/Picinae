# x07 dispatch evidence

Source of evidence: unchanged `Examples/claude/memmove_avx_amd64.v`;
addresses below are normalized instruction offsets. This is source inspection,
not an independently validated binary disassembly or execution certificate.

- Entry `0/4` establishes RAX=d. `13` saves the original 32-byte head.
- `192/199`: n greater than entry-memory qword 0x31a3f8 branches to704.
  This is the proposed theorem's strategy boundary, with n>256.
- `704..713`: RCX=d-s modulo2^64. Under d<s and s+n<=2^64,
  RCX>=n; backward branch496 cannot be taken.
- `719` saves d in R8; `722/729` compares n with qword0x3215a0.
- Below stop: `731/741` reads bit0 of dword0x321598.
  Clear: `640` saves second head vector, `645/651` selects source-aligned
  REP676 if low32(d-s)&0xe00=0, otherwise destination-aligned REP778.
  Set: `743/746` sends low32(d-s)>0xffffffc0 directly to363. Other
  distances save second head at752 then use destination alignment757..778.
  This unsigned low32 test includes close gaps1..63, and is not equivalent
  to a simple full64 gap bound for arbitrary large inputs.
- At/above stop: `800/807` rereads REP threshold. Under entry n>T1, the
  branch337 cannot be taken. `813` negates RCX, yielding s-d. `816/819`
  tests n>s-d; genuine forward overlap therefore jumps to363 before825
  and before NT staging stores830/834. No NT threshold is read here.
- Fallback363 saves the original last128 bytes in YMM5..8, and aligns
  destination to next32-byte boundary. Loop416 loads four vectors before
  storing them. Its final writes467..486 are n-32,n-64,n-96,n-128,0 in
  that order. These ranges may overlap each other and the last row.
- REP676/778 decrements RCX once per byte and advances both pointers with
  DF=0, looping at the same instruction. Zero RCX jumps to678/780.
  Saved original head vectors are stored at0 then32, followed by
  VZEROUPPER and pre-RET cuts692/794. The fallback pre-RET cut is493.

Every tunable read on these paths happens before the first store. The theorem
needs no disjointness between globals and destination and makes no claim that
their bytes are unchanged after stores. Threshold0x3215a8 is not read in this
strategy. The initial theorem leaves n<=T1 and n>T2 to x10 (x03 only handles
n<=both), and n>=2^63 to x09. Within the stated overlap domain aboveT1,
the NT-selection guard rejects streaming stores even when n>=stop. This is
an intended proof obligation of x07, not something certified by this note.

No permissions/CPU-feature predicates are silently postulated: the existing
IL uses total memory and modeled instructions; its partial-correctness theorem
assumes a typed state and, at a RET corollary, an actual `exec_prog` trace.
It does not establish a trace exists, runs without faults, terminates, or
matches physical hardware. The entry witnesses concern state satisfiability.
