# Exact continuation obligations

The unchanged public theorem is `strcmp_correct : strcmp_full_contract`.
The proof must establish `strcmp_invs` for actual traces from 0x192f80 with
`models arm8typctx`, original MEM/X0/X1, first-stop STOP and READ. In particular,
proving only the auxiliary word facts in this unit cannot close it.

Required auxiliary cuts and edges:

- Entry 192f80: derive X10=(q-p) mod2^64, X8=0x0101010101010101,
  p mod8; separate equal and distinct residue cases with no domain exclusion.
- Aligned loop 192fa0: use i<=K, down8/read/nonwrap facts, word-byte memory
  correspondence; no zero mask and equal words implies i+8<=K. Prefix-masked
  first word may start below p; masked bytes are 255, and all later bytes
  retain original memory. Derive a decoder pair with local stop j and a strong
  syndrome on the stop edge.
- Distinct byte loop 193018: load bytes from p+i,q+i, use exact CMP/CCMP flags,
  i<K on continue, i=K on stop; prove alignment transition into 193034 and frame.
- q setup 193034: floor q+i, prefix-one masking and zero detection in q word;
  when no NUL, record q segment nonzero for the lookahead loop. Do not infer a
  next-word memory value without an actual load.
- Lookahead 193060: strengthen only auxiliary invariants with the loaded word
  and lookahead state. Read q's next aligned word and q+i unaligned word;
  establish relationship of its zero mask shifted by (64-8*((q+i) mod8)) mod64
  to the concatenated original q bytes. Handle zero masks with borrow-induced
  later high-bit false positives. Continue only after all eight current
  comparisons are nonzero/equal, with i+8<=K. Terminal q word 193090 fills
  inaccessible comparison-tail bytes with zero; its earliest stop and any
  prior mismatch must still refer to original memory.
- Decoder 192fc4: relate the exact generated REV expression to byte reversal;
  locate CLZ in [8*j,8*j+7] and derive the equal high-bit prefix needed by
  strcmp_fix_shifted_byte_sign. On common NUL derive CLZ=8*j, so following
  bytes cannot pollute the output. Relate modulo64 shift to these bounds,
  then LSR56 and SUB to signed32 W0 sign. Maintain frame at RET192fe4.
- Byte suffix: use first-stop bytes in X2/X3, then checked SUB segment to
  RET1930b0. Compose all cuts and project any stronger auxiliary invariants
  to unchanged public strcmp_invs. Query the resulting main constant.

All paths and all seven original sample entry witnesses remain in scope.
The weak-decoder counterexample from the prerequisite is not a reachable
entry-state counterexample and cannot justify rejecting the public contract.
