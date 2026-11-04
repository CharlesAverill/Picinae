# High-size dispatch analysis and remaining counterexample obligation

Initial author: gpt-6-astra, xhigh/default. Analysis of the accepted unchanged
encoded IL, not a binary validation or a completed counterexample theorem.

Write Q=2^64, H=2^63, delta=(d-s) mod Q. For genuine forward overlap and
nonwrapping endpoints, d<s<d+n and s+n<=Q imply n<=delta, so the unsigned
JC at 318 is not taken. With both initial threshold values >=n, entry
reaches 337. For n>=H, s<=H and s-d<H, hence delta>=H. At 337--344 the
sign bit is ((delta+n) mod Q XOR delta)>>63. It is 1 exactly when
n-(s-d)<H. Instructions 348 and 354 add that bit to (delta & 0xf00), in
32 bits; 357 branches backward to 501 exactly when the sum is zero.
No true signed JG/JL occurs here: the signed-domain issue is the explicit
XOR-and-shift sign-change heuristic. The row loop tests are unsigned.

The ordinary forward branch can therefore be proved for a nonzero sum
without imposing n<H. The initial main theorem does exactly this, retaining
x03's copied-byte sets, unread-source lemma, head/tail snapshots, RAX/RSP,
external memory frame, and callee-saved frame. It does not silently equate
that nonzero-sum domain with all high sizes.

Counterexample candidate outside that branch domain:

- d=4096, s=8192, n=H+4096=9223372036854779904.
- d+n=H+8192 and s+n=H+12288 are both below Q.
- delta=Q-4096; (delta+n) mod Q=H; both sign bits are 1.
- delta & 0xf00=0, so the branch at 357 selects 501.
- Set both initial threshold quadwords to n (or a larger representable N).
  This bypasses REP and NT and is consistent with the memory model.

Candidate finite corruption sequence (not a machine-checked execution):
At 511/533, the first row destination is
L=align_down_32(d+n-129)=d+n-160=H+8032.
The row loads at 544/549/554/559 read offsets +96,+64,+32,+0 from L+4096;
the stores at 567/572/577/582 write [L,L+128). The loop decrements both
pointers by 128 and branches at 593. After 32 decrements, the row loads
[L,L+128), which has already been overwritten, and stores [L-4096,L-3968).
Choose original m[L]=1 and zero other bytes in these high source rows, while
setting the two low-address threshold quadwords as above. The first row
writes zero at L; the 33rd row consequently writes zero at L-4096, where
memmove requires the ORIGINAL m[L]=1. Saved head vectors and the final
saved tail vector do not cover L-4096, and later descending rows are below
that address. A complete counterexample needs an encoded execution prefix,
byte-load/store proofs, persistence through the suffix, and a return or
suitable total-execution argument. Those obligations must not be replaced
by merely assuming the output or an unproved callee contract.

The new numerical example and map equation, even if checked, are only a
domain/branch diagnostic; they do not certify this candidate corruption
sequence. An all-high-size correctness statement cannot be claimed from
the conditional forward-loop theorem. A Sol continuation should preserve
its statements, complete the exact dispatch normalization, and resolve the
zero-sum region with a proper encoded-IL counterexample or justified result.
