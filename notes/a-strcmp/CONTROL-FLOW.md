# Map inspection before the first proof build

The immutable input is `Examples/claude/lifter/scalar_ccmp/e30_strcmp_arm8.v`
with SHA256 `2b7b58a310afd013b2dae9e2953786404640796734fc6ae39cf309f0a6568dc3`.
Its adjacent manifest pins Ubuntu AArch64 glibc 2.35-0ubuntu3.15, ELF SHA256
`79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06`.
Entry is `0x192f80`, size 308 bytes, 77 instruction addresses.

The brief says three exits, but the actual map has exactly two RETs:
`0x192fe4` and `0x1930b0`. The former is shared by all word paths.
There are no calls, vector instructions, tunable reads, or stores.

- `0x192f80..0x192f98`: compute q-p, repeated-one mask, p alignment;
  dispatch on `(q-p)&7`, then `p&7`.
- `0x192fa0..0x192fb8`: aligned pair of eight-byte loads, subtract-one
  zero detector, BICS and conditional compare; loop only for equal words
  without a detected NUL.
- `0x192ff0..0x193010`: align p downward, load both words at the same
  displacement, mask all bytes before p to 0xff, join at `0x192fa8`.
- `0x193014..0x193030`: unequal-alignment byte prefix; increment both
  pointers until p is aligned or a difference/NUL sends execution to
  `0x1930ac` and then the byte RET `0x1930b0`.
- `0x193034..0x19305c`: align q downward, load its leading aligned word,
  mark irrelevant prefix bytes nonzero, detect a possible NUL; branch
  to terminal partial-word handling or set the lookahead displacement.
- `0x193060..0x19308c`: load the next aligned q word first, then the
  unaligned q comparison word and aligned p comparison word. Continue on
  equal comparison words and no NUL in the lookahead. Otherwise shift the
  zero mask into the comparison word and form the XOR/zero syndrome.
  A nonzero syndrome goes to the common decoder; a zero syndrome falls
  into terminal partial-word handling.
- `0x193090..0x1930a8`: load the next p word, shift the q word and NUL
  detector past the prefix, form the syndrome, jump to the common decoder.
- `0x192fc4..0x192fe4`: REV syndrome and both comparison words, CLZ the
  syndrome, variable left shifts (low six shift-count bits), extract the
  high byte, subtract in X0, RET. The shift need not be a byte multiple.
  Therefore the full contract specifies the signed32 return sign, not exact
  equality to the source-byte difference.

The formal domain uses actual A_READ bits for two conservative half-open
envelopes: `[down8(p),down8(p+K)+8)` and
`[down8(q),down8(q+K)+16)`, with both upper endpoints strictly below 2^64.
The q suffix explicitly includes one lookahead word. These bounds do not
exclude either alignment dispatch or page-end addresses, but they do require
readability of any additional pages in that envelope. They do not assert
that a C string necessarily owns those padding bytes. The proposed proof
still has to establish that every actual load is covered by these envelopes.

The invariant at the decoder relates local first-stop bytes to original
memory. Its syndrome predicate requires all XOR bits to be included, no
nonzero byte before the first stop, and a nonzero stop byte. These are proof
obligations at internal cuts, never caller hypotheses or assumed instruction
lemmas. Loop invariants retain the original pointer displacement, progress
bounded by K, relevant alignment, and frame. The lookahead invariant also
records nonzero bytes in the already examined prefix of the current q word.

The main statement is `strcmp_full_contract`, proved by the attempted
`strcmp_correct`. It uses `satisfies_all` and stops before RET. No termination,
executed return, hardware, page-fault freedom or verified lifting conclusion
is claimed.
