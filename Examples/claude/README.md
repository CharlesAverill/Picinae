# amd64 glibc proofs

Machine-checked Picinae correctness proofs for functions lifted from the
system's own C library: `/lib/x86_64-linux-gnu/libc.so.6`, glibc
2.35-0ubuntu3.12 (sha256 `9b846df0…62c4d9`).

These specifications and proofs were written by Claude Opus 5.5
(`claude-opus-5-5`), an AI model by Anthropic, and checked by Rocq 9.1. Each
proof file starts with a header that gives the function's semantics, quotes
the man page, names the model, and states the input/output specification in
English.

## Layout

| File | Contents |
|---|---|
| `<fn>_amd64.v` | Picinae IL program, lifted by Ghidra + pcode2coq (generated; don't edit) |
| `amd64_<fn>_proof.v` | Specification and proof for `<fn>` |
| `amd64_common.v` | Shared lemmas and tactics (bit-blasting, bounded-loop reasoning, byte scanning, ...) |
| `amd64_cstring.v` | C-string predicates (`strspn`/`strcspn` as relations) and frame-agreement lemmas |
| `amd64_ieee.v` | IEEE-754 field decomposition (`exp64`, `man64`, ...), the borrow lemmas `shr_msub64`/`shr_msub32`, and the x87 80-bit lemmas (`exp80`, `isnanl_spec`, `isinfl_spec`) |
| `amd64_termios.v` | `struct termios` speed checks shared by `cfsetospeed`/`cfsetispeed` (`speed_ok`, the lifted range test) |
| `amd64_memcpy_sets.v` | `cpy`: the set of destination offsets a copy has written so far; one lemma per 16-byte store (`cpy_store`) and per non-overlapping load (`cpy_load`) |
| `amd64_memcpy_lemmas.v` | the head/tail store patterns of small memcpy sizes, each proved by a chain of `cpy_store` |
| `lifter/` | Headless lifting driver (`lift.sh`, `pcode2coq_headless.py`) and p-code dump helpers |

Build with `make` (needs `../..` built first, Rocq ≥ 9). Several proofs need
4–10 GB at `Qed` (`lfind`, `bsearch`, `strspn_sse2`, `strcspn_sse2`, the
memcpy proofs), so on a 16 GB machine build with `make -j1` or `-j2`.

## Proved functions

All theorems are complete except where noted, with no `Admitted`.  Every function also has
theorems for well-typedness, non-writable code, and preservation of the
callee-saved registers (plus memory preservation for functions that don't
write memory).

| Function(s) covered | Proof file | Main property |
|---|---|---|
| `toascii` | `toascii` | RAX = c & 0x7f |
| `isascii` | `isascii` | RAX = 1 iff 0 ≤ c ≤ 127 (signed) |
| `htonl`, `ntohl` | `htonl` | RAX = bswap32; storing it little-endian gives the big-endian encoding |
| `htons`, `ntohs` | `htons` | AX = bswap16, plus the exact full-register effect |
| `abs` | `abs` | RAX = \|j\| mod 2^32; exact \|j\| for j ≠ INT_MIN |
| `labs`, `llabs`, `imaxabs` | `labs` | 64-bit version of the above |
| `div` | `div` | quot/rem in EAX/upper half, rounded toward zero, quot·d + rem = n |
| `ldiv`, `lldiv`, `imaxdiv` | `ldiv` | quot in RAX, rem in RDX |
| `ffs` | `ffs` | 1-based index of lowest set bit (BSF loop) |
| `ffsl`, `ffsll` | `ffsl` | 64-bit version |
| `insque`, `remque` | `insque`, `remque` | exact final memory, plus link-level corollaries under non-aliasing |
| `swab` | `swab` | pairwise byte swap of `n & ~1` bytes, frame elsewhere (loop) |
| `pthread_equal` | `pthread_equal` | 1 iff equal |
| `mbsinit` | `mbsinit` | 1 iff NULL or `__count == 0` |
| `gnu_dev_major/minor/makedev` | `gnu_dev_*` | glibc dev_t encoding; major/minor invert makedev; makedev injective |
| `inet_netof`, `inet_lnaof` | `inet_netof`, `inet_lnaof` | classful split; the network and host parts recombine to the address |
| `cfgetospeed`, `cfgetispeed` | `cfgetospeed`, `cfgetispeed` | `c_cflag & (CBAUD\|CBAUDEX)`, with glibc's IBAUD0 case |
| `sigemptyset` | `sigemptyset` | clears signals 1..64; NULL → errno = EINVAL |
| `sigisemptyset` | `sigisemptyset` | **does not meet its spec**; see below |
| `wcschrnul` | `wcschrnul` | first wc or the terminator (loop) |
| `__strspn_c1`, `__strspn_c2` | `strspn_c1`, `strspn_c2` | strspn with a 1- or 2-character accept set (loops) |
| `__strcspn_c1`, `__strcspn_c2` | `strcspn_c1`, `strcspn_c2` | strcspn with a 1- or 2-character reject set (loops) |
| `__strpbrk_c2` | `strpbrk_c2` | strpbrk with a 2-character set (loop) |
| `__sigismember` | `sigismember_internal` | bit (sig-1) mod 64 of word (sig-1)/64 |
| `seed48` → `seed48_r` | `seed48` | **non-leaf**: callee proved first, caller uses it via `perform_call` |
| `memcpy` (SSE2, `memcpy@GLIBC_2.2.5` entry) | `memcpy` | for n ≤ 128: dest[0,n) = src[0,n), everything else unchanged, even when the buffers overlap (`memcpy_correct_small`, `memcpy_correct_mid`); the loop paths for n > 128 are in progress |
| `isnan`, `isnanf` | `isnan`, `isnanf` | RAX = 1 iff the bit pattern is a NaN (exponent all ones, mantissa ≠ 0; `is_nan64`/`is_nan32` in `amd64_ieee.v`) |
| `isinf`, `isinff` | `isinf`, `isinff` | RAX = 1 for +inf, 0xffffffff (−1) for −inf, else 0 (branch-free sign trick, proved bit by bit) |
| `finite`, `finitef` | `finite`, `finitef` | RAX = 1 iff the exponent is not all ones; the red-zone spill below RSP is part of the spec |
| `finitel` | `finitel` | RAX = 1 iff the 15-bit exponent of the x87 long double (at RSP+16) is not all ones |
| `isnanl` | `isnanl` | RAX = `isnanl_spec`: 0xffff for a NaN or pseudo-NaN, \| 1 for an *unnormal* (exponent ≠ 0, integer bit clear); glibc counts unnormals as NaNs |
| `isinfl` | `isinfl` | RAX = `isinfl_spec`: 1 / 0xffffffff for ±inf (exponent 0x7fff, significand 0x8000000000000000), else 0; main theorem **Admitted (QED-SLOW)**: tactics take ~10 s, the kernel check > 5 min (power-of-two literal 2^31) |
| `cfmakeraw` | `cfmakeraw` | the man page's flag masks on c_iflag/c_oflag/c_cflag/c_lflag, plus c_cc[VTIME] = 0, c_cc[VMIN] = 1; the single 16-byte store is split into four dword stores (`setmem16_split`) |
| `cfsetospeed`, `cfsetispeed` | `cfsetospeed`, `cfsetispeed` | valid speed (`speed_ok`: inside CBAUD, or B57600..B4000000) → c_[io]speed := speed, CBAUD bits of c_cflag := speed (cfsetispeed: speed 0 sets glibc's private IBAUD0 bit instead); else EINVAL.  The binary also accepts 0x1000 (BOTHER) |
| `copysign`, `copysignf` | `copysign`, `copysignf` | low 64 (32) bits of YMM0 = magnitude bits of x, sign bit of y; the `.rodata` masks are a precondition |
| `inet_makeaddr` | `inet_makeaddr` | RAX = byte-swapped classful net/host combination (`makeaddr`), the converse of `inet_netof`/`inet_lnaof` |
| `sigfillset` | `sigfillset` | first word := 0xfffffffe7fffffff: every signal 1..64 **except 32 and 33** (`sigfillset_members`); NULL → EINVAL |
| `sigaddset`, `sigdelset` | `sigaddset`, `sigdelset` | `N.setbit`/`N.clearbit` of bit n−1; EINVAL for n ∉ 1..64, NULL set, **and n = 32 or 33** (reserved by NPTL; not in the man page) |
| `sigismember` | `sigismember` | RAX = bit n−1 of the first word; EINVAL for n ∉ 1..64 or NULL (32 and 33 are accepted) |
| `sigandset`, `sigorset` | `sigandset`, `sigorset` | first word of dest := AND / OR of the operands' first words; any NULL → EINVAL |
| `a64l` | `a64l` | RAX = value of the leading ≤ 6 base-64 digits mod 2^32; **does not meet its spec**, see below |
| `__strspn_sse2` (`strspn` without SSE4.2) | `strspn_sse2` | RAX = strspn(s, accept) (`spn`); memory unchanged outside the 256-byte table below RSP (three loops: REP STOSQ, table fill, scan) |
| `__strcspn_sse2` (`strcspn` without SSE4.2) | `strcspn_sse2` | RAX = strcspn(s, reject) (`cspn`); same frame |
| `bsearch` | `bsearch` | **non-leaf, function-pointer callee**: under a comparator contract and a sorted (partitioned) array, returns a matching element or NULL only if none matches |
| `lfind` | `lfind` | **non-leaf, function-pointer callee**: returns the *first* matching element, or NULL only if none matches |
| `strsep` | `strsep` | **non-leaf, PLT callee** (`strcspn`): returns the token; NUL-terminates it and advances `*stringp`, or sets it to NULL |
| `strtok_r` | `strtok_r` | **non-leaf, two PLT callees** (`strspn`, `strcspn`): skips delimiters, returns the next token or NULL, and updates `*saveptr` exactly |
| `strdup` | `strdup` | **non-leaf, three PLT callees** (`strlen`, `malloc`, tail-call `memcpy`): NULL if malloc fails, else jumps to `memcpy(d, s, strlen(s)+1)` with `d` a fresh heap block; memory outside the heap is unchanged |
| `strndup` | `strndup` | **non-leaf** (`strnlen`, `malloc`, tail-call `memcpy`): NULL if malloc fails; else stores the NUL at d[n] and jumps to `memcpy(d, s, n)` with n = strnlen(s, maxlen) and [d, d+n+1) in the heap |
| `memccpy` | `memccpy` | **non-leaf** (`memchr`, then tail-call `mempcpy` or call `memcpy`): if c occurs first at offset k < n, jumps to `mempcpy(dest, src, k+1)`; otherwise copies n bytes via memcpy and returns NULL |
| `sigabbrev_np`, `sigdescr_np` | `sigabbrev_np`, `sigdescr_np` | RAX = table[sig] (8-byte load) for 0 ≤ sig ≤ 64, else NULL |
| `srand48_r` | `srand48_r` | the four stores into `drand48_data`; afterwards Xi = seed·2^16 + 0x330E, a = 0x5DEECE66D, c = 0xB, init = 1 (`srand48_r_fields`) |
| `lcong48_r` | `lcong48_r` | Xi := param[0..2], a := param[3] + param[4]·2^16 + param[5]·2^32, c := param[6], init := 1, assuming param and the buffer don't overlap |
| `rand_r` | `rand_r` | equals glibc's C reference (`rand_r_ref`) and stays ≤ RAND_MAX; main theorem **Admitted (QED-SLOW)**: tactics take ~10 s, the kernel check takes > 10 min |

`bsearch` and `lfind` call their comparator through a function pointer, and
`strsep`/`strtok_r` call `strspn`/`strcspn` through the PLT, whose
IFUNC-selected targets aren't part of the lifted program.  These proofs place
arbitrary code (`cp`, any code map) at every address outside the function and
assume only a contract for the code entered at the callee address (a fixed C
for the comparator, the PLT stub for the string functions).  The contract is
stated in the shape `perform_call` consumes.  It also requires the callee to
leave memory unchanged, which idealizes callees that write below their own
stack pointer.  `malloc` is the exception: `strdup` is parameterized by an
abstract heap region, and malloc may change only heap bytes and must return
NULL or a block inside the heap.

Each contract comes with a `*_satisfiable` theorem showing that some
well-typed `cp` meets it.  A contract that no `cp` can meet would make the
main theorem vacuously true.  An earlier version of the bsearch/lfind
contracts had exactly this bug: the callee's entry invariant required the
return address on the stack (`mem Ⓠ[sp] = RET_SITE`), but the contract didn't
assume it, so a single-state trace refuted the contract.  The contracts now
take every entry-invariant conjunct as a hypothesis.  For bsearch/lfind the
witness is a comparator that returns 0, and for strdup's malloc it is a
malloc that returns NULL.  For strlen/strspn/strcspn it is a callee that
spins forever (weaker evidence, but it rules out the contradiction).

Non-leaf functions are lifted into one program with global addresses
(`lifter/lift.sh seed48+seed48_r=seed48_amd64`), following
`../arm8_strcasecmp_proof.v`.  `wip/` holds unfinished work (`__sigaddset`,
a field-level corollary for `seed48`).

The loop proofs are partial correctness: the property holds whenever the
function returns.

## Finding: `sigisemptyset` ignores signals 33–64

glibc 2.35's `sigisemptyset` tests only the low 32 bits of the signal set.
The internal `__sigisemptyset` stores an `unsigned long` word in an `int`, so
the 4-byte test `mov edx, [rdi]; test edx, edx` is all that survives
compilation. Any set whose members are all real-time signals (≥ 33) is
therefore reported as empty, which contradicts the man page ("returns 1 if
set contains no signals"). `amd64_sigisemptyset_proof.v` proves:

* `sigisemptyset_correct`: the binary's exact behavior;
* `sigisemptyset_ignores_rt_signals`: no member in 1..32 ⇒ result 1;
* `sigisemptyset_rtmin_counterexample`: `{SIGRTMIN}` is non-empty, yet the
  result is 1;
* `sigisemptyset_sound_low`: the result is correct for sets of signals 1..32.

The behavior was confirmed by running the system libc. A C program that calls
`sigaddset(&s, SIGRTMIN)` on an empty set then gets `sigisemptyset(&s) == 1`.

## Finding: `a64l` does not sign-extend

The man page says that when `long` is wider than 32 bits, "a64l()
sign-extends its 32-bit result".  glibc 2.35 builds the result in a 32-bit
register and returns it with `mov rax, r8`, so bits 32–63 are always zero.
`amd64_a64l_proof.v` proves:

* `a64l_correct`: RAX = (Σ val(s[i])·64^i over the leading digits) mod 2^32;
* `a64l_zero_extends`: the result is always < 2^32;
* `a64l_no_sign_extension`: for `".....0"` the result is 2^31, not the
  sign-extended −2^31.

Running the system libc agrees: `a64l(".....0")` returns 2147483648.  The
proof also checks, byte by byte, that glibc's 77-entry digit table matches the
man page's alphabet.

## Lifting pipeline

1. `~/.cache/picinae_lift/proj` holds a Ghidra 11.4.2 project with libc
   imported and auto-analyzed. The flatpak Ghidra is used because it ships
   JDK 21; PyGhidra was installed into its venv, with JPype1 from PyPI.
2. `lifter/lift.sh fn=coqname ...` runs `pcode2coq_headless.py`, which calls
   pcode2coq's `liftFunc` with relative addressing (entry = 0),
   `--strictFailure` (unmodeled registers/ops abort instead of becoming
   `Nop`), and `--typeCheck`.
3. The lifter is the pcode2coq checkout at `~/Desktop/pcode2coq`, branch
   `claude/amd64-fixes` (uncommitted changes). These fixes were needed for
   sound amd64 lifts:
   * **Partial-register writes** (AL/AX/EAX/XMM in their base register) now
     merge the written bits into the base register with `Concat`/`Extract`.
     Previously, for example, `ROL AX,8` lifted as `RAX := sext(result)`,
     clobbering bits 16–63, and `NEG EAX` assigned a 32-bit value to RAX.
   * Every varnode read has width exactly `8*size`. 1-bit flags are
     zero-extended to p-code's 1-byte booleans on read and truncated on write.
     `BOOL_NEGATE` is `xor 1`, not a bitwise `NOT` (which gave 0xFE/0xFF).
   * Shift amounts of a different width than the shifted value are coerced
     without changing the semantics.
   * `LZCOUNT` was lifted as `width − popcount`; it is now
     `width − bitwidth`.
   * XMM/YMM/ZMM varnodes map to `R_YMMn` (the registers Picinae models). The
     missing comma that merged `'R_YMM7' 'R_YMM8'` in the register list is
     fixed.
   * Intra-instruction p-code branches are supported: forward branches become
     nested `If`s. The bit-scan loops Ghidra uses for BSF/BSR/TZCNT/LZCNT
     become a bounded `Rep (w+1)` of one `Move v (Ite c (Var v) e)` per
     loop-carried temporary. Loops in any other instruction are rejected. The
     soundness argument is in the comment on `find_scan_loop`.

## Model caveats

* Code is lifted with its entry point rebased to 0. Data references stay at
  Ghidra's absolute addresses (image base 0x100000). For example, the errno
  GOT slot appears as `0x319e10` in the `sigemptyset`/`sigisemptyset` specs.
* Ghidra's p-code doesn't model `#DE` for `IDIV`. The `div`/`ldiv` theorems
  therefore assume the C preconditions (d ≠ 0 and no MIN/−1 overflow).
* For a zero source, Ghidra's BSF writes 0 to the destination, whereas the
  hardware leaves it undefined. glibc's `ffs`/`ffsl` overwrite the
  destination with CMOVZ in that case, so their results don't depend on this.
* `copysignl` cannot be lifted: it uses x87 instructions (`FLD`/`FSTP` on
  `long double`), and pcode2coq rejects their p-code ("Unmodeled Regs:
  R_FPUINSTRUCTIONPOINTER").  `finitel`, `isnanl` and `isinfl` lift because
  glibc implements them with integer instructions on the stack copy of the
  argument.

## Proof-engineering notes

* `bitblast_upto w` proves equalities between bitwise expressions by checking
  each bit. `bsf_iter` and `rep_move_iter` analyze the lifted bit-scan loops.
* After a `CMP` whose flags feed a later `CMOVcc`/`Jcc`, put an invariant
  (cut point) between the two instructions. Without one, the kernel check at
  `Qed` can blow up: `inet_netof` took over 10 minutes before the cut and
  9 s after.
* Functions containing `CALL` must be lifted with global addresses (`fn+=name`):
  pcode2coq's relative mode rebases jump targets but not the return address
  that `CALL` pushes.  `lift.sh` refuses such functions in relative mode.
* Byte-by-byte case analysis does not scale to copies.  The first
  `amd64_memcpy_lemmas.v` peeled each byte read through each store; it took
  15 minutes and 9.6 GB.  Tracking the set of written offsets
  (`amd64_memcpy_sets.v`) proves the same lemmas in 3 seconds.
* When a loop body reads memory it has just written (the strspn table fill,
  four stores per iteration), symbolic execution nests every read inside every
  earlier store and slows to a crawl (65 s for one iteration).  A cut point
  before each unrolled byte keeps one store per segment (12 s).
* `x64_step` cannot split an `If` nested inside a `Seq` (the lifted
  `REP STOSQ`).  Step it by hand: `ISA_step_and_simplify`, `destruct` the
  condition, then repeat `ISA_step_and_simplify`.
* A cut placed exactly on a `CALL` instruction gives a trace without the
  `++` shape that `models_after_steps` expects; put the cut one instruction
  earlier.
* `lia` looks at every arithmetic hypothesis in context, and after a call
  the context is large.  A side condition that took 0.1 s in a small context
  took 139 s (or overflowed the stack) after a `perform_call`.  Run `clear`
  (or `clear - H1 H2`) before `lia` in such side conditions; see `slot_nov` in
  `amd64_strtok_r_proof.v`.
* The same holds inside one big symbolic-execution goal: after five
  `cpy_store`s the memcpy loop exit had ~20 side goals like `k + 16 <= n`,
  and `lia` timed out on each (400 s in total) because the context still held
  the symbolic memory.  Clearing hypotheses by a blacklist missed some;
  `clear - K EX BIG NW NB A0` (a whitelist of the arithmetic facts) made all
  of them take 0.3 s together.  Likewise, `lia` runs out of memory when a
  hypothesis mentions a memory read at a literal address (`n <= m Ⓠ[0x3215a8]`);
  clear it first.
* Avoid `all: first [...]` / `all: try ...` over many goals: a failing
  alternative is retried on every goal, and real failures are hidden.  Use
  explicit bullets and a side tactic that dispatches on the goal's shape
  (`lazymatch goal with |- nov _ _ _ => ... | |- _ + 16 <= _ => ...`).
* Use `sreflexivity` (syntactic `reflexivity`) when the two sides might
  differ syntactically. Plain `reflexivity` on bit expressions over opaque
  values can start an exponential conversion check.
