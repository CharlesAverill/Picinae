# amd64 glibc proofs

Machine-checked Picinae correctness proofs for functions lifted from the
system's own C library: `/lib/x86_64-linux-gnu/libc.so.6`, glibc
2.35-0ubuntu3.12 (sha256 `9b846df0…62c4d9`).

These specifications and proofs were written by Claude Opus 5.5
(`claude-opus-5-5`), an AI model by Anthropic, and checked by Rocq 9.1. Each
proof file starts with a header that gives the function's semantics, quotes
the man page, names the model, and states the input/output specification in
English.

## How this relates to Anthropic's OSS-Verify proofs

Anthropic and Theorem's [OSS-Verify](https://github.com/theorem-labs/oss-verify-proofs)
proves crash-freedom of hundreds of whole RISC-V programs: no fault and no
sanitizer report on any input, and the same behavior as the plain build.
These proofs are fewer and smaller, but they prove more about each function,
and about harder code.  `doc/comparison.tex` has the full comparison; in short:

* **Correct results, byte by byte.**  A crash-freedom statement accepts a
  `memcpy` that copies the wrong bytes.  Ours require `dest[0,n) = src[0,n)`
  with every other byte unchanged.  glibc's overlapping head/tail stores,
  aligned loops and REP MOVSB therefore each need an argument that their
  stores cover exactly `[0,n)`, and for `memmove` that they never overwrite
  source bytes that have not yet been read.
* **Hand-written AVX2 assembly, chosen at run time.**  What `memcpy`,
  `memmove`, `strlen` and `strchr` resolve to on this machine is glibc's
  vectorized assembly.  `__memmove_avx_unaligned_erms` alone has 351
  instructions and at least seven strategies, chosen by size, overlap,
  4 KiB aliasing, CPU-feature flags and tunable thresholds kept in memory.
  OSS-Verify runs vector-capable binaries with the vector unit disabled, so
  its proofs cover scalar code.
* **SIMD and bit-index reasoning.**  VPCMPEQB/VPMINUB/VPMOVMSKB/TZCNT turn
  "first zero byte" into "lowest set bit of a mask".  The proofs relate bit
  positions to byte offsets, including an arithmetic shift (SARX) on the
  page-cross path and a 64-bit TZCNT over two 32-bit masks.  Stepping these
  instructions symbolically was too slow, so `amd64_avx2.v` proves one lemma
  per lifted instruction, by induction over the lanes.
* **x86 and lifting.**  Partial registers, flags, REP prefixes, LOCK, and AVX
  operations Ghidra leaves opaque all needed lifter work, several of them
  soundness fixes.
* **The proof engine at its limit** (see Proof-engineering notes below).

The comparison cuts both ways.  OSS-Verify handles whole programs, a
nondeterministic OS, and proofs that every access stays inside mapped
memory.  These theorems are partial correctness about single functions, in a
memory model where faults are not errors.

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
| `amd64_fill_sets.v` | `fil`: the set of destination offsets memset has filled so far; `fil_store` for one store of a value whose bytes are all c (`bytes_are`), and `rep_bytes` for the lifted broadcast values |
| `amd64_simd.v` | byte-lane specs (`byte`, `zbyte`, `cmpz_spec`, `msk_spec`) and the TZCNT scan loop (`tz_step W`, `tz_result`: W+1 iterations give the index of the lowest set bit, or W) |
| `amd64_avx2.v` | instruction-level lemmas for VPCMPEQB (`vpcmpeqb_tail_exec`), VPMINUB (`vpminub_tail_exec`), VPMOVMSKB (`vpmovmskb_exec`) and TZCNT (`tzcnt32_exec`, `tzcnt64_exec`, `tzcnt32_dc_exec`; register-vs-memory `vpcmpeqb_rld_exec`; `vpbroadcastb0_exec`). Each one describes a whole lifted instruction through a Coq generator convertible to the lifter's output, and is proved once by induction over the lanes. A proof steps such an instruction by hand (`eapply NIStep`, then the lemma), so the 32-lane terms are never built. |
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
| `memcpy` (SSE2, `memcpy@GLIBC_2.2.5` entry) | `memcpy` | for n ≤ 128: dest[0,n) = src[0,n), everything else unchanged, even when the buffers overlap (`memcpy_correct_small`, `memcpy_correct_mid`); for 128 < n ≤ the non-temporal threshold, the same for non-overlapping buffers with d ≥ 64 (`memcpy_correct_loops` in `amd64_memcpy_loops_proof.v`: forward and 4 KiB-aliasing backward 64-byte loops; Qed 125 s).  The non-temporal path above the threshold is not covered |
| `__memmove_avx_unaligned_erms` (what `memmove` and `memcpy` resolve to on AVX2 machines) | `memmove_avx` | for n ≤ 256: dest[0,n) = src[0,n), everything else unchanged, **even when the buffers overlap** (memmove semantics; `memmove_avx_correct_small`; Qed 70 s). Precondition n ≤ `__x86_rep_movsb_threshold`, which glibc never sets below 256 for AVX.  For 256 < n ≤ both thresholds, the same for non-overlapping buffers with d ≥ 128 (`memmove_avx_correct_loops` in `amd64_memmove_avx_loops_proof.v`: the forward 128-byte loop and the 4 KiB-aliasing backward loop; Qed 148 s).  Above `__x86_rep_movsb_threshold` and below `__x86_rep_movsb_stop_threshold`, the same (`memmove_avx_correct_rep` in `amd64_memmove_avx_rep_proof.v`: REP MOVSB with the source or the destination aligned to 64 bytes, and the short-distance fallback to the forward loop; needs DF = 0; Qed 145 s).  At or above the stop threshold the non-temporal path (`amd64_memmove_avx_nt_proof.v`) is proven by factoring every per-address obligation into a standalone lemma whose conclusion is a `nextinv` (`nt_seg_1117` … `nt_seg_1706`), so each has its own bounded Qed and the theorem just applies them.  The two-page interleaved 8-vector store loop uses `nt_adv2` (post-store memory abstraction); the two-page tail (`nt_seg_1117`/`1125`/`1210`) and four-page tail (`nt_seg_1613`/`1621`/`1706`) are proven, the key being cut points 1210/1706 at the final overlapping-copy entries so the tail loops stop there instead of stepping the final copy into their branch tests (which peaked at ~9 GB); the 128-byte tail-loop body advances by `cpy_store4w`, the final copy by `cpy_store4w` + `cpy_copied` via the `fcaddr` address lemma.  The four-page inner loop (`nt_seg_1285`) advances `done4` by `cpy_store16` (16 stores), mirroring the two-page inner loop's `cpy_store8`.  Build this file with `ulimit -v 13000000`.  Not yet covered: overlapping buffers above 256 bytes |
| `__strlen_avx2` (what `strlen` resolves to on AVX2 machines) | `strlen_avx2` | RAX = strlen(s) (`slen`), for every path: the first unaligned 32-byte block, the page-cross block (VPCMPEQB on the aligned block, SARX by s mod 32), four aligned blocks, and the 128-byte loop (VPMINUB of four vectors; exit located with two 32-bit masks and a 64-bit TZCNT).  Memory unchanged.  The SIMD instructions are stepped with the lemmas of `amd64_avx2.v`; Qed 56 s |
| `__strchr_avx2` (what `strchr` resolves to on AVX2 machines) | `strchr_avx2` | with K the first index whose byte is c or NUL (`fhit`; `fhit_of_slen` shows every terminated string has one): RAX = s + K if that byte is c, else NULL; so c = 0 returns the terminator.  Every path: the first block (VPCMPEQB against the broadcast c and against zero, VPOR), the page-cross block (SARX), four aligned blocks, and the 128-byte loop (a hit is a zero byte of VPMINUB(x, x XOR c)).  Memory unchanged |
| `__strcmp_avx2` (what `strcmp` resolves to on AVX2 machines) | `strcmp_avx2` | short-string case: with K the first index where the strings differ or `p` terminates (`scmp`), and K < 32 with both pointers ≥128 bytes from a page end, EAX = `(m[p+K] - m[q+K]) mod 2^32`.  The stop mask comes from VPCMPEQB(p,q); VPMINUB(_,p); VPCMPEQB(_,0).  The four-block path, the 128-byte loop and the page-straddle path are refuted by the preconditions; proving them for K ≥ 32 is future work |
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
| `lsearch` | `lsearch` | **non-leaf, two callees** (comparator through R14, memcpy through the PLT): the first match, or else key appended at base + N·size, *nmemb := N + 1, return the new element.  glibc treats a match at address 0 as "not found"; the precondition NZ excludes that |
| `pthread_mutex_lock` | `pthread_mutex_lock` | **non-leaf** (`__lll_lock_wait` at three call sites, contract satisfiable): every kind: normal / error-check-not-owner (lock := 1 or 2, owner := TID, ++nusers), recursive (++count, EAGAIN at 2^32-1, or first lock with count := 1), adaptive (bounded spin, `__spins` updated), error-check owned (EDEADLK); robust/PI/PP and elision tail-call out; `__assert_fail` otherwise.  Needs `__pthread_force_elision = 0` (the default) and the mutex/TID/global outside the 32-byte frame.  Main theorem **Admitted (QED-SLOW)**: tactics take ~3 min, the kernel check > 30 min.  #1 libc function in the Firefox profile |
| `pthread_mutex_unlock` | `pthread_mutex_unlock` | **non-leaf** (futex wake through `__lll_lock_wake`): every mutex kind: normal/adaptive release (--nusers, owner := 0, lock := 0, return 0); recursive (EPERM unless owner = TID, else --count, release at 0); error-check (EPERM unless owner = TID and locked); robust/PI/PP and elision kinds tail-call out; other kinds hit `__assert_fail`.  Chosen first because it is the #3 libc function in a Firefox profile (`lifter/firefox_libc_profile.txt`) |
| `__memset_avx2_unaligned_erms` | `memset_avx2` | every size class: n < 32 (overlapping 1-16-byte stores), 32..256 (2, 4 or 8 YMM stores), the 128-byte aligned loop, and REP STOSB above `__x86_rep_stosb_threshold`: dest[0,n) = c, all other bytes unchanged, RAX = d.  Main theorem **Admitted (QED-SLOW)**: tactics take about a minute, the kernel check > 30 min (power-of-two literals in the size tests).  The memset IFUNC chooses on AVX2 machines |
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
   * **AVX/AVX2** (added for the glibc variants Firefox actually runs):
     the user-defined ops Ghidra leaves opaque (`vpcmpeqb_avx[2]`,
     `vpminub_avx[2]`, `vpor_avx2`, `vpand_avx2`, `swap_bytes` for `MOVBE`,
     `vmovntdq_avx`) are spelled out byte by byte, the same way SLEIGH spells
     their SSE2 counterparts.  Whole-ZMM varnodes and unnamed sub-pieces of
     a vector register (e.g. byte 17 of YMM0) are handled.
     `lifter/list_userops.py` lists the user ops a function needs.
   * **Lane writes are merged.** SLEIGH writes some vector results one lane
     at a time (VPBROADCASTB: 32 byte writes into YMM0).  Lifted naively,
     each write re-reads the register to merge its lane, so the symbolic
     value doubles with every lane; `memset_avx2` ran out of memory in the
     type checker (11 GB).  Consecutive writes to disjoint parts of one
     register that don't read it now become one `Move` of the assembled
     `Concat` (`merge_lane_writes`).
   * The `LOCK`/`UNLOCK` user ops of `LOCK`-prefixed instructions lift as
     no-ops (see the caveat below).
   * The generated "Static Memory Hypotheses" section is switched off
     (`staticMemory=False` in the headless driver): its `SMCorrect` proof
     can take gigabytes to check, and the proofs here state such facts as
     preconditions instead.  Uninitialized (`.bss`) data is skipped.

Canonical temporaries: the headless lifter now passes `canonicalTemps=True`, so each instruction's unique-space temporaries are numbered `V_TEMP 0, 1, ...` in order of first appearance.  Ghidra's unique varnodes never live across instructions, so this preserves semantics, and every occurrence of an instruction (for example `VPMOVMSKB EAX,YMM1`) lifts to the same statement.  The five AVX files (strlen, strchr, memcmp, strcmp, memmove) were re-lifted this way; earlier lifts keep Ghidra's offsets.

## Model caveats

* Code is lifted with its entry point rebased to 0. Data references stay at
  Ghidra's absolute addresses (image base 0x100000). For example, the errno
  GOT slot appears as `0x319e10` in the `sigemptyset`/`sigisemptyset` specs.
* Ghidra's p-code doesn't model `#DE` for `IDIV`. The `div`/`ldiv` theorems
  therefore assume the C preconditions (d ≠ 0 and no MIN/−1 overflow).
* For a zero source, Ghidra's BSF writes 0 to the destination, whereas the
  hardware leaves it undefined. glibc's `ffs`/`ffsl` overwrite the
  destination with CMOVZ in that case, so their results don't depend on this.
* Ghidra marks `LOCK`-prefixed (and implicitly locked `XCHG`) instructions
  with `LOCK`/`UNLOCK` user ops.  pcode2coq lifts them as no-ops: Picinae's
  semantics is single-threaded, so the atomicity they add is not modeled.
  The mutex proofs are therefore sequential-correctness results.
* Picinae models the low 256 bits of the vector registers.  When Ghidra's
  p-code touches a whole ZMM register (VEX-encoded AVX/AVX2 instructions
  and `VZEROUPPER` zero bits 256-511), pcode2coq drops the write to the
  upper half and reads it as zero.
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
* Symbolic execution of a function with many paths that rejoin (lock's
  dispatch, two acquire variants, three wait calls) needs a cut at every
  join point; without them the live paths and their states grew past 8 GB.
* Conversion checks on goals that mention symbolic memory can expand
  `getmem`/`setmem` and exhaust memory: `reflexivity`, `assumption`,
  `contradiction`, non-linear `match goal` patterns, and `rewrite` with a
  lemma whose memory argument is a unification variable all did this in the
  mutex_lock proof.  Use syntactic versions (`constr_eq` before `exact` /
  `reflexivity`), explicit lemma arguments, and let `psimpl` normalize both
  goals and hypotheses the same way.
* From the memmove proofs: `discriminate` with memory equations in the
  context (`s R_YMM0 = m Ⓨ[s]`) can hang head-normalizing the loads;
  `eapply cpy_store` / `rewrite cpy_load` with the memory or the offset left
  as unification variables ran out of memory, while `refine` of the instance
  with every argument explicit is instant.  Refuting an infeasible path
  works best from one branch hypothesis plus one bound (`refute` in
  `amd64_memmove_avx_loops_proof.v`) after excluding hypotheses that mention
  `getmem`.  Pruning paths after every step (`step_prune`) turned a 23 s
  stepping phase into more than 10 minutes; step everything, then prune once.
* Avoid `all: first [...]` / `all: try ...` over many goals: a failing
  alternative is retried on every goal, and real failures are hidden.  Use
  explicit bullets and a side tactic that dispatches on the goal's shape
  (`lazymatch goal with |- nov _ _ _ => ... | |- _ + 16 <= _ => ...`).
* Use `sreflexivity` (syntactic `reflexivity`) when the two sides might
  differ syntactically. Plain `reflexivity` on bit expressions over opaque
  values can start an exponential conversion check.
