# amd64 stdlib verification roadmap

## What is already covered

Functions with a correctness proof somewhere in the repo, on any branch:

| Function | ISA | Where |
|---|---|---|
| strlen | i386, armv7 | `Examples/` (master) |
| strcmp | i386 | `Examples/` (master) |
| strcasecmp | armv8 | `Examples/` (master) |
| memset | armv7 | `Examples/` (master) |
| memcmp (constant-time, fault-tolerant) | armv8 | `Examples/crypto_memcmp` |
| wcsspn | i386 | `Examples/` (master) |
| wcsnlen | i386 | `wcsnlen_i386` branch |
| strspn | armv8 | `ixb/strspn`, master history (one `Admitted`) |
| tolower / toupper | armv8 | `nya-master-smc` (musl softballs) |
| strtok | armv7 | `arm-strtok-proof` (2 lemmas only, no top-level theorem) |
| binary search, strlen (timing) | various | `timing*` branches |

The `musl-armv8` / `nya-master*` branches also **lift** atoi, memchr, memrchr, memmem,
memmove, strcspn, strchrnul, strrchr, swab, wcschr, wcscspn, wcslen, wcscpy, wcstok,
wmemchr, wmemcmp, wmemmove, htonl, fabs, ceil, inet_aton. Those files only prove
`welltyped`/`nwc`, though, so they count as uncovered.

**No amd64 proofs exist yet.** Everything below is new for amd64, including
amd64 ports of strlen, strcmp, memset, and the rest. The first few of those ports
are good warm-ups because the i386/ARM invariants can be reused almost unchanged.

## Pick the implementation before picking the function

The difficulty of a given function depends more on *which* binary you lift than on the
function itself:

* **glibc x86_64**: str/mem functions dispatch by ifunc to SSE2, AVX2 or EVEX
  variants (`pcmpeqb`, `pmovmskb`, `vpminub`, `tzcnt`, 256-bit YMM). Proving these
  takes a SIMD byte-lane theory first. Avoid them for the bulk effort.
* **musl x86_64**: almost everything is portable C. The exceptions are
  `memcpy`, `memmove` and `memset`, which are hand-written asm using `rep movsq` /
  `rep stosq`. Check that the lifter handles `rep` prefixes before relying on those.
* **Recommended**: compile musl's C sources yourself with
  `-O2 -fno-tree-vectorize -fno-builtin -mno-sse -fno-stack-protector` (or `-O1`).
  This gives scalar, loop-structured code close to the i386 examples. Note that
  musl's `strlen`/`memchr`/`strchrnul` use word-at-a-time `HASZERO` tricks; the
  `Ones`/`noborrow_nonil` lemmas in `i386_strlen_proof.v` port directly (32→64).

## Shared conventions for the draft theorems

SysV amd64 ABI: args in `RDI, RSI, RDX, RCX, R8, R9`; return in `RAX` (and `RDX` for
128-bit struct returns); callee-saved `RBX, RBP, R12–R15`; on return `RSP = rsp0 + 8`.
`int` arguments are only valid in the low 32 bits. Every theorem below implicitly also
comes with the standard side theorems in the style of `i386_strcmp_proof.v`:
`*_nwc`, `*_welltyped`, `*_preserves_rsp`, `*_preserves_callee_saved`, and (for
read-only functions) `*_preserves_memory`.

Common definitions (Picinae notation, `mem := s0 V_MEM64`):

```coq
(* bytes p[0..k) are all nonzero *)
Definition nilfree m p k := ∀ i, i < k -> m Ⓑ[p ⊕ i] <> 0.
(* the C string at p has length n *)
Definition strlen_is m p n := nilfree m p n /\ m Ⓑ[p ⊕ n] = 0.
(* m and m' agree outside [p, p+n) *)
Definition frame m m' p n := ∀ a, ¬(p <= a < p + n) -> m' Ⓑ[a] = m Ⓑ[a].
(* low byte / low dword of an int argument *)
Definition uc x := x mod 2^8.
Definition i32 x := toZ 32 (x mod 2^32).
```

Functions that write memory have no-overlap preconditions, and also need the
caller's buffers to be disjoint from the callee's stack frame. Reuse the `mem' fbytes`
trick from `i386_wcsspn_proof.v`, or state `frame` relative to `[rsp0 - k, rsp0)`.

---

## Tier 0: straight-line, no memory (hours each)

Good first amd64 examples. They test the lifter/ISA plumbing and build the
amd64 proof idioms.

| # | Function | Man-page contract | Draft postcondition (at `ret`) |
|---|---|---|---|
| 1 | `htons` / `ntohs` | host to network byte order, 16-bit | `s' R_RAX mod 2^16 = (x mod 2^8) * 2^8 + (x / 2^8) mod 2^8` where `x = rdi mod 2^16` |
| 2 | `htonl` / `ntohl` | same, 32-bit (`bswap`) | `s' R_RAX mod 2^32 = Σ_{i<4} byte_i(rdi) * 2^(8*(3-i))` (define `bswap32` by `N.lor` of shifted bytes) |
| 3 | `isascii`, `isdigit`, `isupper`, `islower`, `isblank`, `isspace`, `isxdigit`, `isalpha`, `isalnum`, `isprint`, `isgraph`, `iscntrl`, `ispunct` | "checks whether c falls into a certain character class" (C locale) | `(s' R_RAX mod 2^32 <> 0) <-> class (rdi mod 2^32)` for `0 <= c < 256`, with e.g. `class c := 48 <= c <= 57`. musl uses `(unsigned)c-'0' < 10`, which is easy. **glibc** uses a TLS-based `__ctype_b_loc` table, so use musl. |
| 4 | `toascii` | low 7 bits | `s' R_RAX mod 2^32 = rdi mod 2^7` |
| 5 | `abs`, `labs`, `llabs`, `imaxabs` | "absolute value" (UB for `INT_MIN`) | Precondition `i32 rdi <> -2^31`. Post: `i32 (s' R_RAX) = Z.abs (i32 rdi)`. For `labs`, use 64-bit `toZ 64`. Branchless `cdq; xor; sub` needs a small `toZ`/xor lemma. |
| 6 | `div`, `ldiv`, `lldiv`, `imaxdiv` | `quot*den + rem = num`, quot rounds toward 0 | Pre: `den <> 0` and `¬(num = MIN /\ den = -1)`. Post (`ldiv`, returned in `RAX:RDX`): `toZ 64 rax = Z.quot n d /\ toZ 64 rdx = Z.rem n d`. `div` packs both 32-bit fields into `RAX`. Needs `idiv` semantics in the lifter. |
| 7 | `ffs`, `ffsl`, `ffsll` | "position of the first (least significant) bit set… or 0" | `(x = 0 -> rax = 0) /\ (x <> 0 -> N.testbit x (rax-1) = true /\ ∀ j, j < rax-1 -> N.testbit x j = false)` (32-bit result). Uses `bsf`/`tzcnt` + `cmov`; check that BSF's undefined-dest case is modelled. |
| 8 | `fabs`, `copysign`, `signbit` (bit-level only) | sign-bit manipulation | `ymm0'[63:0] = N.clearbit (ymm0[63:0]) 63`. No FP semantics needed because `andpd` is a mask. A good test of YMM sub-register handling. |
| 9 | `toupper`, `tolower` (amd64 port) | "if c is lowercase, returns uppercase… otherwise c" | `rax32 = if 97 <= c <= 122 then c - 32 else c` for `c ∈ [0,255] ∪ {EOF}`. Port of the existing arm8 proof. |

## Tier 1: single loop, read-only, no arithmetic tricks (1–3 days each)

One loop invariant of the form "prefix checked, pointer = base ⊕ k". Use
`i386_strcmp_proof.v` as the template.

| # | Function | Contract | Draft postcondition |
|---|---|---|---|
| 10 | **strlen** (amd64 port) | number of bytes before NUL | `strlen_is mem rdi rax`. Scalar version first, then the musl word-at-a-time version reusing the i386 lemmas. |
| 11 | **strnlen** | "`strlen(s)` if < maxlen, else maxlen; never beyond `s[maxlen-1]`" | `rax <= rsi /\ nilfree mem rdi rax /\ (rax < rsi -> mem Ⓑ[rdi ⊕ rax] = 0)`. Also prove a read-footprint theorem: every memory read address lies in `[rdi, rdi+rsi)`. The man page explicitly promises this, and it is the interesting part. |
| 12 | `wcslen`, `wcsnlen` (amd64 port) | wide version, `wchar_t` = 4 bytes | as above with `Ⓓ[p ⊕ 4*i]` |
| 13 | **memchr** | "first instance of c in the initial n bytes… pointer or NULL" | `(rax = 0 /\ ∀ i<n, mem Ⓑ[s⊕i] <> uc c) \/ (∃ k, k < n /\ rax = s ⊕ k /\ mem Ⓑ[s⊕k] = uc c /\ ∀ i<k, mem Ⓑ[s⊕i] <> uc c)` with `s=rdi, c=rsi, n=rdx` |
| 14 | `rawmemchr` | "assumes an instance of c lies somewhere" | Pre: `∃ k, mem Ⓑ[s⊕k] = uc c`. Post: `∃ k, rax = s⊕k /\ mem Ⓑ[s⊕k] = uc c /\ ∀ i<k, mem Ⓑ[s⊕i] <> uc c` |
| 15 | **memrchr** | like memchr but "searches backward from the end" | `(rax = 0 /\ ∀ i<n, …≠) \/ (∃ k<n, rax = s⊕k /\ mem Ⓑ[s⊕k] = uc c /\ ∀ i, k<i<n -> mem Ⓑ[s⊕i] <> uc c)` |
| 16 | `wmemchr` | wide memchr | memchr with 4-byte stride; compares full 32-bit `wchar_t` |
| 17 | **strchrnul** | "pointer to matched character, or to the null byte… (`s+strlen(s)`)" | `∃ k, rax = s⊕k /\ (mem Ⓑ[s⊕k] = uc c \/ mem Ⓑ[s⊕k] = 0) /\ ∀ i<k, mem Ⓑ[s⊕i] <> uc c /\ mem Ⓑ[s⊕i] <> 0` |
| 18 | **strchr** | "first occurrence… NUL is part of the string" | `∃ n, strlen_is mem s n /\ ((rax = 0 /\ ∀ i<=n, mem Ⓑ[s⊕i] <> uc c) \/ (∃ k<=n, rax = s⊕k /\ mem Ⓑ[s⊕k] = uc c /\ ∀ i<k, mem Ⓑ[s⊕i] <> uc c))`. Note that `c = 0` yields `s⊕n`. |
| 19 | **strrchr** | "last occurrence" | as strchr, but the uniqueness clause is `∀ i, k<i<=n -> …≠` |
| 20 | `wcschr`, `wcsrchr` | wide versions | as 18/19 with 4-byte stride |
| 21 | **memcmp** (plain, amd64) | "<0, 0, >0… bytes interpreted as unsigned char" | `(rax32 = 0 /\ ∀ i<n, a_i = b_i) \/ (∃ k<n, (∀ i<k, a_i=b_i) /\ (a_k ?= b_k) = (i32 rax ?= 0)%Z)` where `a_i := mem Ⓑ[rdi⊕i]` |
| 22 | `bcmp` | 0 iff equal | `(rax32 = 0) <-> ∀ i<n, a_i = b_i` |
| 23 | **wmemcmp** | wide memcmp; `wchar_t` is **signed** on x86_64 | as memcmp but compare `toZ 32` of each `Ⓓ` |
| 24 | **strcmp** (amd64 port) | | Reuse `streq` and `postcondition` from `i386_strcmp_proof.v`, with `toZ 32 (rax mod 2^32)`. |
| 25 | **strncmp** | "compares only the first (at most) n bytes" | `∃ k, k <= n /\ streq mem s1 s2 k /\ ((k = n /\ rax32 = 0) \/ (k < n /\ (rax32 = 0 -> a_k = 0) /\ (a_k ?= b_k) = (i32 rax ?= 0)%Z))` |
| 26 | `wcscmp`, `wcsncmp` | wide; signed compare | as 24/25 with signed `Ⓓ` |
| 27 | **strncasecmp** | strcasecmp bounded by n | combine 25 with the `tolower` relation from `arm8_strcasecmp_proof.v` |

## Tier 2: single loop that writes memory (2–5 days each)

New ingredient: a write-frame postcondition plus no-overlap preconditions.
Build a reusable amd64 `frame`/no-alias lemma library while doing #28, then use
it for the rest of this tier.

| # | Function | Contract | Preconditions | Draft postcondition (`m' := s' V_MEM64`) |
|---|---|---|---|---|
| 28 | **bzero**, `explicit_bzero` | write n zero bytes | `[s, s+n)` writable, disjoint from stack frame | `(∀ i<n, m' Ⓑ[s⊕i] = 0) /\ frame mem m' s n` |
| 29 | **memset** (amd64 port) | fill n bytes with `(unsigned char)c`, return s | same | `rax = s /\ (∀ i<n, m' Ⓑ[s⊕i] = uc c) /\ frame mem m' s n` |
| 30 | `wmemset` | fill n `wchar_t`s, return wcs | same, 4n bytes | `rax = s /\ (∀ i<n, m' Ⓓ[s⊕4i] = c mod 2^32) /\ frame mem m' s (4n)` |
| 31 | **memcpy** | copy n bytes, "areas must not overlap", return dest | `[d,d+n) ∩ [s,s+n) = ∅`, d writable | `rax = d /\ (∀ i<n, m' Ⓑ[d⊕i] = mem Ⓑ[s⊕i]) /\ frame mem m' d n` |
| 32 | `mempcpy`, `wmemcpy`, `wmempcpy` | memcpy variants | same | `rax = d ⊕ n` (resp. `d ⊕ 4n`), rest as memcpy |
| 33 | **stpcpy** | copy string incl. NUL; return pointer to dest's NUL | `strlen_is mem s n`, `[d,d+n]` disjoint from `[s,s+n]` | `rax = d⊕n /\ (∀ i<=n, m' Ⓑ[d⊕i] = mem Ⓑ[s⊕i]) /\ frame mem m' d (n+1)` |
| 34 | **strcpy**, `wcscpy` | same, return dest | same | as stpcpy with `rax = d` |
| 35 | **strncpy** | copy ≤ n bytes, then NUL-pad to exactly n | `[d,d+n)` disjoint from src | `let L := min(strlen s, n) in rax = d /\ (∀ i<L, m'[d⊕i] = mem[s⊕i]) /\ (∀ i, L<=i<n -> m'[d⊕i] = 0) /\ frame mem m' d n`. Two loops, but sequential. |
| 36 | **stpncpy** | as strncpy; returns ptr to dest's NUL, or `dest+n` | same | same body, plus `rax = d ⊕ L` |
| 37 | **memccpy** | copy until c found or n bytes; "pointer to the next character in dest after c, or NULL" | disjoint | `(∃ k<n, mem[s⊕k] = uc c /\ (∀ i<k, mem[s⊕i] <> uc c) /\ rax = d⊕(k+1) /\ copied (k+1) /\ frame … (k+1)) \/ ((∀ i<n, mem[s⊕i] <> uc c) /\ rax = 0 /\ copied n /\ frame … n)` |
| 38 | **swab** | "copies n bytes… exchanging adjacent even and odd bytes; does nothing when n < 0" | disjoint, n even | `(toZ 64 n <= 0 -> m' = mem) /\ (0 < n -> ∀ i < n/2, m'[d⊕2i] = mem[s⊕2i+1] /\ m'[d⊕2i+1] = mem[s⊕2i])` plus a frame over `[d, d+n)` (odd last byte left unspecified) |
| 39 | **strcat** | append src at dest's NUL, return dest | `strlen_is mem d a`, `strlen_is mem s b`, disjoint | `rax = d /\ (∀ i<=b, m'[d⊕(a+i)] = mem[s⊕i]) /\ frame mem m' (d⊕a) (b+1)`. Composes strlen and strcpy loops. |
| 40 | **strncat** | ≤ n bytes from src, always NUL-terminate; "writes n+1 bytes" when src ≥ n | `strlen_is mem d a`, src need not be terminated | `let L := (k s.t. k <= n /\ nilfree mem s k /\ (k < n -> mem[s⊕k]=0)) in rax = d /\ copied L at d⊕a /\ m'[d⊕(a+L)] = 0 /\ frame mem m' (d⊕a) (L+1)` |
| 41 | **strlcpy** | copy up to `size-1`, NUL-terminate if `size > 0`; returns `strlen(src)` | `strlen_is mem s n` | `rax = n /\ (size > 0 -> let L := min n (size-1) in copied L /\ m'[d⊕L] = 0 /\ frame mem m' d (L+1)) /\ (size = 0 -> m' = mem)`. musl/glibc ≥ 2.38. |
| 42 | **strlcat** | append ≤ `size - strlen(dst) - 1`; returns `strlen(dst)+strlen(src)`, or `size+strlen(src)` if no NUL in first `size` bytes | `strlen_is mem s b` | `(∃ a<size, strlen_is mem d a /\ rax = a+b /\ …strlcpy at d⊕a with size-a…) \/ (nilfree mem d size /\ rax = size + b /\ m' = mem)` |

## Tier 3: nested loops or overlap reasoning (1–2 weeks each)

| # | Function | Contract | Draft postcondition | Main difficulty |
|---|---|---|---|---|
| 43 | **memmove** | copy "as though… first copied into a temporary array" | `rax = d /\ (∀ i<n, m' Ⓑ[d⊕i] = mem Ⓑ[s⊕i]) /\ frame mem m' d n`. Same as memcpy but with no disjointness precondition. | Two directions. The forward copy invariant must state that the source suffix is still unclobbered when `d < s`. |
| 44 | `wmemmove` | wide memmove | as above, ×4 | same |
| 45 | **strcspn** | "length of initial segment… not in reject" | `(∀ i<r, ¬contains mem rej (mem[s⊕i]) /\ mem[s⊕i] <> 0) /\ (mem[s⊕r] = 0 \/ contains mem rej (mem[s⊕r]))`, with `contains` as in `i386_wcsspn_proof.v` but 1-byte | Nested loop. musl builds a 256-bit bitset on the stack, so the stack-frame memory must be part of the invariant. |
| 46 | `wcscspn`, `wcspbrk` | wide variants | as 45/47 with 4-byte stride | wcsspn proof is the template |
| 47 | **strpbrk** | "first occurrence in s of any of the bytes in accept… or NULL" | `rax = 0 ∧ ¬∃… \/ ∃ k, rax = s⊕k ∧ (strcspn s acc = k) ∧ mem[s⊕k] <> 0`. Easiest as a corollary of 45 if it calls `strcspn`. | function call: needs a call/return spec (see `funccalls` branch) |
| 48 | **strspn** (amd64 port) | | port of the arm8 spec | bitset again |
| 49 | **strsep** | "If `*stringp` is NULL returns NULL… token terminated by overwriting delimiter with NUL; `*stringp` updated past token, or NULL" | Let `p := mem Ⓠ[rdi]`. `(p = 0 -> rax = 0 /\ m' = mem) /\ (p <> 0 -> rax = p /\ ∃ k, (∀ i<k, mem[p⊕i] ∉ delim ∪ {0}) /\ ((mem[p⊕k] = 0 /\ m' Ⓠ[rdi] = 0 /\ m' agrees except [rdi,rdi+8)) \/ (mem[p⊕k] ∈ delim /\ m'[p⊕k] = 0 /\ m' Ⓠ[rdi] = p⊕(k+1) /\ m' agrees except at p⊕k and [rdi,rdi+8))))` | Two writes, one through a double pointer; calls strcspn in musl. |
| 50 | **strtok_r** | see man page; tokens are nonempty, runs of delimiters collapse | Pre: `str ≠ 0` or `*saveptr` valid. Post: `rax = 0` iff the remainder is only delimiters; otherwise `rax` = first non-delim, the next delim (if any) is overwritten with 0, and `*saveptr` = following byte | Spec is long, and it chains strspn and strcspn. |
| 51 | `strtok` | strtok_r with a static saveptr | as 50, with saveptr in `.bss` | The static global needs data-segment modelling. |
| 52 | **strstr** (naive) / `memmem` (naive) | "first occurrence of the substring needle… NULL if not found" | `match m h k nl := ∀ j<nl, m[h⊕(k+j)] = m[nd⊕j]`. Post: `(∃ k, rax = h⊕k /\ match k /\ ∀ k'<k, ¬match k' /\ k+nl <= hl) \/ (rax = 0 /\ ∀ k, k+nl <= hl -> ¬match k)`. Empty needle returns h. | **musl/glibc use Two-Way** (Crochemore–Perrin), which is research-grade. Compile a naive O(nm) version first, or treat Two-Way as a stretch goal. |
| 53 | `strcasestr` | case-insensitive strstr | as 52 with `tolower` | same |
| 54 | `insque` / `remque` | doubly linked list insert/remove | `insque(e,p)`: `p = 0 -> m' Ⓠ[e] = 0 /\ m' Ⓠ[e⊕8] = 0`; else `m' Ⓠ[e] = mem Ⓠ[p] /\ m' Ⓠ[e⊕8] = p /\ m' Ⓠ[p] = e /\ (mem Ⓠ[p] <> 0 -> m' Ⓠ[mem Ⓠ[p] ⊕ 8] = e)` | Straight-line, but needs pointer aliasing case-splits (elem ≠ prev ≠ next). It could sit in Tier 1 by effort; it is listed here because the frame and aliasing preconditions are fiddly. |

## Tier 4: arithmetic parsing, overflow, errno (2–4 weeks)

| # | Function | Contract | Draft postcondition | Main difficulty |
|---|---|---|---|---|
| 55 | **a64l** | base-64 string (≤ 6 chars, `./0-9A-Za-z`) to 32-bit long, **sign-extended** to 64 | `let ds := digits up to first non-digit or 6 in rax = sext32 (Σ_i val(ds_i) * 64^i mod 2^32)` | Small and well-defined. A good entry point to this tier. |
| 56 | `l64a` | inverse; returns a static buffer | `decode(static_buf) = rdi mod 2^32 /\ ∀ i<len, valid_digit` | static buffer in `.bss` |
| 57 | **atoi / atol / atoll** | "same as `strtol(nptr,NULL,10)` except… no checks for overflow" | Pre: the result fits (UB otherwise). Post: `∃ ws sg ds, isspace* ws /\ sg ∈ {ε,+,-} /\ digits ds /\ next ∉ digits /\ toZ 64 rax = sign sg * Σ ds_i 10^(len-1-i)` | Spec needs a small grammar. musl calls `isspace`, a call boundary. musl accumulates negatively to avoid overflow on MIN. |
| 58 | **strtoul / strtol / strtoll / strtoull** | bases 0, 2–36, `0x` prefix, `*endptr`, saturate to LONG_MIN/MAX and set `errno = ERANGE` | as 57, plus base detection, `*endptr` write, and the saturation case: `overflow -> rax = LONG_MAX /\ errno' = ERANGE` | errno is `*__errno_location()`, which is TLS through `FS_BASE`. musl's implementation goes through `__intscan`/FILE shims, so it is very hard; a standalone C implementation is more realistic. |
| 59 | `strverscmp` | version-aware compare | state machine | spec is a long table |

## Tier 5: function pointers and recursion (research-grade)

| # | Function | Contract | Notes |
|---|---|---|---|
| 60 | **bsearch** | "pointer to a matching member… or NULL"; array sorted w.r.t. `compar` | Needs a callee contract for `compar` (an indirect `call`): `compar` is pure, returns a sign consistent with a total preorder, and preserves callee-saved registers. Post: `rax = 0 -> ∀ i<nmemb, cmp(key, elt i) <> 0`; `rax <> 0 -> ∃ i<nmemb, rax = base ⊕ i*size /\ cmp(key, elt i) = 0`. Reuse the timing-branch binary_search invariant. |
| 61 | `lfind` / `lsearch` | linear search with comparator (lsearch appends) | as bsearch without sortedness; lsearch adds a write and `*nmemb++` |
| 62 | **qsort** | sort in place w.r.t. `compar` | Post: `Permutation (elems m') (elems mem) /\ Sorted cmp (elems m')`. musl uses smoothsort, glibc uses introsort with a malloc fallback. Very hard; write your own insertion sort and start there. |
| 63 | `tsearch`/`tfind`/`tdelete`, `hsearch` | trees and hash tables with malloc | Out of scope until there is an allocator model. |

---

## Suggested order

1. `htonl`, `ffs`, `abs`, `isdigit`, `toupper`: shake out the amd64 lifter and the
   psimpl idioms.
2. `strlen`, `strnlen`, `memchr`, `strchrnul`, `strchr`, `strrchr`: one invariant
   pattern that can be shared, ideally factored into a `Picinae_amd64_strings.v`
   lemma file.
3. `memcmp`, `strcmp`, `strncmp`, `wmemcmp` (signed!): comparison family.
4. `bzero`, `memset`, `memcpy`, `stpcpy`, `strcpy`, `strncpy`, `strlcpy`: build the
   write-frame library once, then reuse it.
5. `strcat`, `strncat`, `strlcat`, `swab`, `memccpy`.
6. `memmove`, `strcspn`/`strspn`/`strpbrk`, `strsep`, `strtok_r`.
7. `a64l`, `atoi`, then the comparator family (`bsearch`, `lfind`), which needs a
   call-contract framework.

## Open questions to settle before starting

* Which lifter produces the amd64 `.v` programs (BAP or Ghidra p-code), and does it
  support `rep movs/stos`, `bsf`/`tzcnt` with undefined-dest semantics, `idiv`, and
  `cmov`?
* Should postconditions use `⊕` (mod 2^64) addresses throughout, or add
  non-wraparound preconditions (`p + n < 2^64`) to keep arithmetic in plain `+`? The
  i386 proofs mix both styles.
* Calls (`strpbrk → strcspn`, `atoi → isspace`, `bsearch → compar`): inline
  them at compile time (`-finline-functions`, static), or build on the
  `buzzetti/funccall` / `henry/calling-conventions` work?
