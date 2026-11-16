(* strchr -- AVX2 implementation (__strchr_avx2)

   SEMANTICS
   ---------
   strchr(s, c) returns a pointer to the first byte of s equal to
   (unsigned char) c, or NULL if the terminating NUL comes first; for c = 0
   it returns a pointer to the terminator.  On AVX2 machines glibc's IFUNC
   resolver selects __strchr_avx2 (in our Firefox profile it is the most-used
   strchr variant).  It broadcasts c to all 32 bytes of YMM0 and looks for
   the first "hit", a byte that is either c or 0:
   * unless s is within 32 bytes of the end of a 4 KiB page, it checks the
     32 bytes at s: VPCMPEQB with the broadcast c and with zero, VPOR, then
     VPMOVMSKB and TZCNT; near a page end it checks the aligned block that
     contains s and shifts the mask right by s mod 32 (SARX);
   * then it checks the next four aligned 32-byte blocks one by one;
   * then it loops over aligned 128-byte blocks: for each vector x it computes
     VPMINUB(x, x XOR c), whose bytes are zero exactly at the hits, combines
     the four with VPMINUB, and compares with zero once;
   * at the first hit it compares the byte with c: equal gives its address,
     otherwise (it is the terminator) NULL.
   As for strlen, it reads past the end of the string within the page, and
   Picinae needs no page argument.

   SPECIFICATION (man 3 strchr, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *strchr(const char *s, int c);

     DESCRIPTION
            The  strchr() function returns a pointer to the first occurrence of the
            character c in the string s.

            Here "character" means "byte"; these functions do not work with wide or
            multibyte characters.

     RETURN VALUE
            The strchr() and strrchr() functions return a pointer  to  the  matched
            character  or NULL if the character is not found.  The terminating null
            byte is considered part of the string, so that if  c  is  specified  as
            '\0', these functions return a pointer to the terminator.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            __strchr_avx2 at 0x29d200 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            canonical temporaries, entry rebased to 0; see strchr_avx2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = c (only the low byte c8 = c mod 256 matters);
            m = memory on entry.  K is the index of the first hit: the bytes
            s+0 .. s+K-1 are neither 0 nor c8, and the byte at s+K is 0 or c8
            (fhit m s c8 K; every NUL-terminated string has one, see
            fhit_of_slen).  s + K < 2^64.
   Output:  On return, RAX = s + K if the byte at s+K is c8, and 0 (NULL)
            otherwise; RSP is unchanged.  strchr writes no memory.
 *)
