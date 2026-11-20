# Confirmed copy entry matrix

Every address is an ELF virtual address; add `0x100000` for the original Ghidra image. Exact symbol extents, byte hashes, aliases and shared-body edges are in `inventory.json`. Suffixes apply to `__<column>_<suffix>`. Equal addresses are aliases; SSSE3 memcpy and memmove entries differ. Mempcpy entries require their own return adapter.

| Suffix | memcpy | memmove | mempcpy | memcpy_chk | memmove_chk | mempcpy_chk |
|---|---|---|---|---|---|---|
| avx512_no_vzeroupper | 0x1a3cf0 | 0x1a3cf0 | 0x1a3cd0 | 0x1a3ce0 | 0x1a3ce0 | 0x1a3cc0 |
| avx512_unaligned | 0x1a67b0 | 0x1a67b0 | 0x1a6790 | 0x1a67a0 | 0x1a67a0 | 0x1a6780 |
| avx512_unaligned_erms | 0x1a6840 | 0x1a6840 | 0x1a6800 | 0x1a6810 | 0x1a6810 | 0x1a67f0 |
| avx_unaligned | 0x1a07b0 | 0x1a07b0 | 0x1a0790 | 0x1a07a0 | 0x1a07a0 | 0x1a0780 |
| avx_unaligned_erms | 0x1a0840 | 0x1a0840 | 0x1a0800 | 0x1a0810 | 0x1a0810 | 0x1a07f0 |
| avx_unaligned_erms_rtm | 0x1a7cc0 | 0x1a7cc0 | 0x1a7c80 | 0x1a7c90 | 0x1a7c90 | 0x1a7c70 |
| avx_unaligned_rtm | 0x1a7c30 | 0x1a7c30 | 0x1a7c10 | 0x1a7c20 | 0x1a7c20 | 0x1a7c00 |
| erms | 0xc48e0 | 0xc48e0 | 0xc48b0 | 0xc48d0 | 0xc48d0 | 0xc48a0 |
| evex_unaligned | 0x1aedb0 | 0x1aedb0 | 0x1aed90 | 0x1aeda0 | 0x1aeda0 | 0x1aed80 |
| evex_unaligned_erms | 0x1aee40 | 0x1aee40 | 0x1aee00 | 0x1aee10 | 0x1aee10 | 0x1aedf0 |
| sse2_unaligned | 0xc4870 | 0xc4870 | 0xc4850 | 0xc4860 | 0xc4860 | 0xc4840 |
| sse2_unaligned_erms | 0xc4980 | 0xc4980 | 0xc4930 | 0xc4940 | 0xc4940 | 0xc4920 |
| ssse3 | 0x17ac80 | 0x17d660 | 0x17ac60 | 0x17ac70 | 0x17d650 | 0x17ac50 |
| ssse3_back | 0x180210 | 0x182d00 | 0x1801f0 | 0x180200 | 0x182cf0 | 0x1801e0 |

# Subsequent string wave

These suffixes are observed debug symbols, including internal helpers and compatibility entries. Runtime-selectable candidates and CPU conditions are separately recorded in `ifunc-implementations.json`.

| Family | Observed suffixes |
|---|---|
| memset | `avx2_erms`, `avx2_erms_rtm`, `avx2_unaligned`, `avx2_unaligned_erms`, `avx2_unaligned_erms_rtm`, `avx2_unaligned_rtm`, `avx512_erms`, `avx512_no_vzeroupper`, `avx512_unaligned`, `avx512_unaligned_erms`, `chk`, `chk@@GLIBC_2.3.4`, `chk_avx2_unaligned`, `chk_avx2_unaligned_erms`, `chk_avx2_unaligned_erms_rtm`, `chk_avx2_unaligned_rtm`, `chk_avx512_no_vzeroupper`, `chk_avx512_unaligned`, `chk_avx512_unaligned_erms`, `chk_erms`, `chk_evex_unaligned`, `chk_evex_unaligned_erms`, `chk_sse2_unaligned`, `chk_sse2_unaligned_erms`, `erms`, `evex_erms`, `evex_unaligned`, `evex_unaligned_erms`, `sse2_unaligned`, `sse2_unaligned_erms` |
| memcmp | `avx2_movbe`, `avx2_movbe_rtm`, `evex_movbe`, `sse2`, `sse4_1`, `ssse3` |
| strlen | `avx2`, `avx2_rtm`, `evex`, `sse2` |
| strcpy | `avx2`, `avx2_rtm`, `chk`, `chk@@GLIBC_2.3.4`, `evex`, `small@GLIBC_2.2.5`, `sse2`, `sse2_unaligned`, `ssse3` |
| strcmp | `avx2`, `avx2_rtm`, `evex`, `sse2`, `sse2_unaligned`, `sse42`, `ssse3` |
| memchr | `avx2`, `avx2_rtm`, `evex`, `evex_rtm`, `sse2` |
| strnlen | `avx2`, `avx2_rtm`, `evex`, `sse2` |
| strncmp | `avx2`, `avx2_rtm`, `evex`, `sse2`, `sse42`, `ssse3` |
| strncpy | `avx2`, `avx2_rtm`, `chk`, `chk@@GLIBC_2.3.4`, `evex`, `sse2`, `sse2_unaligned`, `ssse3` |
| stpcpy | `avx2`, `avx2_rtm`, `chk`, `chk@@GLIBC_2.3.4`, `evex`, `small@GLIBC_2.2.5`, `sse2`, `sse2_unaligned`, `ssse3` |
| strcat | `avx2`, `avx2_rtm`, `chk`, `chk@@GLIBC_2.3.4`, `evex`, `sse2`, `sse2_unaligned`, `ssse3` |
| bcmp |  |
| bcopy |  |
| bzero |  |
| memcmpeq | `avx2`, `avx2_rtm`, `evex`, `sse2` |
| memccpy |  |
| memrchr | `avx2`, `avx2_rtm`, `evex`, `sse2` |
| rawmemchr | `avx2`, `avx2_rtm`, `evex`, `evex_rtm`, `sse2` |
| strchr | `avx2`, `avx2_rtm`, `evex`, `sse2`, `sse2_no_bsf` |
| strchrnul | `avx2`, `avx2_rtm`, `evex`, `sse2` |
| strrchr | `avx2`, `avx2_rtm`, `evex`, `sse2` |
| strspn | `c1@GLIBC_2.2.5`, `c2@GLIBC_2.2.5`, `c3@GLIBC_2.2.5`, `sse2`, `sse42` |
| strcspn | `c1@GLIBC_2.2.5`, `c2@GLIBC_2.2.5`, `c3@GLIBC_2.2.5`, `sse2`, `sse42` |
| strpbrk | `c2@GLIBC_2.2.5`, `c3@GLIBC_2.2.5`, `sse2`, `sse42` |
| stpncpy | `avx2`, `avx2_rtm`, `chk`, `chk@@GLIBC_2.4`, `evex`, `sse2`, `sse2_unaligned`, `ssse3` |
| strncat | `avx2`, `avx2_rtm`, `chk`, `chk@@GLIBC_2.3.4`, `evex`, `sse2`, `sse2_unaligned`, `ssse3` |
| strstr | `sse2`, `sse2_unaligned` |
| strcasestr |  |
| memmem |  |
