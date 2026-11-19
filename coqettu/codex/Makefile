SHELL := /bin/bash
ROCQ ?= rocq
ROOT := ../..
FLAGS := -q -R $(ROOT) Picinae
# audit.v is a diagnostic script loaded once by check_assumptions.py.
SOURCES := $(filter-out x86/audit.v,$(wildcard x86/*.v))
PROOFS := $(wildcard x86/*_proof.v)
OBJECTS := $(SOURCES:.v=.vo)
MODULES := $(patsubst x86/%.v,Picinae.coqettu.codex.x86.%,$(SOURCES))
MUSL_LIB := $(abspath ../alpine_musl/x86/lib)

.PHONY: all check core provenance smoke adapter-check
all: $(OBJECTS)

# Build the shared Picinae prerequisites using the repository's configuration.
core:
	ulimit -v 8000000; $(MAKE) -C $(ROOT) Picinae_i386.vo Picinae_numbers.vo

x86/%.vo: x86/%.v
	ulimit -v 8000000; $(ROCQ) c $(FLAGS) $<

$(PROOFS:.v=.vo): x86/%_proof.vo: x86/%_proof.v x86/%_i386.vo x86/i386_common.vo x86/i386_bits.vo
	ulimit -v 8000000; $(ROCQ) c $(FLAGS) $<

x86/i386_casecmp.vo: x86/i386_strings.vo x86/i386_compare.vo x86/i386_ascii.vo x86/tolower_proof.vo
x86/i386_call_pair.vo: x86/i386_deep_stack.vo
x86/strcasecmp_l_support.vo: x86/strcasecmp_l_i386.vo x86/strcasecmp_proof.vo x86/i386_binary_call.vo
x86/strcasecmp_l_proof.vo: x86/strcasecmp_l_support.vo x86/i386_calls.vo
x86/i386_string_copy.vo: x86/i386_byte_copy_word.vo x86/i386_stack2.vo x86/i386_binary_call.vo
x86/stpcpy_proof.vo: x86/stpcpy_i386.vo x86/i386_string_copy.vo
x86/strcpy_support.vo: x86/strcpy_i386.vo x86/stpcpy_proof.vo x86/i386_string_copy.vo
x86/strcpy_proof.vo: x86/strcpy_support.vo x86/i386_calls.vo
x86/strncat_support.vo: x86/strncat_i386.vo x86/i386_byte_copy.vo x86/i386_ternary_call.vo x86/i386_search_arith.vo x86/pc_thunk_bx_i386.vo x86/strlen_proof.vo
x86/strncat_proof.vo: x86/strncat_support.vo x86/i386_calls.vo
x86/i386_byte_copy_word.vo: x86/i386_byte_copy.vo
x86/i386_byte_copy.vo: x86/i386_memory.vo x86/i386_strings.vo
x86/i386_tls_call.vo: x86/i386_binary_call.vo
x86/strcoll_support.vo: x86/strcoll_i386.vo x86/strcoll_l_proof.vo x86/i386_tls_call.vo
x86/strcoll_proof.vo: x86/strcoll_support.vo x86/i386_calls.vo
x86/wcscoll_support.vo: x86/wcscoll_i386.vo x86/wcscoll_l_proof.vo x86/i386_tls_call.vo
x86/wcscoll_proof.vo: x86/wcscoll_support.vo x86/i386_calls.vo
x86/index_support.vo: x86/index_i386.vo x86/strchr_proof.vo x86/i386_binary_call.vo
x86/index_proof.vo: x86/index_support.vo x86/i386_calls.vo
x86/rindex_support.vo: x86/rindex_i386.vo x86/strrchr_proof.vo x86/i386_binary_call.vo
x86/rindex_proof.vo: x86/rindex_support.vo x86/i386_calls.vo
x86/i386_ternary_call.vo: x86/i386_binary_call.vo
x86/i386_casecmp_bounded.vo: x86/i386_casecmp.vo x86/i386_search_arith.vo x86/i386_compare.vo
x86/strncasecmp_l_support.vo: x86/strncasecmp_l_i386.vo x86/strncasecmp_support.vo x86/i386_ternary_call.vo x86/pc_thunk_bx_i386.vo
x86/strncasecmp_l_proof.vo: x86/strncasecmp_l_support.vo x86/strncasecmp_proof.vo x86/i386_calls.vo
x86/strncasecmp_support.vo: x86/strncasecmp_i386.vo x86/pc_thunk_ax_i386.vo x86/i386_casecmp_bounded.vo x86/i386_call_pair.vo x86/i386_stack4.vo x86/i386_binary_call.vo x86/tolower_proof.vo
x86/strncasecmp_proof.vo: x86/strncasecmp_support.vo x86/i386_calls.vo
x86/strcasecmp_support.vo: x86/strcasecmp_i386.vo x86/i386_casecmp.vo x86/i386_call_pair.vo x86/i386_stack4.vo x86/i386_binary_call.vo x86/tolower_proof.vo
x86/strcasecmp_proof.vo: x86/strcasecmp_support.vo x86/i386_calls.vo
x86/iswblank_support.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_deep_stack.vo x86/iswblank_i386.vo x86/pc_thunk_bx_i386.vo x86/isblank_i386.vo
x86/iswblank_proof.vo: x86/iswblank_support.vo x86/i386_calls.vo x86/isblank_proof.vo
x86/bcmp_support.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_compare.vo x86/i386_deep_stack.vo x86/bcmp_i386.vo x86/pc_thunk_bx_i386.vo x86/memcmp_i386.vo
x86/bcmp_proof.vo: x86/bcmp_support.vo x86/i386_calls.vo x86/memcmp_proof.vo
x86/iswxdigit_proof.vo: x86/i386_ascii.vo
x86/iswcntrl_proof.vo: x86/i386_wctype.vo
x86/i386_search_arith.vo: x86/i386_byte_search.vo x86/i386_bits.vo
x86/i386_stack4.vo: x86/i386_deep_stack.vo
x86/iswdigit_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/iswdigit_l_i386.vo x86/pc_thunk_bx_i386.vo x86/iswdigit_i386.vo
x86/iswdigit_l_proof.vo: x86/iswdigit_l_support.vo x86/iswdigit_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/iswxdigit_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/iswxdigit_l_i386.vo x86/pc_thunk_bx_i386.vo x86/iswxdigit_i386.vo
x86/iswxdigit_l_proof.vo: x86/iswxdigit_l_support.vo x86/iswxdigit_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isalnum_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isalnum_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isalnum_i386.vo
x86/isalnum_l_proof.vo: x86/isalnum_l_support.vo x86/isalnum_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isalpha_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isalpha_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isalpha_i386.vo
x86/isalpha_l_proof.vo: x86/isalpha_l_support.vo x86/isalpha_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isblank_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isblank_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isblank_i386.vo
x86/isblank_l_proof.vo: x86/isblank_l_support.vo x86/isblank_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/iscntrl_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/iscntrl_l_i386.vo x86/pc_thunk_bx_i386.vo x86/iscntrl_i386.vo
x86/iscntrl_l_proof.vo: x86/iscntrl_l_support.vo x86/iscntrl_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isdigit_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isdigit_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isdigit_i386.vo
x86/isdigit_l_proof.vo: x86/isdigit_l_support.vo x86/isdigit_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isgraph_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isgraph_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isgraph_i386.vo
x86/isgraph_l_proof.vo: x86/isgraph_l_support.vo x86/isgraph_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/islower_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/islower_l_i386.vo x86/pc_thunk_bx_i386.vo x86/islower_i386.vo
x86/islower_l_proof.vo: x86/islower_l_support.vo x86/islower_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isprint_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isprint_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isprint_i386.vo
x86/isprint_l_proof.vo: x86/isprint_l_support.vo x86/isprint_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isspace_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isspace_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isspace_i386.vo
x86/isspace_l_proof.vo: x86/isspace_l_support.vo x86/isspace_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isupper_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isupper_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isupper_i386.vo
x86/isupper_l_proof.vo: x86/isupper_l_support.vo x86/isupper_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/isxdigit_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/isxdigit_l_i386.vo x86/pc_thunk_bx_i386.vo x86/isxdigit_i386.vo
x86/isxdigit_l_proof.vo: x86/isxdigit_l_support.vo x86/isxdigit_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/i386_named_string.vo: x86/i386_stringcmp.vo
x86/wctype_l_support.vo: x86/wctype_l_i386.vo x86/wctype_proof.vo x86/i386_named_string.vo x86/i386_binary_call.vo
x86/wctype_l_proof.vo: x86/wctype_l_support.vo x86/i386_calls.vo
x86/wctype_support.vo: x86/wctype_i386.vo x86/i386_named_string.vo x86/strcmp_proof.vo x86/i386_stack4.vo x86/i386_binary_call.vo
x86/wctype_proof.vo: x86/wctype_support.vo x86/i386_calls.vo
x86/wctrans_l_support.vo: x86/wctrans_l_i386.vo x86/wctrans_proof.vo x86/i386_binary_call.vo
x86/wctrans_l_proof.vo: x86/wctrans_l_support.vo x86/i386_calls.vo
x86/wctrans_support.vo: x86/wctrans_i386.vo x86/strcmp_proof.vo x86/i386_binary_call.vo
x86/wctrans_proof.vo: x86/wctrans_support.vo x86/i386_calls.vo
x86/strchr_support.vo: x86/strchr_i386.vo x86/strchrnul_proof.vo x86/i386_binary_call.vo
x86/strchr_proof.vo: x86/strchr_support.vo x86/i386_calls.vo
x86/strchrnul_support.vo: x86/i386_common.vo x86/i386_binary_call.vo x86/i386_stack4.vo x86/i386_search_arith.vo x86/strchrnul_i386.vo x86/pc_thunk_bx_i386.vo x86/strlen_proof.vo
x86/strchrnul_proof.vo: x86/strchrnul_support.vo x86/strlen_proof.vo x86/i386_calls.vo
x86/strrchr_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/i386_binary_call.vo x86/i386_stack2.vo x86/i386_reverse.vo x86/strrchr_i386.vo x86/pc_thunk_bx_i386.vo x86/strlen_proof.vo x86/memrchr_proof.vo
x86/strrchr_proof.vo: x86/strrchr_support.vo x86/strlen_proof.vo x86/memrchr_proof.vo x86/i386_calls.vo
x86/wcsrchr_support.vo: x86/i386_common.vo x86/i386_backward.vo x86/i386_binary_call.vo x86/i386_wsearch.vo x86/wcsrchr_i386.vo x86/pc_thunk_bx_i386.vo x86/wcslen_proof.vo
x86/wcsrchr_proof.vo: x86/wcsrchr_support.vo x86/wcslen_proof.vo x86/i386_calls.vo
x86/i386_wsearch.vo: x86/i386_wstrlen.vo
x86/wcschr_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/i386_binary_call.vo x86/i386_wsearch.vo x86/wcschr_i386.vo x86/pc_thunk_bx_i386.vo x86/wcslen_proof.vo
x86/wcschr_proof.vo: x86/wcschr_support.vo x86/wcslen_proof.vo x86/i386_calls.vo
x86/strcoll_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/i386_binary_call.vo x86/strcoll_l_i386.vo x86/pc_thunk_bx_i386.vo x86/strcmp_i386.vo x86/strcmp_proof.vo x86/i386_stringcmp.vo
x86/strcoll_l_proof.vo: x86/strcoll_l_support.vo x86/strcmp_proof.vo x86/i386_calls.vo x86/i386_binary_call.vo
x86/wcscoll_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/i386_binary_call.vo x86/wcscoll_l_i386.vo x86/pc_thunk_bx_i386.vo x86/wcscmp_i386.vo x86/wcscmp_proof.vo x86/i386_stringcmp.vo
x86/wcscoll_l_proof.vo: x86/wcscoll_l_support.vo x86/wcscmp_proof.vo x86/i386_calls.vo x86/i386_binary_call.vo
x86/i386_binary_call.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_stack2.vo x86/i386_deep_stack.vo x86/i386_stack4.vo x86/i386_unary_call.vo x86/i386_strings.vo x86/i386_wstringcmp.vo
x86/iswcntrl_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/iswcntrl_l_i386.vo x86/pc_thunk_bx_i386.vo x86/iswcntrl_i386.vo
x86/iswcntrl_l_proof.vo: x86/iswcntrl_l_support.vo x86/iswcntrl_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/ispunct_l_support.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_deep_stack.vo x86/i386_unary_call.vo x86/ispunct_l_i386.vo x86/ispunct_support.vo
x86/ispunct_l_proof.vo: x86/ispunct_l_support.vo x86/ispunct_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/iswblank_l_support.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_deep_stack.vo x86/i386_unary_call.vo x86/iswblank_l_i386.vo x86/iswblank_support.vo
x86/iswblank_l_proof.vo: x86/iswblank_l_support.vo x86/iswblank_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/tolower_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/tolower_l_i386.vo x86/pc_thunk_bx_i386.vo x86/tolower_i386.vo
x86/tolower_l_proof.vo: x86/tolower_l_support.vo x86/tolower_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/toupper_l_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/toupper_l_i386.vo x86/pc_thunk_bx_i386.vo x86/toupper_i386.vo
x86/toupper_l_proof.vo: x86/toupper_l_support.vo x86/toupper_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo
x86/ispunct_support.vo: x86/i386_common.vo x86/i386_unary_call.vo x86/ispunct_i386.vo x86/pc_thunk_bx_i386.vo x86/isalnum_i386.vo
x86/ispunct_proof.vo: x86/ispunct_support.vo x86/isalnum_proof.vo x86/i386_calls.vo x86/i386_unary_call.vo x86/i386_ascii.vo
x86/i386_unary_call.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_deep_stack.vo x86/i386_calls.vo
x86/wcsnlen_support.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_deep_stack.vo x86/i386_stack4.vo x86/i386_strings.vo x86/i386_wstrlen.vo x86/wcsnlen_i386.vo x86/pc_thunk_bx_i386.vo x86/wmemchr_i386.vo x86/wmemchr_proof.vo
x86/wcsnlen_proof.vo: x86/wcsnlen_support.vo x86/i386_calls.vo x86/wmemchr_proof.vo x86/i386_wstrlen.vo
x86/strnlen_support.vo: x86/i386_common.vo x86/i386_stack.vo x86/i386_deep_stack.vo x86/i386_stack4.vo x86/i386_strings.vo x86/i386_byte_search.vo x86/strnlen_i386.vo x86/pc_thunk_bx_i386.vo x86/memchr_i386.vo x86/memchr_support.vo
x86/strnlen_proof.vo: x86/strnlen_support.vo x86/memchr_proof.vo x86/i386_calls.vo
x86/memchr_support.vo: x86/i386_stack4.vo x86/i386_common.vo x86/i386_byte_search.vo x86/i386_search_arith.vo
x86/memchr_proof.vo: x86/memchr_support.vo x86/i386_stack4.vo x86/i386_byte_search.vo x86/i386_search_arith.vo
x86/i386_byte_search.vo: x86/i386_strings.vo
x86/i386_wstrlen.vo: x86/i386_strings.vo
x86/wcslen_proof.vo: x86/i386_wstrlen.vo
x86/i386_wstringcmp.vo: x86/i386_compare.vo x86/i386_stack2.vo x86/i386_stack.vo x86/i386_signed.vo
x86/wcscmp_proof.vo: x86/i386_wstringcmp.vo x86/i386_stack2.vo x86/i386_signed.vo
x86/wcsncmp_proof.vo: x86/i386_wstringcmp.vo x86/i386_stack.vo x86/i386_signed.vo x86/i386_strings.vo
x86/i386_abs64.vo: x86/i386_common.vo x86/i386_bits.vo
x86/llabs_proof.vo x86/imaxabs_proof.vo: x86/i386_abs64.vo x86/i386_stack.vo
x86/i386_ascii.vo: x86/i386_bits.vo
x86/isxdigit_proof.vo x86/isalpha_proof.vo x86/isalnum_proof.vo x86/isblank_proof.vo x86/iscntrl_proof.vo x86/isspace_proof.vo x86/tolower_proof.vo x86/toupper_proof.vo: x86/i386_ascii.vo
x86/wmemset_proof.vo: x86/i386_memory.vo x86/i386_strings.vo
x86/strlen_proof.vo: x86/i386_strings.vo
x86/wmemchr_proof.vo: x86/i386_strings.vo
x86/memcmp_proof.vo: x86/i386_strings.vo x86/i386_stack.vo x86/i386_compare.vo
x86/wmemcmp_proof.vo: x86/i386_strings.vo x86/i386_stack.vo x86/i386_compare.vo
x86/wmemcmp_proof.vo: x86/i386_signed.vo
x86/i386_signed.vo: x86/i386_bits.vo
x86/i386_compare.vo: x86/i386_bits.vo
x86/i386_reverse.vo: x86/i386_stack2.vo
x86/i386_stack2.vo: x86/i386_stack.vo
x86/i386_stringcmp.vo: x86/i386_strings.vo x86/i386_compare.vo x86/i386_stack2.vo
x86/strcmp_proof.vo: x86/i386_stringcmp.vo x86/i386_stack2.vo
x86/memrchr_proof.vo: x86/i386_reverse.vo x86/i386_stack2.vo x86/i386_strings.vo
x86/i386_bsf.vo: x86/i386_rep.vo
x86/ffs_proof.vo: x86/i386_bsf.vo
x86/ffsl_proof.vo: x86/i386_bsf.vo
x86/ffsll_proof.vo: x86/i386_bsf.vo x86/i386_stack.vo

x86/audit.vo: x86/audit.v $(patsubst %.v,%.vo,$(wildcard x86/*_proof.v))
	ulimit -v 8000000; $(ROCQ) c $(FLAGS) x86/audit.v

provenance:
	python3 verify_provenance.py --manifest .build/lift_manifest.json

.build/native_smoke: x86/native_smoke.c $(MUSL_LIB)/libc.musl-x86.so.1
	mkdir -p .build
	$(CC) -m32 -O2 -Wall -Wextra -Werror -fno-builtin -fno-stack-protector -fno-pie -no-pie -nostdlib \
	  -mno-sse -mno-mmx -Wl,-e,_start -Wl,-z,noexecstack \
	  -Wl,--dynamic-linker=$(MUSL_LIB)/libc.musl-x86.so.1 -Wl,-rpath,$(MUSL_LIB) \
	  x86/native_smoke.c $(MUSL_LIB)/libc.musl-x86.so.1 -o $@

smoke: provenance .build/native_smoke
	./.build/native_smoke

adapter-check:
	python3 -m unittest discover -s tests -p 'test_*.py'

check: all provenance adapter-check
	ulimit -v 8000000; python3 check_assumptions.py
	ulimit -v 8000000; $(ROCQ) check -silent -R $(ROOT) Picinae $(MODULES)
