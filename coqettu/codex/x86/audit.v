(* Logical assumptions of every completed public function contract. *)
From Picinae.coqettu.codex.x86 Require Import
  abs_proof
  bcmp_proof
  ffs_proof
  ffsl_proof
  ffsll_proof
  htonl_proof
  htons_proof
  imaxabs_proof
  index_proof
  isalnum_l_proof
  isalnum_proof
  isalpha_l_proof
  isalpha_proof
  isascii_proof
  isblank_l_proof
  isblank_proof
  iscntrl_l_proof
  iscntrl_proof
  isdigit_l_proof
  isdigit_proof
  isgraph_l_proof
  isgraph_proof
  islower_l_proof
  islower_proof
  isprint_l_proof
  isprint_proof
  ispunct_l_proof
  ispunct_proof
  isspace_l_proof
  isspace_proof
  isupper_l_proof
  isupper_proof
  iswblank_l_proof
  iswblank_proof
  iswcntrl_l_proof
  iswcntrl_proof
  iswdigit_l_proof
  iswdigit_proof
  iswxdigit_l_proof
  iswxdigit_proof
  isxdigit_l_proof
  isxdigit_proof
  labs_proof
  llabs_proof
  memchr_proof
  memcmp_proof
  memrchr_proof
  ntohl_proof
  ntohs_proof
  rindex_proof
  strcasecmp_l_proof
  strcasecmp_proof
  strchr_proof
  strchrnul_proof
  strcmp_proof
  strcoll_l_proof
  strcoll_proof
  strlen_proof
  strncasecmp_l_proof
  strncasecmp_proof
  strncat_proof
  strnlen_proof
  strrchr_proof
  toascii_proof
  tolower_l_proof
  tolower_proof
  toupper_l_proof
  toupper_proof
  wcschr_proof
  wcscmp_proof
  wcscoll_l_proof
  wcscoll_proof
  wcslen_proof
  wcsncmp_proof
  wcsnlen_proof
  wcsrchr_proof
  wctrans_l_proof
  wctrans_proof
  wctype_l_proof
  wctype_proof
  wmemchr_proof
  wmemcmp_proof
  wmemset_proof.

Print Assumptions abs_correct.
Print Assumptions abs_returns.
Print Assumptions bcmp_correct.
Print Assumptions bcmp_returns.
Print Assumptions ffs_correct.
Print Assumptions ffs_returns.
Print Assumptions ffsl_correct.
Print Assumptions ffsl_returns.
Print Assumptions ffsll_correct.
Print Assumptions ffsll_returns.
Print Assumptions htonl_correct.
Print Assumptions htonl_returns.
Print Assumptions htons_correct.
Print Assumptions htons_returns.
Print Assumptions imaxabs_correct.
Print Assumptions imaxabs_returns.
Print Assumptions index_correct.
Print Assumptions index_returns.
Print Assumptions isalnum_l_correct.
Print Assumptions isalnum_l_returns.
Print Assumptions isalnum_correct.
Print Assumptions isalnum_returns.
Print Assumptions isalpha_l_correct.
Print Assumptions isalpha_l_returns.
Print Assumptions isalpha_correct.
Print Assumptions isalpha_returns.
Print Assumptions isascii_correct.
Print Assumptions isascii_returns.
Print Assumptions isblank_l_correct.
Print Assumptions isblank_l_returns.
Print Assumptions isblank_correct.
Print Assumptions isblank_returns.
Print Assumptions iscntrl_l_correct.
Print Assumptions iscntrl_l_returns.
Print Assumptions iscntrl_correct.
Print Assumptions iscntrl_returns.
Print Assumptions isdigit_l_correct.
Print Assumptions isdigit_l_returns.
Print Assumptions isdigit_correct.
Print Assumptions isdigit_returns.
Print Assumptions isgraph_l_correct.
Print Assumptions isgraph_l_returns.
Print Assumptions isgraph_correct.
Print Assumptions isgraph_returns.
Print Assumptions islower_l_correct.
Print Assumptions islower_l_returns.
Print Assumptions islower_correct.
Print Assumptions islower_returns.
Print Assumptions isprint_l_correct.
Print Assumptions isprint_l_returns.
Print Assumptions isprint_correct.
Print Assumptions isprint_returns.
Print Assumptions ispunct_l_correct.
Print Assumptions ispunct_l_returns.
Print Assumptions ispunct_correct.
Print Assumptions ispunct_returns.
Print Assumptions isspace_l_correct.
Print Assumptions isspace_l_returns.
Print Assumptions isspace_correct.
Print Assumptions isspace_returns.
Print Assumptions isupper_l_correct.
Print Assumptions isupper_l_returns.
Print Assumptions isupper_correct.
Print Assumptions isupper_returns.
Print Assumptions iswblank_l_correct.
Print Assumptions iswblank_l_returns.
Print Assumptions iswblank_correct.
Print Assumptions iswblank_returns.
Print Assumptions iswcntrl_l_correct.
Print Assumptions iswcntrl_l_returns.
Print Assumptions iswcntrl_correct.
Print Assumptions iswcntrl_returns.
Print Assumptions iswdigit_l_correct.
Print Assumptions iswdigit_l_returns.
Print Assumptions iswdigit_correct.
Print Assumptions iswdigit_returns.
Print Assumptions iswxdigit_l_correct.
Print Assumptions iswxdigit_l_returns.
Print Assumptions iswxdigit_correct.
Print Assumptions iswxdigit_returns.
Print Assumptions isxdigit_l_correct.
Print Assumptions isxdigit_l_returns.
Print Assumptions isxdigit_correct.
Print Assumptions isxdigit_returns.
Print Assumptions labs_correct.
Print Assumptions labs_returns.
Print Assumptions llabs_correct.
Print Assumptions llabs_returns.
Print Assumptions memchr_correct.
Print Assumptions memchr_returns.
Print Assumptions memcmp_correct.
Print Assumptions memcmp_returns.
Print Assumptions memrchr_correct.
Print Assumptions memrchr_returns.
Print Assumptions ntohl_correct.
Print Assumptions ntohl_returns.
Print Assumptions ntohs_correct.
Print Assumptions ntohs_returns.
Print Assumptions rindex_correct.
Print Assumptions rindex_returns.
Print Assumptions strcasecmp_l_correct.
Print Assumptions strcasecmp_l_returns.
Print Assumptions strcasecmp_correct.
Print Assumptions strcasecmp_returns.
Print Assumptions strchr_correct.
Print Assumptions strchr_returns.
Print Assumptions strchrnul_correct.
Print Assumptions strchrnul_returns.
Print Assumptions strcmp_correct.
Print Assumptions strcmp_returns.
Print Assumptions strcoll_l_correct.
Print Assumptions strcoll_l_returns.
Print Assumptions strcoll_correct.
Print Assumptions strcoll_returns.
Print Assumptions strlen_correct.
Print Assumptions strlen_returns.
Print Assumptions strncasecmp_l_correct.
Print Assumptions strncasecmp_l_returns.
Print Assumptions strncasecmp_correct.
Print Assumptions strncasecmp_returns.
Print Assumptions strncat_correct.
Print Assumptions strncat_returns.
Print Assumptions strnlen_correct.
Print Assumptions strnlen_returns.
Print Assumptions strrchr_correct.
Print Assumptions strrchr_returns.
Print Assumptions toascii_correct.
Print Assumptions toascii_returns.
Print Assumptions tolower_l_correct.
Print Assumptions tolower_l_returns.
Print Assumptions tolower_correct.
Print Assumptions tolower_returns.
Print Assumptions toupper_l_correct.
Print Assumptions toupper_l_returns.
Print Assumptions toupper_correct.
Print Assumptions toupper_returns.
Print Assumptions wcschr_correct.
Print Assumptions wcschr_returns.
Print Assumptions wcscmp_correct.
Print Assumptions wcscmp_returns.
Print Assumptions wcscoll_l_correct.
Print Assumptions wcscoll_l_returns.
Print Assumptions wcscoll_correct.
Print Assumptions wcscoll_returns.
Print Assumptions wcslen_correct.
Print Assumptions wcslen_returns.
Print Assumptions wcsncmp_correct.
Print Assumptions wcsncmp_returns.
Print Assumptions wcsnlen_correct.
Print Assumptions wcsnlen_returns.
Print Assumptions wcsrchr_correct.
Print Assumptions wcsrchr_returns.
Print Assumptions wctrans_l_correct.
Print Assumptions wctrans_l_returns.
Print Assumptions wctrans_correct.
Print Assumptions wctrans_returns.
Print Assumptions wctype_l_correct.
Print Assumptions wctype_l_returns.
Print Assumptions wctype_correct.
Print Assumptions wctype_returns.
Print Assumptions wmemchr_correct.
Print Assumptions wmemchr_returns.
Print Assumptions wmemcmp_correct.
Print Assumptions wmemcmp_returns.
Print Assumptions wmemset_correct.
Print Assumptions wmemset_returns.
