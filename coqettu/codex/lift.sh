#!/usr/bin/env bash
# Reproduce the Codex i386 lifts without importing other models' artifacts.
set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_dir=$(cd -- "$script_dir/../.." && pwd)
ghidra_dir=${GHIDRA_INSTALL_DIR:-/home/ixb/research/programs/ghidra_12.0_PUBLIC}
project_dir=${COQETTU_GHIDRA_PROJECT_DIR:-/tmp/coqettu-codex-ghidra}
project_name=${COQETTU_GHIDRA_PROJECT_NAME:-musl_x86}
output_dir=${COQETTU_LIFT_OUTPUT_DIR:-$script_dir/x86}
binary="$repo_dir/coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1"
expected=8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
actual=$(sha256sum -- "$binary")
if [[ ${actual%% *} != "$expected" ]]; then
  printf 'Unexpected musl binary SHA256: %s\n' "${actual%% *}" >&2
  exit 1
fi
mkdir -p -- "$project_dir" "$script_dir/.build"
if [[ -f "$project_dir/$project_name.gpr" ]]; then
  input=(-process ld-musl-i386.so.1 -noanalysis)
else
  input=(-import "$binary")
fi
functions='^(toascii|htonl|htons|ntohl|ntohs|isascii|isdigit|isgraph|islower|isprint|isupper|abs|labs|strlen|memcmp|bcmp|strnlen|wmemchr|wmemcmp|ffs|ffsl|ffsll|strcmp|memrchr|wmemset|isalpha|isalnum|isblank|iscntrl|isspace|tolower|toupper|wcscmp|wcsncmp|isxdigit|llabs|imaxabs|wcslen|wcsnlen|memchr|iswdigit|iswxdigit|iswcntrl|iswblank|iswdigit_l|iswxdigit_l|isalnum_l|isalpha_l|isblank_l|iscntrl_l|isdigit_l|isgraph_l|islower_l|isprint_l|isspace_l|isupper_l|isxdigit_l|ispunct|tolower_l|toupper_l|iswblank_l|ispunct_l|iswcntrl_l|strcoll_l|wcscoll_l|wcschr|wcsrchr|strrchr|strchrnul|strchr|wctrans|wctrans_l|wctype|wctype_l|strcasecmp|strcasecmp_l|strncasecmp|strncasecmp_l|index|rindex|strcoll|wcscoll|strncat|stpcpy|strcpy)$'
"$ghidra_dir/support/pyghidraRun" --headless "$project_dir" "$project_name" \
  "${input[@]}" -scriptPath "$script_dir" \
  -postScript pcode2coq_codex.py --functionRegex "$functions" \
  --globalAddressing --strictFailure --typeCheck --outputDir "$output_dir" \
  2>&1 | tee "$script_dir/.build/lift.log"
# Ghidra can report a post-script exception while returning process status zero.
if rg -q '^ERROR|Traceback|NotImplementedError' "$script_dir/.build/lift.log"; then
  printf 'Lifting reported an error; inspect .build/lift.log.\n' >&2
  exit 1
fi
for symbol in toascii htonl htons ntohl ntohs isascii isdigit isgraph islower \
  isprint isupper abs labs strlen memcmp bcmp strnlen wmemchr wmemcmp ffs ffsl ffsll strcmp memrchr wmemset isalpha isalnum isblank iscntrl isspace tolower toupper wcscmp wcsncmp isxdigit llabs imaxabs wcslen wcsnlen memchr iswdigit iswxdigit iswcntrl iswblank iswdigit_l iswxdigit_l isalnum_l isalpha_l isblank_l iscntrl_l isdigit_l isgraph_l islower_l isprint_l isspace_l isupper_l isxdigit_l ispunct tolower_l toupper_l iswblank_l ispunct_l iswcntrl_l strcoll_l wcscoll_l wcschr wcsrchr strrchr strchrnul strchr wctrans wctrans_l wctype wctype_l strcasecmp strcasecmp_l strncasecmp strncasecmp_l index rindex strcoll wcscoll strncat stpcpy strcpy; do
  if ! rg -q "Written: .*/${symbol}_i386.v" "$script_dir/.build/lift.log"; then
    printf 'No fresh lift reported for %s.\n' "$symbol" >&2
    exit 1
  fi
done
# The internal PIC thunk is not an exported ELF symbol. Lift it separately
# after releasing the project, with its address and exact bytes checked.
bash "$script_dir/lift_support.sh"
