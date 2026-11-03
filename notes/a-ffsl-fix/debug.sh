#!/usr/bin/env bash
set -eu
python3 - <<'PY'
from pathlib import Path
source = Path('Examples/claude/arm8_ffsl_proof.v').read_text()
rest = source[source.index('Lemma ffsl_asr_upper:'):]
Path('notes/a-ffsl-fix/Debug.v').write_text('Require Import Picinae_armv8 ffsl_arm8 ffsll_arm8 arm8_common FixDebug.DebugPrefix.\nFrom Stdlib Require Import NArith ZArith Lia List.\nImport ARM8Notations ListNotations.\nOpen Scope N.\n'+rest)
PY
exec /home/charles/code/friends/.toolchains/arm-validation/picinae-env bash --noprofile --norc -e -c 'ulimit -v 3000000; ulimit -s 65536; rocq compile -time -q -R _build/default Picinae -Q notes/a-ffsl-fix FixDebug notes/a-ffsl-fix/Debug.v'
