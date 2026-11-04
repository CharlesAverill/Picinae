#!/bin/bash
set -euo pipefail
export PROOF_MEMORY_KB=3000000 PROOF_STACK_KB=65536
mapfile -t theorem_names < <(python3 - <<'PY'
import re
from pathlib import Path
s=Path('Examples/FreeRTOS/armv6m_list_refinement.v').read_text()
starts=list(re.finditer(r'^(?:Lemma|Theorem)\s+(\w+)\s*:',s,re.M))
for i,m in enumerate(starts):
    body=s[m.end():starts[i+1].start() if i+1<len(starts) else len(s)]
    if re.search(r'\bProof\.',body) and re.search(r'\bQed\.',body):
        print(m[1])
PY
)
bash tools/print-assumptions.sh Picinae.Examples.FreeRTOS.armv6m_list_refinement "${theorem_names[@]}"
bash tools/print-assumptions.sh Picinae.Examples.FreeRTOS.armv6m_vListInsertEnd_proof \
  insert_end_welltyped insert_end_nwc insert_end_at_bx insert_end_memory_fields insert_end_memory_frame
bash tools/print-assumptions.sh Picinae.Examples.FreeRTOS.armv6m_uxListRemove_proof \
  list_remove_welltyped list_remove_nwc list_remove_at_bx list_remove_mem_effects list_remove_mem_frame
