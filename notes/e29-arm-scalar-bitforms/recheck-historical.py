#!/usr/bin/env python3
"""Run the existing e11 finite historical comparison against fresh Ghidra IL.

Only output destinations and the new-IL input directory are rerouted. The
historical programs, old diffs and comparison receipt are never overwritten.
"""
from pathlib import Path
import sys
repo = Path(__file__).resolve().parents[2]
fresh = Path(sys.argv[1]).resolve()
out = Path(__file__).resolve().parent / 'historical'
out.mkdir(exist_ok=False)
path = repo / 'notes/e11-canonical-lifter/compare-il.py'
script = path.read_text()
script = script.replace("repo/f'Examples/claude/lifter/scalar_smoke/e11_{name}_arm8.v'", "fresh/f'e11_{name}_arm8.v'")
script = script.replace("repo/f'notes/e11-canonical-lifter/{name}.diff'", "out/f'{name}.diff'")
script = script.replace("repo/'notes/e11-canonical-lifter/comparison.json'", "out/'comparison.json'")
# The upstream diff header uses relative_to(repo); fresh toolchain input is
# outside the repository, so label it by its absolute path instead.
script = script.replace('str(new_path.relative_to(repo))', 'str(new_path)')
exec(compile(script, str(path), 'exec'), {'__file__': str(path), 'fresh': fresh, 'out': out})
