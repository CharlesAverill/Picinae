#!/usr/bin/env python3
"""Reject unexpected logical axioms in the completed correctness contracts."""
import re
import subprocess
from pathlib import Path

directory = Path(__file__).resolve().parent
audit = directory / "x86/audit.v"
contracts = re.findall(r"^Print Assumptions ([A-Za-z_][\w.]*)\.", audit.read_text(), re.M)
required = {
    f"{proof.stem.removesuffix('_proof')}_{suffix}"
    for proof in (directory / "x86").glob("*_proof.v")
    for suffix in ("correct", "returns")
}
if len(contracts) != len(set(contracts)) or set(contracts) != required:
    raise SystemExit(
        f"Audit inventory differs from proof sources: "
        f"missing={sorted(required - set(contracts))}, "
        f"unexpected={sorted(set(contracts) - required)}, "
        f"duplicates={len(contracts) - len(set(contracts))}"
    )
expected = len(contracts)
result = subprocess.run(
    ["rocq", "repl", "-q", "-batch", "-R", str(directory.parent.parent), "Picinae", "-l", str(audit)],
    text=True, capture_output=True, check=True,
)
output = result.stdout + result.stderr
reports = re.findall(r"^(?:Axioms:|Closed under the global context)", output, re.M)
if not expected or len(reports) != expected:
    raise SystemExit(f"Expected {expected} assumption reports, received {len(reports)}.\n{output}")
names = set(re.findall(r"^([A-Za-z_][\w.]*)\s*:", output, re.M)) - {"Axioms"}
allowed = {"FunctionalExtensionality.functional_extensionality_dep"}
if names - allowed:
    raise SystemExit(f"Unexpected logical assumptions: {sorted(names - allowed)}\n{output}")
print(f"Audited {expected} contracts: only Picinae's existing functional-extensionality axiom.")
