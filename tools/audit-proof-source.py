#!/usr/bin/env python3
"""Inventory suspicious Rocq tokens and reject additions relative to a base.

This is a source hygiene check, not a substitute for Print Assumptions. Nested
comments and strings are masked; existing module signature Parameters are
reported, not silently treated as new axioms. Uses only Python's stdlib.
"""

import argparse
from collections import Counter
import difflib
import os
from pathlib import Path
import re
import subprocess


TOKENS = re.compile(r"\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b")


def git(*args):
    return subprocess.check_output(["git", *args]).decode()


def mask(text):
    """Keep offsets/newlines, replacing nested comments and strings with spaces."""
    result = list(text)
    depth, quoted, i = 0, False, 0
    while i < len(text):
        if not quoted and text.startswith("(*", i):
            depth += 1
            result[i:i + 2] = "  "
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            result[i:i + 2] = "  "
            i += 2
        elif depth:
            if text[i] != "\n":
                result[i] = " "
            i += 1
        elif text[i] == '"':
            result[i] = " "
            if quoted and text.startswith('""', i):
                result[i + 1] = " "
                i += 2
            else:
                quoted = not quoted
                i += 1
        elif quoted:
            if text[i] != "\n":
                result[i] = " "
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError("unterminated comment or string")
    return "".join(result)


def findings(text):
    return [(i, m.group(), line.strip())
            for i, line in enumerate(mask(text).splitlines())
            for m in TOKENS.finditer(line)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, help="reviewed base commit/ref")
    parser.add_argument("paths", nargs="*", help="optional files/directories")
    args = parser.parse_args()
    root = Path(git("rev-parse", "--show-toplevel").strip())
    os.chdir(root)
    base = git("rev-parse", "--verify", args.base + "^{commit}").strip()
    baseline = set(git("ls-tree", "-rz", "--name-only", base).split("\0"))
    current = set(git("ls-files", "-z", "--cached", "--others",
                      "--exclude-standard").split("\0"))
    paths = sorted(p for p in baseline | current if p.endswith(".v") and
                   (not args.paths or any(p == x.rstrip("/") or
                    p.startswith(x.rstrip("/") + "/") for x in args.paths)))
    if not paths:
        parser.error("no .v source files selected")
    counts = {label: Counter() for label in ("BASELINE", "CURRENT", "NEW")}
    print(f"Base: {base}\nScope: {len(paths)} Rocq source files")
    for path in paths:
        old = git("show", f"{base}:{path}") if path in baseline else ""
        new = (root / path).read_text() if (root / path).is_file() else ""
        # Compare source after masking, so editing only comments is harmless.
        old_lines, new_lines = mask(old).splitlines(), mask(new).splitlines()
        unchanged = set()
        for block in difflib.SequenceMatcher(None, old_lines, new_lines,
                                             autojunk=False).get_matching_blocks():
            unchanged.update(range(block.b, block.b + block.size))
        for label, source in (("BASELINE", old), ("CURRENT", new)):
            for line, token, context in findings(source):
                counts[label][token] += 1
                print(f"{label} {path}:{line + 1}: {context}")
                if label == "CURRENT" and line not in unchanged:
                    counts["NEW"][token] += 1
                    print(f"NEW {path}:{line + 1}: {context}")
    for label, count in counts.items():
        print(f"{label} totals: {dict(sorted(count.items()))}")
    print("Source check only: inspect transitive Print Assumptions separately.")
    return bool(counts["NEW"])


if __name__ == "__main__":
    raise SystemExit(main())
