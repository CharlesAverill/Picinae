#!/usr/bin/env python3
"""Exercise comment/string masking and the source audit's actual exit codes."""

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("audit-proof-source.py").resolve()
SPEC = importlib.util.spec_from_file_location("audit", SCRIPT)
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class SourceAuditTests(unittest.TestCase):
    def test_comments_and_strings(self):
        source = '''(* outer (* admit *) Axiom x : True. *)
Check "Admitted and ""Parameter""".
(* newline
Admitted. *)
Theorem ok : True. Proof. exact I. Qed.
'''
        self.assertEqual(AUDIT.findings(source), [])
        self.assertEqual(AUDIT.mask(source).count("\n"), source.count("\n"))

    def test_real_tokens(self):
        self.assertEqual([x[1] for x in AUDIT.findings(
            'Axiom x : True.\nParameters y z : Prop.\nadmit.\nAdmitted.')],
            ["Axiom", "Parameters", "admit", "Admitted"])

    def test_malformed_source(self):
        for source in ('(* unfinished', 'Check "unfinished'):
            with self.assertRaises(ValueError):
                AUDIT.mask(source)

    def test_recorder_preserves_failure(self):
        with tempfile.TemporaryDirectory(prefix="picinae-recorder-") as tmp:
            log = Path(tmp) / "failure.log"
            result = subprocess.run([
                "bash", str(SCRIPT.with_name("record-command.sh")), str(log),
                "bash", "-c", "printf 'failure output\\n'; exit 23"],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 23)
            self.assertIn("failure output\n", log.read_text())
            self.assertIn("EXIT_CODE=23", log.read_text())

    def test_baseline_and_new_files(self):
        with tempfile.TemporaryDirectory(prefix="picinae-source-audit-") as tmp:
            root = Path(tmp)

            def git(*args):
                subprocess.run(["git", *args], cwd=root, check=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            def scan(expected):
                result = subprocess.run([sys.executable, str(SCRIPT), "--base", "HEAD"],
                                        cwd=root, capture_output=True, text=True)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                return result.stdout

            git("init", "-q")
            baseline = 'Module Type S. Parameter x : Prop. End S.\n'
            (root / "base.v").write_text(baseline)
            git("add", "base.v")
            git("-c", "user.name=Audit Test", "-c", "user.email=audit@example.invalid",
                "-c", "commit.gpgsign=false", "commit", "-qm", "Add fixture")
            self.assertIn("NEW totals: {}", scan(0))
            (root / "base.v").write_text(baseline + '(* Admitted. *)\n')
            scan(0)
            (root / "new.v").write_text('Theorem bad : False. Admitted.\n')
            self.assertIn("NEW new.v:1:", scan(1))
            (root / "new.v").write_text('Theorem ok : True. Proof. exact I. Qed.\n')
            scan(0)
            (root / "base.v").write_text(baseline + 'Axiom extra : False.\n')
            self.assertIn("NEW base.v:2:", scan(1))


if __name__ == "__main__":
    unittest.main()
