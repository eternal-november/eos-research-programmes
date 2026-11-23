"""Regression controls for the source-policy check; uses the package's pinned Lake environment."""
from pathlib import Path
import sys
import tempfile
import unittest

PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE))
from source_audit import check_sources


class SourceAuditTests(unittest.TestCase):
    def check_case(self, source, *, reject_line=None):
        with tempfile.TemporaryDirectory(prefix="SourceCommentTest", dir=PACKAGE) as folder:
            path = Path(folder) / "Fixture.lean"
            path.write_bytes(source.replace("\n", "\r\n").encode("utf-8"))
            if reject_line is None:
                check_sources(PACKAGE, [path])
            else:
                with self.assertRaisesRegex(SystemExit, rf"Forbidden proof/trust token in .*Fixture\.lean:{reject_line}:"):
                    check_sources(PACKAGE, [path])

    def test_comment_forms_and_utf8_positions(self):
        self.check_case(
            "module\npublic import Init\n@[expose] public section\n"
            "/-! Shapes λ admit empty axes. -/\n"
            "-- unsafe in prose\n"
            "/-- Nested /- sorry -/ and axiom in documentation. -/\n"
            "theorem finished : True := True.intro\n"
        )

    def test_code_and_literal_tokens_still_fail(self):
        # The delimiter in the string is not the start of a source comment.
        prefix = 'import Init\ndef delimiter : String := "/-"\n/- λ admit -/ '
        for command in ("axiom missing : True", "theorem unfinished : True := by sorry",
                        "theorem unfinished : True := by admit", "unsafe def value : Nat := 0",
                        'def prose : String := "admit"'):
            with self.subTest(command=command):
                self.check_case(prefix + command + "\n", reject_line=3)


if __name__ == "__main__":
    unittest.main()
