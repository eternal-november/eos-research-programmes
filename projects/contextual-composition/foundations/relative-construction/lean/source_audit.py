"""Check proof-policy tokens, using Lean to identify comments in ambiguous files."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


TOKEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe)\b")


def check_sources(package, paths):
    parser = Path(__file__).parent / "checks" / "SourceComments.lean"
    for path in paths:
        # Match Lean's Parser.mkInputContext normalization and UTF-8 byte positions.
        source = path.read_bytes().decode("utf-8").replace("\r\n", "\n")
        offsets = []
        previous = byte_position = 0
        for match in TOKEN.finditer(source):
            byte_position += len(source[previous:match.start()].encode("utf-8"))
            offsets.append(byte_position)
            previous = match.start()
        if not offsets:
            continue
        module = ".".join(path.relative_to(package).with_suffix("").parts)
        stop = int(subprocess.check_output(
            ["lake", "env", "lean", "--run", str(parser.with_name("SourceHeader.lean")), str(path)],
            cwd=package, text=True, encoding="utf-8",
        ))
        header = source.encode("utf-8")[:stop].decode("utf-8")
        program = header + "\n" + parser.read_text(encoding="utf-8") + "\nrun_cmd SourceCommentCheck.checkRequest\n"
        with tempfile.TemporaryDirectory() as work:
            request = Path(work) / "request.json"
            request.write_text(json.dumps({
                "fileName": str(path), "moduleName": module, "positions": offsets,
            }), encoding="utf-8")
            checked = subprocess.run(
                ["lake", "env", "lean", "--stdin"], cwd=package, input=program,
                env={**os.environ, "CONTEXTUAL_SOURCE_COMMENT_REQUEST": str(request)},
                text=True, encoding="utf-8", stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
        if checked.returncode:
            raise SystemExit(checked.stdout or f"Source-policy check failed for {path}")
