#!/usr/bin/env python3
"""Static TeX integrity checks only; deliberately does not compile TeX.

This checker does not establish mathematical correctness or visual layout.
It checks balanced grouping/environments, labels, references, citations,
document boundaries, and explicit assembly markers.
"""
from __future__ import annotations
import argparse
import collections
import hashlib
import json
import re
from pathlib import Path


def strip_comments(text: str) -> str:
    lines = []
    for line in text.splitlines():
        for i, ch in enumerate(line):
            if ch == "%":
                slashes = 0
                j = i - 1
                while j >= 0 and line[j] == "\\":
                    slashes += 1
                    j -= 1
                if slashes % 2 == 0:
                    line = line[:i]
                    break
        lines.append(line)
    return "\n".join(lines)


def check(path: Path) -> dict:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    clean = strip_comments(text)
    errors = []
    stack = []
    for m in re.finditer(r"\\(?:begin|end)\{([^}]+)\}", clean):
        op = "begin" if m.group().startswith("\\begin") else "end"
        env = m.group(1)
        line = clean[:m.start()].count("\n") + 1
        if op == "begin":
            stack.append((env, line))
        elif not stack:
            errors.append(f"Unmatched end {env} at line {line}")
        elif stack[-1][0] != env:
            errors.append(f"End {env} at line {line} closes {stack[-1]}")
        else:
            stack.pop()
    errors.extend(f"Unclosed environment {env} from line {line}" for env, line in stack)
    braces = []
    for i, ch in enumerate(clean):
        if ch not in "{}":
            continue
        j = i - 1
        slashes = 0
        while j >= 0 and clean[j] == "\\":
            slashes += 1
            j -= 1
        if slashes % 2:
            continue
        line = clean[:i].count("\n") + 1
        if ch == "{":
            braces.append(line)
        elif not braces:
            errors.append(f"Unmatched closing brace at line {line}")
        else:
            braces.pop()
    errors.extend(f"Unclosed brace from line {line}" for line in braces)
    labels = re.findall(r"\\label\{([^}]+)\}", clean)
    label_counts = collections.Counter(labels)
    errors.extend(f"Duplicate label: {label}" for label, n in label_counts.items() if n > 1)
    refs = re.findall(r"\\(?:ref|eqref|pageref|autoref)\{([^}]+)\}", clean)
    errors.extend(f"Unresolved reference: {ref}" for ref in sorted(set(refs) - set(labels)))
    bibs = re.findall(r"\\bibitem(?:\[[^]]*\])?\{([^}]+)\}", clean)
    citations = []
    for keys in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", clean):
        citations.extend(key.strip() for key in keys.split(","))
    errors.extend(f"Unresolved citation: {key}" for key in sorted(set(citations) - set(bibs)))
    for token in ("\\documentclass", "\\begin{document}", "\\end{document}"):
        n = clean.count(token)
        if n != 1:
            errors.append(f"Expected one {token}, found {n}")
    assembly_markers = [token for token in ("ASSEMBLY POINT", "awaiting the full crossing proof", "TODO", "TBD", "PLACEHOLDER") if token in text]
    errors.extend(f"Unresolved assembly marker: {token}" for token in assembly_markers)
    safeguards = {
        "all_ten_coherence_items": all(f"\\item[C{i} " in clean for i in range(1, 11)),
        "relative_genuine_lifts": "genuine" in clean and "No cartesian lift outside" in clean,
        "finite_support_global_lift_assumption": "is a global fibration" in clean,
        "noninvertible_content_bodies": "Neither displayed body is assumed" in clean,
        "unit_rigidity_iff": "if and only if" in clean and "End_{" in clean,
        "explicit_necessary_sufficient_gap": "realizable" in clean and "\\D=\\J" in clean,
        "no_compilation_claim": "No TeX engine was run" in clean,
        "whole_contract_remains_open": "whole expanded contract remains open" in clean,
    }
    errors.extend(f"Missing scope safeguard: {key}" for key, good in safeguards.items() if not good)
    for start, end in ((r"\[", r"\]"), (r"\(", r"\)")):
        if len(re.findall(r"(?<!\\)" + re.escape(start), clean)) != len(re.findall(r"(?<!\\)" + re.escape(end), clean)):
            errors.append(f"Unbalanced math delimiters {start} and {end}")
    unescaped_dollars = re.findall(r"(?<!\\)\$", clean)
    if len(unescaped_dollars) % 2:
        errors.append("Odd number of unescaped dollar delimiters")
    return {
        "file": path.name,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "bytes": len(raw),
        "lines": len(text.splitlines()),
        "labels": len(labels),
        "references": len(refs),
        "bibliography_entries": len(bibs),
        "citations": len(citations),
        "scope_safeguards": safeguards,
        "errors": errors,
        "static_check_passed": not errors,
        "compiled": False,
        "mathematical_proof_check": False,
        "visual_layout_check": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.source)
    output = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")
    raise SystemExit(0 if result["static_check_passed"] else 1)
