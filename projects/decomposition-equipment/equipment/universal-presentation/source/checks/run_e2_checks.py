#!/usr/bin/env python3
"""Source-bound, optimization-invariant E2 finite regression runner (stdlib)."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def checked_sources(root, manifest):
    recorded = json.loads(manifest.read_text(encoding="utf-8"))
    require(recorded.get("schema") == "E2 finite source scope v1", "unrecognized source manifest")
    files = recorded["files"]
    required = {"universal_theorem.md", "reconstruction_theorem.md", "checks/e2_finite_cells.py",
                "checks/run_e2_checks.py", "checks/README.md"}
    require(required <= files.keys(), "source manifest omits mandatory substantive input")
    actual = {}
    for relative, digest in sorted(files.items()):
        path = Path(relative)
        require(not path.is_absolute() and ".." not in path.parts, "nonportable source manifest path")
        data = (root / path).read_bytes()
        actual[relative] = sha(data)
        require(actual[relative] == digest, "source drift: " + relative)
    return actual


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True,
                        help="External receipt JSON FILE; source tree is not modified")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    # Validate before the try/final receipt write: a REJECT receipt must not itself
    # overwrite a protected source. resolve handles existing or parent symlinks.
    output = args.output.expanduser().resolve()
    protected = output == root or root in output.parents
    if not protected and output.exists():
        # An external hard link is another name for source bytes, not a safe log.
        protected = any(p.is_file() and p.samefile(output) for p in root.rglob("*"))
    if protected:
        sys.stdout.write(json.dumps({"status": "REJECT", "reason": "output must be outside source tree and not alias a source file"}, sort_keys=True) + "\n")
        return 2
    manifest = root / "checks/source_scope_manifest.json"
    try:
        before = checked_sources(root, manifest)
        manifest_hash = sha(manifest.read_bytes())
        environment = os.environ.copy()
        # The labels below denote genuine subprocess modes, not an inherited
        # caller's PYTHONOPTIMIZE setting (including when this runner uses -OO).
        environment.pop("PYTHONOPTIMIZE", None)
        environment["PYTHONHASHSEED"] = "0"
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
        script = root / "checks/e2_finite_cells.py"
        baselines = {}
        raw_baseline = None
        baseline_data = None
        modes = {"normal": [], "-O": ["-O"], "-OO": ["-OO"]}
        for mode, flags in modes.items():
            process = subprocess.run([sys.executable, "-B", *flags, str(script)],
                                     cwd=root, env=environment, capture_output=True, timeout=600)
            require(process.returncode == 0, "baseline rejected in " + mode + ": " +
                    process.stdout.decode("utf-8", errors="replace") +
                    process.stderr.decode("utf-8", errors="replace"))
            require(not process.stderr, "unexpected baseline stderr in " + mode)
            data = json.loads(process.stdout)
            require(data.get("status") == "PASS", "baseline status not PASS in " + mode)
            if raw_baseline is None:
                raw_baseline = process.stdout
                baseline_data = data
            require(process.stdout == raw_baseline, "optimization changed exact baseline output in " + mode)
            baselines[mode] = {"status": "PASS", "stdout_sha256": sha(process.stdout)}
        mutations = {}
        for mutation in ("drop_nullary_scalar", "drop_choice_scalar", "forget_refinement_slots", "forget_partition_order"):
            observed = None
            for mode, flags in modes.items():
                process = subprocess.run([sys.executable, "-B", *flags, str(script), "--mutate", mutation],
                                         cwd=root, env=environment, capture_output=True, timeout=60)
                require(process.returncode == 1, "semantic mutation was not rejected: " + mutation + " / " + mode)
                require(not process.stderr, "mutation crashed rather than explicit semantic reject: " + mutation)
                data = json.loads(process.stdout)
                require(data.get("status") == "REJECT" and data.get("mutation") == mutation,
                        "mutation rejection metadata mismatch: " + mutation)
                if observed is None:
                    observed = process.stdout
                require(process.stdout == observed, "optimization changed mutation rejection: " + mutation)
                mutations[mutation + "/" + mode] = data
        after = checked_sources(root, manifest)
        require(before == after and manifest_hash == sha(manifest.read_bytes()),
                "source changed during verification; no final receipt is valid")
        receipt = {"status": "PASS", "schema": "E2 finite verification receipt v1",
                   "source_sha256": before, "source_manifest_sha256": manifest_hash,
                   "optimization_modes": baselines, "semantic_mutation_controls": mutations,
                   "finite_evidence": baseline_data,
                   "limits": ["The parameterized mathematical proofs are in the named source files; no new Lean/L claim.",
                              "Finite evaluation does not prove arbitrary-target interpretation, transformation extension, or all-cell generation.",
                              "The negative quotient tests are preequipment/relative-marking tests, never full-equipment congruence countermodels."]}
        exit_code = 0
    except (RuntimeError, OSError, ValueError, subprocess.TimeoutExpired) as error:
        receipt = {"status": "REJECT", "reason": str(error)}
        exit_code = 1
    rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    sys.stdout.write(rendered)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
