"""Reproduce the full research package; standard library only.
--output writes an explicit manifest. --fingerprints-only runs no research checks.
"""
from pathlib import Path
import argparse
import hashlib
import importlib
import json
import sys

if not __debug__:
    raise RuntimeError("Verification requires assertions: disable -O and PYTHONOPTIMIZE")

MODULES = ("core_model", "evidence_model", "institution_model", "digital_model",
           "timed_recovery_model", "quorum_alignment", "assembly_model",
           "physical_adapter", "institution_adapter")
PROOFS = ("Control", "Execution", "Evidence", "Institution", "Digital",
          "TimedRecovery", "QuorumAlignment")
ROOT = Path(__file__).resolve().parent


def source_hashes():
    paths = ["program_check.py", "verify_program.ps1", "check_models.py", "results.json"]
    paths += [name + ".py" for name in MODULES]
    paths += [name + ".lean" for name in PROOFS]
    paths += ["../handoff/" + name for name in
              ("Foundations.lean", "lean-toolchain", "verify.ps1",
               "HANDOFF.md", "EXECUTION.md", "VERIFICATION.md")]
    return {
        name: hashlib.sha256((ROOT / name).read_text(encoding="utf-8").replace("\r\n", "\n").encode("utf-8")).hexdigest()
        for name in sorted(paths)
    }


def current_module(name):
    # Repeated use in one interpreter must not silently reuse a previously loaded version.
    return importlib.reload(sys.modules[name]) if name in sys.modules else importlib.import_module(name)


def run_checks():
    before = source_hashes()
    increment = current_module("check_models")
    result = {
        "prior_increment": {
            "physical": increment.physical(), "digital": increment.broadcast(),
            "structural": increment.structural(), "epistemic": increment.epistemic(),
            "certificate_epistemic": increment.certificate_epistemic(),
            "counterexamples": increment.failures(),
        }
    }
    prior_expected = json.loads((ROOT / "results.json").read_text(encoding="utf-8"))
    assert json.loads(json.dumps(result["prior_increment"])) == prior_expected, "Prior increment changed"
    for name in MODULES:
        result[name] = current_module(name).run_checks()
    after = source_hashes()
    if before != after:
        raise RuntimeError("Research sources changed during verification; discard this run")
    result["normalized_source_sha256"] = before
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--fingerprints-only", action="store_true")
    args = parser.parse_args()
    result = {"normalized_source_sha256": source_hashes()} if args.fingerprints_only else run_checks()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
