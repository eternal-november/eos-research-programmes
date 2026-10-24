"""Reproduce the joint-control package and bind its checked source snapshot.

Proof elaboration, executable evidence, analytic/source review and completion
are distinct. A passing record alone is not a full-contract completion verdict.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
DEFAULT_LEAN = Path(os.environ["USERPROFILE"])/".elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def inputs():
    paths = [p for p in HERE.iterdir() if p.is_file()
             and p.suffix in (".md", ".py", ".lean", ".json")
             and p.name != "verification.json"]
    for name in ("DOWNSTREAM-CONTRACT.md", "FAULT-COVERAGE.md", "ASSUMPTION-REVIEW.md",
                 "REMAINING-PROGRAM.md", "REVISED-AUDIT.md", "MOTIVATING-PROBLEM.md"):
        paths.append(PROJECT/name)
    # These are actual transitive proof/checking sources and reuse evidence.
    for folder in ("handoff", "research", "enforcement", "integration"):
        paths += [p for p in (PROJECT/folder).iterdir() if p.is_file()
                  and p.suffix in (".md", ".py", ".lean", ".json", ".ps1")]
    paths.append(PROJECT/"handoff/lean-toolchain")
    # Freeze every retained dependency that retained_binding() checks, including
    # parent-level contracts outside the four historical artifact directories.
    retained = json.loads((PROJECT/"integration/verification.json").read_text(encoding="utf-8"))
    paths += [PROJECT/name for name in retained["sources_sha256_lf"]
              if name != "TODO.md"]
    return {p.relative_to(PROJECT).as_posix(): digest(p) for p in sorted(set(paths))}


def run(command):
    environment = dict(os.environ)
    environment.pop("PYTHONOPTIMIZE", None)
    process = subprocess.run(command, cwd=HERE, text=True, encoding="utf-8",
                             capture_output=True, env=environment)
    require(process.returncode == 0, repr(command)+"\n"+process.stdout+"\n"+process.stderr)
    require(not process.stderr.strip(), "Unexpected diagnostic: "+process.stderr)
    return process.stdout.replace("\r\n", "\n").strip()


def strict_checker():
    path = PROJECT/"integration/verify.py"
    spec = importlib.util.spec_from_file_location("retained_strict_checker", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def retained_binding():
    old = PROJECT/"integration/verification.json"
    record = json.loads(old.read_text(encoding="utf-8"))
    require(record["verification_passed"], "Retained source-bound record did not pass")
    checked = {}
    excluded = {}
    for name, expected in record["sources_sha256_lf"].items():
        if name == "TODO.md":
            # The old workflow/completion status was replaced deliberately. No
            # proof or executable reads it; its old completion verdict is unused.
            excluded[name] = "Historical workflow status; not a mathematical input or current completion verdict"
            continue
        actual = digest(PROJECT/name)
        require(actual == expected, "Retained mathematical/check input changed: "+name)
        checked[name] = actual
    return {
        "record_sha256_lf": digest(old),
        "matched_sources": checked,
        "excluded_workflow": excluded,
        "scope": "Retained encoded results at their original hypotheses, not the revised program verdict",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--lean", type=Path, default=DEFAULT_LEAN)
    args = parser.parse_args()
    require(not sys.flags.optimize and sys.version_info[:2] == (3, 12),
            "Unoptimized Python3.12 is required")
    required = ("PROGRAM.md", "SOURCE.md", "SOURCES.md", "ASSUMPTIONS.md", "LEDGER.md", "ADMISSION.md",
                "INFORMATION.md", "EVOLUTION.md", "RESTORATION.md", "CONTROL.md",
                "BOUNDARIES.md", "COMPOSITION.md", "REALIZATION.md", "COVERAGE.md", "AUDIT.md")
    for name in required:
        require((HERE/name).is_file(), "Missing required artifact: "+name)
    before = inputs()
    output_path = HERE/"verification.json"
    expected = json.loads(output_path.read_text(encoding="utf-8")) if args.check else None
    if expected:
        require(expected["sources_sha256_lf"] == before, "Inputs changed; inspect before deliberate refresh")

    version = run([str(args.lean), "--version"])
    require("version 4.33.0," in version, "Pinned Lean4.33.0 required")
    old = strict_checker()
    guards = old.verifier_regressions(str(args.lean))
    proofs = {}
    for name in ("Information.lean", "Evolution.lean", "Restoration.lean", "Control.lean"):
        print("Strict proof and dependency check: "+name, flush=True)
        proofs[name] = old.proof_check(HERE/name, str(args.lean))
    declared = {p.name for p in HERE.glob("*.lean")}
    require(declared == set(proofs), "Uninventoried proof module: "+repr(declared-set(proofs)))

    checks = {}
    commands = {
        "information_model.py": [sys.executable, "-B", str(HERE/"information_model.py"), "--check"],
        "evolution_model.py": [sys.executable, "-B", str(HERE/"evolution_model.py"), "--check", "--lean", str(args.lean)],
        "control_model.py": [sys.executable, "-B", str(HERE/"control_model.py"), "--check"],
        "boundary_model.py": [sys.executable, "-B", str(HERE/"boundary_model.py"), "--check"],
        "joint_model.py": [sys.executable, "-B", str(HERE/"joint_model.py"), "--check"],
    }
    optimization_guards = {}
    for name in commands:
        probe = subprocess.run([sys.executable, "-O", "-B", str(HERE/name), "--check"],
                               cwd=HERE, text=True, encoding="utf-8", capture_output=True)
        require(probe.returncode != 0 and "Unoptimized Python is required" in probe.stderr,
                "Component can run with assertions disabled: "+name)
        optimization_guards[name] = True
    for name, command in commands.items():
        print("Reproducing "+name, flush=True)
        text = run(command)
        checks[name] = {"passed": True, "stdout_sha256": hashlib.sha256(text.encode()).hexdigest()}
    retained = retained_binding()
    require(before == inputs(), "Inputs changed during verification")
    actual = {
        "schema": "byzantine-joint-verification-v1",
        "verification_passed": True,
        "scope": "Strict encoded proof dependencies and reproduced executable records; analytic/source and full-contract judgments are in AUDIT.md",
        "lean_version": version,
        "python_major_minor": list(sys.version_info[:2]),
        "sources_sha256_lf": before,
        "joint_axiom_dependencies": proofs,
        "joint_declaration_count": sum(len(v) for v in proofs.values()),
        "verifier_guard_checks": guards,
        "executable_checks": checks,
        "component_optimization_guards": optimization_guards,
        "retained_evidence_binding": retained,
    }
    if args.write:
        output_path.write_text(json.dumps(actual, indent=2, sort_keys=True)+"\n",
                               encoding="utf-8", newline="\n")
    else:
        require(actual == expected, "Reproduced verification differs")
    print("PASS: joint proof/check records and source binding; consult independent completion audit", flush=True)


if __name__ == "__main__":
    main()
