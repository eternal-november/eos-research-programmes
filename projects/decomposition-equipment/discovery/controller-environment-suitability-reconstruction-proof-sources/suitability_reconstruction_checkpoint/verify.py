#!/usr/bin/env python3
"""Verify this research checkpoint using only the Python standard library."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import shutil
import stat
import subprocess
import sys
import tempfile
import zipfile

PACKAGE_ROOT = "suitability_reconstruction_checkpoint"
CHECKERS = [
    ("theory/check_typed_causal_closure.py", "theory/check_typed_causal_closure_results.json", "author"),
    ("scripts/check_typed_causal_presentation.py", "scripts/check_typed_causal_presentation_results.json", "author"),
    ("scripts/check_operational_cut_criterion.py", "review/Operational_Cut_Criterion_Results.json", "author"),
    ("scripts/check_causal_constraint_descent.py", "review/Causal_Constraint_Descent_Results.json", "author"),
    ("scripts/check_parametric_causal_descent.py", "review/Parametric_Causal_Descent_Results.json", "author"),
    ("scripts/check_causal_families.py", "examples/Causal_Family_Checks.json", "author"),
    ("scripts/check_coupled_target_index.py", "review/Coupled_Target_Index_Results.json", "author"),
    ("scripts/check_causal_families_independent.py", "review/Causal_Family_Independent_Results.json", "independent"),
    ("scripts/check_mixed_cut_driver_gap_independent.py", "review/Mixed_Cut_Driver_Gap_Independent_Results.json", "independent"),
    ("scripts/check_block_index_family_independent.py", "review/Block_Index_Independent_Results.json", "independent"),
    ("scripts/check_parametric_descent_independent.py", "review/Parametric_Descent_Independent_Results.json", "independent"),
    ("scripts/check_unbounded_recognition_independent.py", "review/Unbounded_Recognition_Independent_Results.json", "independent"),
]
REQUIRED = {
    "README.txt", "verify.py", "verification/Checkpoint_Verification_Receipt.json",
    "delivery/Controller environment suitability reconstruction results.txt",
    "references/Original_Calculus_Dynamic_Interpretation.md",
    "references/CompletionContract.md",
    "theory/Causal_Constraint_Descent.md", "theory/Causal_Descent.md",
    "theory/Coupled_Target_Index_Capability.md", "theory/Operational_Cut_Capability.md",
    "theory/Operational_Semantic_Profile_Recognition.md", "theory/Parametric_Causal_Descent.md",
    "theory/Typed_Causal_Presentation_Closure.md", "theory/Typed_Persistent_Completion.md",
    "examples/Causal_Interlock_and_Telemetry_Families.md",
} | {script for script, _, _ in CHECKERS}
SOURCE_PREFIXES = ("theory/", "examples/", "scripts/", "references/")

class VerificationError(Exception):
    pass

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")

def safe_relative(name):
    if not isinstance(name, str) or not name or "\\" in name or "\0" in name:
        raise VerificationError("Invalid member path")
    p = PurePosixPath(name)
    if p.is_absolute() or any(c in ("", ".", "..") or ":" in c for c in name.split("/")):
        raise VerificationError("Unsafe member path")
    return p

def source_fingerprint(entries):
    return sha256(canonical({p: e["sha256"] for p, e in entries.items() if p.startswith(SOURCE_PREFIXES)}))

def verify_manifest(root):
    root = Path(root)
    try:
        manifest = json.loads((root / "MANIFEST.json").read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        raise VerificationError("Missing or invalid MANIFEST.json") from e
    if manifest.get("schema") != "suitability-checkpoint-manifest-v1":
        raise VerificationError("Unknown manifest schema")
    entries = manifest.get("files")
    if not isinstance(entries, dict) or set(entries) != REQUIRED:
        raise VerificationError("Required source or package member omitted or unexpected member listed")
    actual = set()
    for p in root.rglob("*"):
        if p.is_symlink():
            raise VerificationError("Symlink in checkpoint")
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
        elif not p.is_dir():
            raise VerificationError("Nonregular checkpoint member")
    if actual != REQUIRED | {"MANIFEST.json"}:
        raise VerificationError("Missing or unexpected checkpoint files")
    for name, info in sorted(entries.items()):
        safe_relative(name)
        data = root.joinpath(*PurePosixPath(name).parts).read_bytes()
        if not isinstance(info, dict) or info.get("size_bytes") != len(data) or info.get("sha256") != sha256(data):
            raise VerificationError("Checksum mismatch: " + name)
    if manifest.get("source_fingerprint_sha256") != source_fingerprint(entries):
        raise VerificationError("Source fingerprint mismatch")
    return manifest

def validate_zip(zf):
    infos = zf.infolist()
    if not infos or len(infos) > 1000:
        raise VerificationError("Invalid archive member count")
    names, folded, total = set(), set(), 0
    for info in infos:
        name = info.filename
        p = safe_relative(name)
        if info.is_dir():
            raise VerificationError("Unexpected explicit archive directory entry")
        if len(p.parts) < 2 or p.parts[0] != PACKAGE_ROOT:
            raise VerificationError("Archive must use the single checkpoint root")
        mode = (info.external_attr >> 16) & 0xFFFF
        kind = stat.S_IFMT(mode)
        if kind not in (0, stat.S_IFREG) or info.flag_bits & 1:
            raise VerificationError("Nonregular, symlink, or encrypted archive member")
        if name in names or name.casefold() in folded:
            raise VerificationError("Duplicate or case-colliding archive member")
        names.add(name); folded.add(name.casefold())
        total += info.file_size
        if total > 64 * 1024 * 1024:
            raise VerificationError("Archive exceeds the source-checkpoint size bound")
    expected = {PACKAGE_ROOT + "/" + p for p in REQUIRED | {"MANIFEST.json"}}
    if names != expected:
        raise VerificationError("Archive member set differs from required checkpoint")
    return infos

def extract_zip(archive, destination):
    with zipfile.ZipFile(archive) as zf:
        infos = validate_zip(zf)  # Validate every path before writing any member.
        for info in infos:
            p = Path(destination).joinpath(*PurePosixPath(info.filename).parts)
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(zf.read(info))
    root = Path(destination) / PACKAGE_ROOT
    verify_manifest(root)
    return root

def expect_rejection(action, label):
    try:
        action()
    except VerificationError:
        return {"control": label, "status": "PASS", "observed": "REJECT"}
    raise VerificationError("Negative control was accepted: " + label)

def packaging_controls(root):
    out = []
    with tempfile.TemporaryDirectory(prefix="suitability-controls-") as temp:
        copy = Path(temp) / "copy"
        shutil.copytree(root, copy)
        target = copy / "theory/Operational_Semantic_Profile_Recognition.md"
        original = target.read_bytes()
        target.write_bytes(original + b"\nAltered-source negative control.\n")
        out.append(expect_rejection(lambda: verify_manifest(copy), "altered required source"))
        target.write_bytes(original)
        target.unlink()
        out.append(expect_rejection(lambda: verify_manifest(copy), "omitted required source"))
        mpath = copy / "MANIFEST.json"
        m = json.loads(mpath.read_text(encoding="utf-8"))
        del m["files"]["theory/Operational_Semantic_Profile_Recognition.md"]
        mpath.write_text(json.dumps(m), encoding="utf-8")
        out.append(expect_rejection(lambda: verify_manifest(copy), "omitted source and manifest entry"))
        # Each malicious archive is rejected before extraction.
        malicious = [
            ("parent traversal archive path", "../escape.txt", None),
            ("absolute archive path", "/escape.txt", None),
            ("Windows drive archive path", "C:/escape.txt", None),
            ("backslash archive path", PACKAGE_ROOT + "\\escape.txt", None),
            ("symlink archive member", PACKAGE_ROOT + "/link", stat.S_IFLNK | 0o777),
        ]
        for label, name, mode in malicious:
            archive = Path(temp) / "malicious.zip"
            with zipfile.ZipFile(archive, "w") as zf:
                info = zipfile.ZipInfo(name)
                if mode is not None:
                    info.create_system = 3; info.external_attr = mode << 16
                zf.writestr(info, "test")
            def validate():
                with zipfile.ZipFile(archive) as zf: validate_zip(zf)
            out.append(expect_rejection(validate, label))
        archive = Path(temp) / "duplicate.zip"
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with zipfile.ZipFile(archive, "w") as zf:
                zf.writestr(PACKAGE_ROOT + "/README.txt", "one")
                zf.writestr(PACKAGE_ROOT + "/README.txt", "two")
        def duplicate():
            with zipfile.ZipFile(archive) as zf: validate_zip(zf)
        out.append(expect_rejection(duplicate, "duplicate archive member"))
    return out

def compact_metrics(value, prefix="", depth=0):
    """Keep finite-check counts and control results, not raw reviewer narratives."""
    out = {}
    if not isinstance(value, dict) or depth > 2:
        return out
    for key, val in sorted(value.items()):
        if "sha256" in key or key in ("status", "scope", "method"):
            continue
        name = prefix + key
        if type(val) in (int, bool):
            out[name] = val
        elif isinstance(val, str) and val in ("PASS", "REJECT"):
            out[name] = val
        elif isinstance(val, dict):
            out.update(compact_metrics(val, name + ".", depth + 1))
        elif isinstance(val, list):
            out[name + ".item_count"] = len(val)
    return out

def run_suite(root, manifest):
    results = []
    with tempfile.TemporaryDirectory(prefix="suitability-replay-") as temp:
        work = Path(temp) / "checkpoint"
        shutil.copytree(root, work)
        (work / "review").mkdir(exist_ok=True)
        for script, result_path, role in CHECKERS:
            output = work / result_path
            if output.exists():
                raise VerificationError("A stale checker result was present")
            # -I ignores Python environment/user-site settings; -S excludes site packages; -B avoids bytecode.
            proc = subprocess.run([sys.executable, "-I", "-S", "-B", str(work / script)],
                                  cwd=work, capture_output=True, text=True)
            if proc.returncode != 0:
                # Avoid leaking local absolute paths from a traceback into receipts.
                raise VerificationError("Checker failed: " + script + " (exit " + str(proc.returncode) + ")")
            try:
                result_bytes = output.read_bytes()
                result = json.loads(result_bytes)
            except (OSError, ValueError) as e:
                raise VerificationError("Missing or invalid checker result: " + script) from e
            if result.get("status") != "PASS":
                raise VerificationError("Checker did not return terminal PASS: " + script)
            entry = {"checker": script, "role": role, "status": "PASS", "exit_code": 0,
                     "checker_sha256": manifest["files"][script]["sha256"],
                     "result_relative_path": result_path, "result_sha256": sha256(result_bytes),
                     "metrics": compact_metrics(result)}
            results.append(entry)
            print("PASS " + script, flush=True)
        # A checker is not permitted to alter any sealed input source.
        for name, info in manifest["files"].items():
            if sha256((work / name).read_bytes()) != info["sha256"]:
                raise VerificationError("Checker altered packaged input: " + name)
    return results

def verify(root, integrity_only=False, receipt_path=None):
    manifest = verify_manifest(root)
    print("PASS manifest integrity and required member set", flush=True)
    if integrity_only:
        return
    controls = packaging_controls(root)
    results = run_suite(root, manifest)
    curated = json.loads((root / "verification/Checkpoint_Verification_Receipt.json").read_text(encoding="utf-8"))
    if curated.get("source_fingerprint_sha256") != manifest["source_fingerprint_sha256"]:
        raise VerificationError("Curated receipt does not match the packaged sources")
    if curated.get("status") != "PASS":
        raise VerificationError("Invalid curated receipt status")
    if curated["status"] == "PASS":
        prior = {(r["checker"], r["checker_sha256"], r["status"]) for r in curated.get("checkers", [])}
        now = {(r["checker"], r["checker_sha256"], r["status"]) for r in results}
        if prior != now:
            raise VerificationError("Curated checker coverage differs from full replay")
    receipt = {
        "schema": "suitability-checkpoint-verification-v1", "status": "PASS",
        "scope": "Fresh-copy execution of the packaged finite checkers; supplements the mathematical proofs, not a proof of all-size theorems or a Lean verification.",
        "python": platform.python_version(), "python_implementation": platform.python_implementation(),
        "dependencies": "Python standard library only; no network or external research tree required",
        "source_fingerprint_sha256": manifest["source_fingerprint_sha256"],
        "mandatory_checker_count": len(CHECKERS), "author_checker_count": 7, "independent_checker_count": 5,
        "input_integrity_after_execution": "PASS", "packaging_controls": controls, "checkers": results,
    }
    if receipt_path:
        Path(receipt_path).write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("PASS " + str(len(controls)) + " adversarial packaging controls", flush=True)
    print("PASS all " + str(len(results)) + " mandatory checkers; packaged sources unchanged", flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="Validate and freshly extract a checkpoint ZIP before replay")
    parser.add_argument("--integrity-only", action="store_true", help="Check hashes and required members without running mathematical checkers")
    parser.add_argument("--receipt", type=Path, help="Write a fresh curated receipt outside the checkpoint directory")
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        parser.error("Python 3.10 or newer is required")
    try:
        if args.archive:
            with tempfile.TemporaryDirectory(prefix="suitability-extract-") as temp:
                root = extract_zip(args.archive, temp)
                print("PASS safe ZIP validation and fresh extraction", flush=True)
                verify(root, args.integrity_only, args.receipt)
        else:
            verify(Path(__file__).resolve().parent, args.integrity_only, args.receipt)
    except (VerificationError, OSError, ValueError, zipfile.BadZipFile) as e:
        print("FAIL " + str(e), file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
