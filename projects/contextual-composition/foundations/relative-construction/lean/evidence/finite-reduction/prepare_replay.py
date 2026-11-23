"""Prepare a clean Lake package for the source-closed finite reduction proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def frozen_input(package, revision, name, digest):
    data = (package / name).read_bytes().replace(b"\r\n", b"\n")
    if hashlib.sha256(data).hexdigest() != digest:
        # A newer package verifier may accompany still-identical mathematical sources.
        prefix = subprocess.check_output(
            ["git", "-C", str(package), "rev-parse", "--show-prefix"], text=True
        ).strip()
        data = subprocess.check_output(
            ["git", "-C", str(package), "show", f"{revision}:{prefix}{name}"]
        )
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f"Cannot reproduce the pinned build input: {name}")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path, help="new directory for the scoped build")
    destination = parser.parse_args().destination.resolve()
    evidence = Path(__file__).resolve().parent
    package = evidence.parent.parent
    receipt = json.loads((evidence / "source.json").read_text(encoding="utf-8"))
    sources = {}
    for name, digest in receipt["sha256"].items():
        path = Path(name)
        if path.parent != Path("ContextualComposition") or path.suffix != ".lean":
            raise ValueError(f"Unexpected module path in receipt: {name}")
        data = (package / path).read_bytes().replace(b"\r\n", b"\n")
        if hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f"Source differs from the audited revision: {name}")
        sources[name] = data

    names = {name[:-5].replace("/", ".") for name in sources}
    for path, data in sources.items():
        for line in data.decode("utf-8").splitlines():
            match = re.fullmatch(r"(?:public )?import (?:all )?(ContextualComposition\.\S+)", line.strip())
            if match and match[1] not in names:
                raise ValueError(f"Missing project dependency for {path}: {match[1]}")

    umbrella = []
    for line in (package / "ContextualComposition.lean").read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"public import (\S+)", line)
        if match and match[1] in names:
            umbrella.append(match[1])
    if len(umbrella) != len(names) or set(umbrella) != names:
        raise ValueError("The umbrella does not import every scoped module exactly once")

    index = json.loads((package / "TheoremIndex.json").read_text(encoding="utf-8"))
    scoped = [row for row in index if row["file"] in sources]
    declarations = [row["declaration"] for row in scoped]
    expected = re.findall(r"^'([^']+)' ", (evidence / "axioms.log").read_text(encoding="utf-8"), re.M)
    if declarations != expected or len(set(expected)) != len(expected):
        raise ValueError("Scoped theorem index disagrees with the recorded audit")
    selected = set(declarations)
    commands = (package / "AxiomAudit.lean").read_text(encoding="utf-8").splitlines()
    prints = [line for line in commands if line.removeprefix("#print axioms ") in selected]
    if prints != ["#print axioms " + name for name in declarations]:
        raise ValueError("The ordered package audit disagrees with the scoped index")

    runner_files = {}
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify.py", "audit.py"):
        runner_files[name] = frozen_input(
            package, receipt["revision"], name, receipt["replay_inputs_sha256"][name]
        )

    destination.mkdir(parents=True, exist_ok=False)
    (destination / "ContextualComposition").mkdir()
    for name, data in sources.items():
        (destination / name).write_bytes(data)
    for name, data in runner_files.items():
        (destination / name).write_bytes(data)
    (destination / "ContextualComposition.lean").write_text(
        "module\n\n" + "".join(f"public import {name}\n" for name in umbrella), encoding="utf-8"
    )
    (destination / "AxiomAudit.lean").write_text(
        "module\n\nimport ContextualComposition\n\n" + "\n".join(prints) + "\n", encoding="utf-8"
    )
    (destination / "TheoremIndex.json").write_text(
        json.dumps(scoped, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Prepared {len(sources)} modules and {len(declarations)} audits in {destination}")


if __name__ == "__main__":
    main()
