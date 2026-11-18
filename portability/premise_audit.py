"""Check the pinned RP0 register's finite dependencies and research references."""

import posixpath
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
PREVIOUS = "169be129b9aa090acf8175e79d5114aa84f1cda9"
BASE = "56c4cff67e8d36c88f6b7a51c68d0f4af861cf03"
KINDS = {"primitive", "import", "local", "finite", "comparison", "assembly", "open"}
PRIMITIVES = {"design", "mission", "material", "history", "initial"}
IMPORTS = {"legacy", "flow-existence", "composition", "retained-history", "paced-rules",
           "all-raw", "safe-fibre", "menu-descent", "finite-health"}
# None of the scoped development results consumes either RP6 open leaf.
WITNESSES = {key: set() for key in (
    "a-universal", "b-universal", "positive-a", "positive-b", "b-g2", "b-g3",
    "a-window-applied", "b-window-applied", "later-factual", "information", "structural",
    "matched-coupled", "burden", "reuse",
)}
WITNESSES["completion"] = {"transfer", "aggregate"}
REQUIRED_INPUTS = {
    "flows": {"flow-existence"}, "chronology": {"retained-history", "paced-rules"},
    "query": {"all-raw"}, "remote-debit": {"all-raw"},
    "tracker": {"safe-fibre"}, "factual-menu": {"menu-descent", "intervention"},
    "b-region": {"coupler-law", "b-field"},
    "coupler-material": {"coupler-law", "topology", "flows"},
    "coupler-ingress": {"coupler-material", "topology"},
    "regional-world": {"b-world", "coupler-material", "coupler-ingress"},
    "b-g2": {"prefix-mission", "prefix-guard", "b-region", "b-compare", "b-world",
             "b-cover", "b-use", "b-physical", "b-cut-handoff", "b-lease"},
    "b-g3": {"coupler-law", "b-host-roster", "flows", "b-host-flow", "b-physical"},
    "matched-coupled": {"matched", "b-universal", "b-world", "regional-world", "b-physical", "b-cover"},
    "a-universal": {"prefix-mission", "prefix-use", "a-physical", "a-use", "a-cover", "a-region"},
    "b-universal": {"prefix-mission", "prefix-use", "b-g2", "b-g3", "b-use", "b-cover"},
    "a-witness": {"a-universal", "a-custody", "a-trip"},
    "b-witness": {"b-universal", "b-cut-handoff", "spatial-world", "b-use"},
    "positive-a": {"a-universal", "a-witness"}, "positive-b": {"b-universal", "b-witness"},
    "b-reference": {"b-host-roster", "b-host-flow", "b-sender-port", "b-trip-install", "coupler-material"},
    "b-sender-join": {"b-reference", "b-sender-port", "b-trip-install", "coupler-ingress"},
    "b-trip-install": {"b-host-roster", "b-sender-port"},
    "a-window-applied": {"a-window", "a-window-cover"},
    "b-window-applied": {"b-sender-window", "b-window-cover", "quiet-window"},
    "a-use": {"a-custody", "a-trip", "a-cover", "a-window-applied", "prefix-rules"},
    "b-use": {"b-physical", "b-cover", "b-lease", "b-cut-handoff", "b-window-applied", "prefix-rules"},
    "later-factual": {"b-universal", "factual-menu", "b-normal-action", "b-cut-handoff", "b-sender-join"},
    "information": {"positive-b", "later-factual", "topology", "query", "framing"},
    "structural": {"positive-a", "positive-b", "a-custody", "b-field", "b-cover"},
    "burden": {"structural", "matched-coupled", "a-trip", "b-cut-handoff", "framing", "flows"},
    "reuse": {"structural", "positive-a", "positive-b", "matched-coupled", "burden"},
    "completion": {"reuse", "information", "replay-method", "transfer", "aggregate"},
    "a-window": {"quiet-window", "a-seat"}, "b-window": {"quiet-window", "b-seat"},
    "wear-boundary": {"finite-health"},
    "b-world": {"b-image", "b-native", "flows", "tracker", "b-region"},
    "spatial-world": {"b-world", "spatial"},
    "b-sender": {"b-sender-port", "b-frame", "b-lease"},
    "a-physical": {"a-g3-seat", "a-tap-install", "a-trip-install"},
    "a-trip": {"a-custody", "a-trip-install"}, "a-custody": {"a-seat", "a-tap-install"},
    "a-g3-seat": {"a-flow", "a-seat-source"},
    "b-physical": {"b-host-flow", "b-reference", "b-sender-port", "b-sender-join"},
    "b-host-flow": {"b-host-roster", "coupler-material", "coupler-ingress", "flows"},
    "b-frame": {"b-image", "b-compare", "b-native", "b-world", "b-field"},
    "b-lease": {"b-rx", "b-data", "b-seat"},
    "b-normal-action": {"intervention", "b-image", "b-compare", "b-lease"},
    "b-sender-window": {"b-sender", "quiet-window", "b-seat"},
    "prefix-rules": {"ancestry", "temporal"}, "prefix-use": {"prefix-rules", "temporal"},
    "prefix-guard": {"prefix-rules", "projection"},
    "prefix-mission": {"prefix-use", "prefix-guard", "flows", "initial", "mission"},
}
LINK = re.compile(r"\[[^\]]+\]\(([^)]+)\)")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def register(path, has_reference):
    nodes = {}
    references = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| ") or line.startswith(("| ---", "| ID |")):
            continue
        fields = [field.strip() for field in line.strip("|").split("|")]
        require(len(fields) == 5, f"Expected five cells: {line}")
        name, kind, inputs, judgment, evidence = fields
        require(re.fullmatch(r"[a-z]+(?:-[a-z][a-z0-9]*)*", name), f"Bad ID {name}")
        require(name not in nodes and kind in KINDS, f"Duplicate ID or unknown kind: {name}")
        deps = [] if inputs == "—" else inputs.split(", ")
        require(len(deps) == len(set(deps)), f"Repeated dependency at {name}")
        terminal = kind in {"primitive", "import", "open"}
        require(terminal == (not deps), f"Unexpected terminal or unexplained result: {name}")
        filenames = LINK.findall(evidence)
        require(judgment and filenames, f"Missing judgment or evidence owner: {name}")
        for filename in filenames:
            require(has_reference(filename), f"Missing source at the audited revision at {name}: {filename}")
        references.update(filenames)
        nodes[name] = (kind, deps)
    require({key for key, (kind, _) in nodes.items() if kind == "primitive"} == PRIMITIVES,
            "Affirmative primitive set differs from the reviewed source assumptions")
    require({key for key, (kind, _) in nodes.items() if kind == "import"} == IMPORTS,
            "Unreviewed or missing imported theorem package")
    return nodes, references


def leaves_by_export(nodes):
    result = {}
    path = []

    def visit(name):
        if name in result:
            return result[name]
        require(name in nodes, f"Unknown dependency at {' -> '.join(path + [name])}")
        require(name not in path, f"Cycle at {' -> '.join(path + [name])}")
        path.append(name)
        kind, deps = nodes[name]
        leaves = {name} if not deps else set().union(*(visit(dep) for dep in deps))
        path.pop()
        result[name] = leaves
        return leaves

    for name in nodes:
        visit(name)
    return result


def validate(nodes):
    leaves = leaves_by_export(nodes)
    for owner, required in WITNESSES.items():
        actual = {name for name in leaves[owner] if nodes[name][0] == "open"}
        require(actual == required, f"Changed open-leaf cut for {owner}: {sorted(actual)}")
    for owner, required in REQUIRED_INPUTS.items():
        missing = required - set(nodes[owner][1])
        require(not missing, f"Missing inputs at {owner}: {sorted(missing)}")
    for owner in ("ancestry", "a-flow", "a-seat", "b-image", "b-compare", "query", "intervention",
                  "factual-menu", "wear-boundary", "a-window", "b-window", "prefix-mission",
                  "a-physical", "coupler-material", "coupler-ingress", "b-host-flow", "b-frame",
                  "b-lease", "b-normal-action", "b-sender", "b-sender-window"):
        require(all(nodes[name][0] != "open" for name in leaves[owner]),
                f"Open application relabelled as a conditional result: {owner}")
    # Successful nominal jobs cannot establish all-mode continuation. The
    # generic mission theorem also precedes both positive source applications.
    forbidden = {
        "a-seat": {"quiet-window"}, "b-seat": {"quiet-window"},
        "a-physical": {"a-use", "a-custody", "a-trip", "orbit", "prefix-mission"},
        "b-host-flow": {"b-frame", "b-normal-action", "b-lease", "orbit", "prefix-mission"},
        "prefix-mission": {"positive-a", "positive-b", "a-universal", "b-universal", "a-witness", "b-witness", "later-factual", "a-physical", "b-host-flow",
                           "a-seat", "b-seat", "a-use", "b-use"},
    }
    # The later existential fork and scaling witnesses consume the universal
    # source results. They cannot establish the causal premises for those results.
    for owner in ("a-universal", "b-universal", "b-g2", "b-g3"):
        forbidden[owner] = {"a-witness", "b-witness", "later-factual", "structural", "burden", "reuse"}
    forbidden["b-g3"].update({"orbit", "b-frame", "b-use", "b-lease", "prefix-mission"})
    for owner, barred in forbidden.items():
        pending = list(nodes[owner][1])
        seen = set()
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            require(current not in barred, f"Out-of-scope premise for {owner}: {current}")
            seen.add(current)
            pending.extend(nodes[current][1])
    return leaves


def main():
    # Resolve every source reference in the same immutable Git tree. In the
    # independent audit worktree the later quiet-window files need not exist on disk.
    def git(*args):
        return subprocess.check_output(["git", "-C", str(HERE), *args], text=True)
    prefix = git("rev-parse", "--show-prefix").strip()
    snapshot = set(git("ls-tree", "-r", "--full-tree", "--name-only", BASE).splitlines())

    def has_reference(filename):
        return posixpath.normpath(prefix + filename) in snapshot

    nodes, references = register(HERE / "EXPORT-DEPENDENCIES.md", has_reference)
    leaves = validate(nodes)
    papers = {filename[len(prefix):] for filename in snapshot
              if filename.startswith(prefix) and "/" not in filename[len(prefix):]
              and filename.endswith((".md", ".lean"))}
    require(bool(papers), "Could not enumerate the base's source documents")
    # These two documents are the previous audit itself. Its appearance in the
    # pinned tree supplies provenance, never a premise for its own conclusions.
    audit_documents = {"CLASS-ADMISSION.md", "EXPORT-DEPENDENCIES.md"}
    require(audit_documents <= papers, "Pinned historical audit documents are missing")
    proof_sources = papers - audit_documents
    require(proof_sources <= references,
            f"Pinned source files without an entry: {sorted(proof_sources - references)}")

    added_paths = git("diff", "--diff-filter=A", "--name-only", PREVIOUS, BASE, "--", ".").splitlines()
    added_evidence = {p[len(prefix):] for p in added_paths if p.startswith(prefix) and "/" not in p[len(prefix):]}
    require(added_evidence <= references,
            f"New local artifacts without an evidence owner: {sorted(added_evidence - references)}")
    require({name for name, (kind, _) in nodes.items() if kind == "open"} == {"transfer", "aggregate"},
            "New or missing open obligation at the final scientific pin")

    admission = (HERE / "CLASS-ADMISSION.md").read_text(encoding="utf-8")
    expected = [f"A{i:02}" for i in range(1, 19)]
    require(re.findall(r"^\| (A\d\d) \|", admission, re.MULTILINE) == expected,
            "Missing, repeated or reordered assumption judgment")
    require(set(re.findall(r"\bC(?:0[1-9]|10)\b", admission)) == {f"C{i:02}" for i in range(1, 11)},
            "Missing conditional-branch judgment")
    for filename in LINK.findall(admission):
        local_register = filename == "EXPORT-DEPENDENCIES.md" and (HERE / filename).is_file()
        require(local_register or has_reference(filename), f"Missing admission reference: {filename}")
    print(f"{len(nodes)} typed nodes; {len(proof_sources)} pinned local source and proof files "
          f"referenced; {len(audit_documents)} earlier audit documents classified separately.")
    for owner in WITNESSES:
        open_leaves = sorted(name for name in leaves[owner] if nodes[name][0] == "open")
        display = ", ".join(open_leaves) if open_leaves else "none"
        print(f"{owner}: {display}")
    print(f"{len(added_evidence)} added local artifacts assigned evidence owners since the previous pin.")
    print("18 assumption families; 10 conditional branches. Structural checks passed.")


if __name__ == "__main__":
    main()
