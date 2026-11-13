# Dynamic calculus — Lean source checkpoint

**27 October 2026 · Focused, kernel-checked formalization**

This checkpoint adds a dynamic target calculus to the original witnessed-decompositions project without changing any original source, configuration, contract, acceptance record, or historical evidence. The new target uses actual graph maps and boundary-compatible tuples, including empty profiles and repeated colours. It connects to the original free and presented extension APIs and semantic-refinement functors. It is an executable Lean proof checkpoint, not merely a Python model or a prose claim.

## What is included

- `baseline/original.zip`: the exact, unchanged original source-and-contract archive (1,681 members; 1,679 payload entries in its integration manifest).
- `overlay/`: 20 new files at their original project-relative paths: seven Lean modules and their README, the author axiom audit and verification wrapper, and the independent regression/audit suite with its unchanged source freeze.
- `assemble_project.py`: an offline assembler that checks the package, extracts the original archive into a **new** directory, adds only nonconflicting new files, and checks the original and frozen source hashes again. It never overwrites an existing project.
- `PAYLOAD_SHA256.json`: SHA-256 and byte length for all other 24 package files; the manifest excludes itself to avoid a circular hash. The final ZIP's hash should be retained separately. Checksums establish byte identity, not publisher authentication.
- `verification/RECEIPT.json`: curated results of fresh extraction, assembly, proof replay, axiom checks, and rejection tests; no raw internal review notes.

This is self-contained **source**, including the original baseline. Lean, Git dependencies and compiled dependency caches are deliberately not bundled. No project `.olean` files or `.lake`/`.git` caches are included. Historical material inside the byte-identical original archive remains historical; it is not a new acceptance decision.

## Assemble offline

Requires Python **3.9 or newer**. Unzip this checkpoint and, from its top-level directory, run:

```sh
python3 assemble_project.py ../dynamic-calculus-project
```

The destination must not exist and must be outside the extracted checkpoint directory. Assembly checks:

1. All package payload hashes and the pinned canonical baseline archive hash.
2. Safe, unique, regular archive members and no overlay/original filename collisions.
3. All 1,679 original integration payload hashes and sizes, before and after adding the overlay.
4. The independent baseline checks and the exact 45-entry source/configuration freeze.

Baseline archive SHA-256:

```text
90f506963b83e6b918fd7fb7d108717b932627f3ea62d2bc9aec5b186ec63060
```

Independent `SOURCE_FREEZE.json` SHA-256:

```text
3a8623e9e3e66f9ebdcd505a0e634355476861f2fabcdf23e6dc808bec460fae
```

The included proof/audit sources are copied byte-for-byte. In particular, do not regenerate `SOURCE_FREEZE.json` or run `--record-freeze` to conceal a mismatch.

## Restore the pinned environment — x86-64 Linux / WSL2

The replay was tested on x86-64 Linux. These instructions target Linux or an x86-64 Linux distribution in WSL2; native Windows and macOS replay are **not** claimed tested. Install the distribution's normal prerequisites: Python 3.9+, Git, curl, GNU tar, zstd, bash and GNU coreutils. Internet access to official upstream vendors is required for first-time dependency restoration. Allow substantial disk space for Lean and the mathlib cache.

From the assembled project directory, first install the official Lean release into a new, project-local tools directory:

```sh
cd ../dynamic-calculus-project
mkdir .checkpoint-tools
curl --fail --location --retry 3 \
  https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst \
  -o .checkpoint-tools/lean-4.35.0-linux.tar.zst
printf '%s  %s\n' \
  7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d \
  .checkpoint-tools/lean-4.35.0-linux.tar.zst | sha256sum --check -
tar --zstd -xf .checkpoint-tools/lean-4.35.0-linux.tar.zst -C .checkpoint-tools
export PATH="$PWD/.checkpoint-tools/lean-4.35.0-linux/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.checkpoint-tools/mathlib-cache"
lean --version
lake --version
```

Expected compiler: Lean **4.35.0**, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Lake: **5.0.0-src+eb6cafb**. The archive SHA-256 was checked against the official GitHub release metadata when preparing this checkpoint.

Fetch **every exact revision already recorded in the original `lake-manifest.json`**, without updating that manifest:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib, json, re, subprocess
manifest = Path('lake-manifest.json')
if hashlib.sha256(manifest.read_bytes()).hexdigest() != '0e4afebb985207e83e2a2fdf3d42281f9986e939ebc31084eaa5f8c3479c22cc':
    raise SystemExit('Unexpected lake-manifest.json; stop and recheck assembly')
packages = Path('.lake/packages')
packages.mkdir(parents=True)  # Deliberately fail if a dependency directory already exists.
for p in json.loads(manifest.read_text())['packages']:
    name, url, rev = p['name'], p['url'], p['rev']
    if not re.fullmatch(r'[A-Za-z0-9_-]+', name) or not re.fullmatch(r'[0-9a-f]{40}', rev):
        raise SystemExit('Invalid pinned package identity')
    if not url.startswith(('https://github.com/leanprover/', 'https://github.com/leanprover-community/')):
        raise SystemExit('Unexpected dependency vendor')
    target = packages / name
    subprocess.run(['git', 'init', str(target)], check=True)
    def git(*args):
        return subprocess.check_output(['git', '-C', str(target), *args], text=True).strip()
    git('remote', 'add', 'origin', url)
    git('fetch', '--depth=1', 'origin', rev)
    git('checkout', '--detach', 'FETCH_HEAD')
    if git('rev-parse', 'HEAD') != rev:
        raise SystemExit('Pinned dependency HEAD mismatch: ' + name)
    print('Verified', name, rev)
PY
lake exe cache get
```

The main mathlib pin is `56a005855ea17e0b0958f73ec801ae140b0a1679`; the original manifest fixes all nine dependency revisions. `lake exe cache get` builds the cache program from the pinned official mathlib source and retrieves official upstream dependency artifacts. **Do not run `lake update`** or substitute newer revisions. If restoration is interrupted, inspect the partial directories and restart in a newly assembled project rather than weakening any checks.

Then run the actual verification entry point:

```sh
bash scripts/verify_dynamic.sh
```

It checks the original export and integration hashes, builds the dynamic bridge, checks 19 headline axiom closures, then invokes the independent fresh-project verifier. The latter compiles all seven dynamic modules in another new project, sharing only the pinned external dependency cache; runs four independent Lean regression modules; requires two invalid constructions to fail with Lean type errors; and checks 38 named axiom closures. It rechecks the source freeze and original API/manifest hashes afterwards. Logs are created under `reproduction/` and `audit/dynamic_independent/evidence/`; these generated outputs are not immutable source inputs. The fresh project is created beside the assembled project, so that parent directory must be writable.

For an already restored environment, put the exact pinned Lean/Lake binaries on PATH and provide its verified `.lake/packages` cache (a dependency-only symlink is sufficient). Do not copy another project's `.lake/build`, `.olean`, or `.ilean` artifacts. The original dynamic README's `source ../.toolchain/env.sh` command refers only to the preparation workspace; that helper and workspace are not required or included here.

## Proved scope and test coverage

The seven modules establish graph maps with actual event records; substitution along the original occurrence API; map-operation unit and associativity laws; compatibility under arbitrary occurrence substitution; compatible-tuple graphs; the actual boundary-compatible dynamic `Calc`; and its free/presented extension and refinement bridges. The original equation quotient is retained. See `overlay/WitnessedDecompositions/Dynamic/README.md` and the Lean statements for the precise definitions and hypotheses.

The target retains all graph maps, including nonexact ones. Nullary fibres are inhabited exactly when the boundary legs agree, are subsingletons, and have the common leg as their witness. Nullary exactness is precisely isomorphism of that leg; identity witnesses are exact. Sortwise bijectivity characterizes graph-map isomorphism on both states and actual events. No finiteness hypothesis is required.

Independent examples distinguish nonterminal empty boundaries, unequal legs, nonexact nullaries (including event-only collapse), all-empty substitution, repeated colours with different occurrence maps, parallel event records, a nonempty declared equation, an invalid event-permutation equation, and distinct refinement forests with the same substituted root. Negative controls reject an incidence-breaking graph map and a purported empty path between distinct endpoints.

## Trust boundary and remaining work

The new local proof terms were freshly compiled and checked by the Lean kernel. The axiom closure union is limited to Lean's standard `propext`, `Quot.sound`, and `Classical.choice`. The source screen rejects `sorry`, `admit`, `sorryAx`, new `axiom` declarations, and `native_decide` in the screened Lean sources. The actual dynamic target calculus does not depend on `Classical.choice`; choice appears in the bijective/inverse characterization and existing generic presentation quotient machinery.

This uses the official precompiled Lean toolchain and upstream compiled dependency cache; it is **not** an independent rebuild or audit of Lean, mathlib, or every transitive dependency. Hash checks and source screens complement, but do not replace, kernel checking or mathematical review.

This focused checkpoint does not prove the later general exact-substitution theorem, execution/time comparison, interface-change theorems, CFG/decision procedures, or physical implementation correctness. A concrete assignment and proof of its equations are still needed for each presented interpretation. It is not a full-paper formalization, a rerun of every historical workstream, or a grant of scientific/contractual acceptance.
