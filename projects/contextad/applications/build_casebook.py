#!/usr/bin/env python3
"""Assemble the standalone O6 TeX from reviewed authoring fragments."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
parts=sorted((ROOT/'authoring').glob('[0-9][0-9]_*.tex'))
assert len(parts)==11, [p.name for p in parts]
out=ROOT/'Applications_and_Boundaries_of_Result_Dependent_Interaction.tex'
out.write_text('\n'.join(p.read_text() for p in parts))
print(json.dumps({'output':out.name,'parts':len(parts),'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest()},indent=2))
