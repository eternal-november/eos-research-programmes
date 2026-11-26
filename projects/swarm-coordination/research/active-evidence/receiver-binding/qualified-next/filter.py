"""Qualify a locally observed probe without splicing installed-law rows."""
from dataclasses import dataclass

@dataclass(frozen=True)
class History:
    binding: str
    probe_receipt: bool
    old_receipt: bool
    next_receipt: bool
    # One immutable source-world label certifies this complete tuple.
    source: str

def check(all_worlds, seen, require_old=True):
    candidates=tuple(w for w in all_worlds if w.probe_receipt==seen)
    if not candidates:return "inconsistent",()
    accepted={w.next_receipt and (w.old_receipt or not require_old) for w in candidates}
    if accepted=={True}:return "carries",candidates
    if accepted=={False}:return "refuted",candidates
    return "undecided",candidates
