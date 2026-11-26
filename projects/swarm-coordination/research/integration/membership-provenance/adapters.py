"""Authored civil reserve scenarios, constructed after core freeze.

An administrator's admission replaces an old supply lease. Domain membership is
a provenance fact about effects, not a claim about a robot's identity alone.
Each private capacity state is independent of the *declared* site outage law.
"""
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Plant:
    name: str
    demand: int
    # Retained capacity for (old_domain_failed=0 or 1; incidental work=0 or 1).
    retained: tuple
    support: int
    horizon: int

    def worlds(self):
        for group_failure, incidental in product((0,1),repeat=2):
            b = ("facility", group_failure, self.horizon)
            yield b, self.retained[group_failure][incidental]

    def install(self, source_id, ready=True):
        assert source_id in {"facility","dedicated"}
        # Exactly the admissible common state; at most one of the distinct
        # named domains is down. Incidental private work is not a site outage.
        all_fault_sets = [set(), {"facility"}]
        if source_id == "dedicated":
            all_fault_sets.append({"dedicated"})
        edits = {}
        for failed in all_fault_sets:
            b = ("facility", int("facility" in failed), self.horizon)
            edits.setdefault(b, set()).add((
                self.support if ready and source_id not in failed else 0,
                self.demand))
        return {b:sorted(value) for b,value in edits.items()}

    def native_matched(self, source_id, ready=True):
        """Direct enumeration from the declared world generator, no summary."""
        cases = []
        for (facility, incoming, incidental) in product((False,True), repeat=3):
            if source_id=="facility" and incoming!=facility:
                continue
            if source_id=="dedicated" and incoming and facility:
                continue
            have = self.retained[facility][incidental] + self.support*(ready and not incoming)
            cases.append((facility,incoming,incidental,have))
        return "served" if all(q[3]>=self.demand for q in cases) else "shortfall", cases


PLANTS=[
    Plant("warehouse staging units ready at pickup cut", 1, ((2,1),(1,0)), 1, 4),
    Plant("report forwarding opportunities at retry cut", 2, ((3,2),(1,0)), 2, 6),
]
