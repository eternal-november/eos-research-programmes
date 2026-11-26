"""Exact reserve-profile algebra for an unchanged retained plant.

Packs a finite support relation at a declared boundary. This module intentionally
knows nothing about robot identities, failure labels, or how new policies select
actions; it is used only to evaluate a fixed service obligation in a model.
"""
from dataclasses import dataclass

@dataclass(frozen=True)
class Profile:
    # A boundary absent from entries is impossible, not zero available capacity.
    entries: tuple

    @staticmethod
    def from_worlds(retained):
        p = {}
        for b, availability in retained:
            assert type(availability) is int and availability >= 0
            if b not in p or availability < p[b]:
                p[b] = availability
        return Profile(tuple(sorted(p.items())))

    def verdict(self, model):
        """Addition of capacity and service cost may vary by valid boundary.

        Model maps selected slices to one or more (extra supply, owed units)
        continuations. Its join with retained states must be saturated at the
        declared boundary, or the result is not an exact verdict. A model
        cannot assert a first reachable slice using this old certificate.
        """
        p = dict(self.entries)
        if any(b not in p for b in model):
            return "unbound"
        # Empty list in a declared cell is a disabled continuation.
        if not any(model.values()):
            return "no-continuation"
        return ("served" if all(p[b] + extra >= need
                                for b, ts in model.items() for extra, need in ts)
                else "shortfall")
