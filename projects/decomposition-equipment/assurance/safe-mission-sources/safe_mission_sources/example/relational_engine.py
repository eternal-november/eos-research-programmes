#!/usr/bin/env python3
"""Exact finite persistent-mechanism knowledge on a forest of sum diagnostics.

No plant truth is accepted by this module. A hypothesis is a fixed Boolean
function of <=2 distinct command-port run-threshold features. Coordinate and
pair-sum observations constrain those functions for the entire execution.

Important scope: the *diagnostic constraint graph* must be a forest. This is not
an assertion that physical response scopes are disjoint or tree-shaped. New
cycle-closing aggregate observations are rejected, not silently approximated.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass, field
from itertools import combinations, product
import numpy as np


class CycleError(ValueError):
    """The requested aggregate would leave the supported forest class."""


class InconsistentEvidence(ValueError):
    """Evidence has no world in the declared structural class."""


def iter_ids(mask: int):
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask ^= b


class Catalogue:
    """Canonical complete <=2-port run-threshold hypothesis universe.

    Binary table bit index is x_first + 2*x_second. Unary tables are 1 (NOT)
    and 2 (identity), indexed by x_first. Constants have kind 0 and table 0/1.
    Port order is increasing and binary tables must depend essentially on both
    inputs. Hence dummy-variable and argument-order duplicates are excluded.
    """
    def __init__(self, n_ports: int, L: int):
        if n_ports < 1 or L < 1:
            raise ValueError('n_ports and L must be positive')
        self.n_ports, self.L = int(n_ports), int(L)
        rows = [(0, -1, 0, -1, 0, 0), (0, -1, 0, -1, 0, 1)]
        for p in range(n_ports):
            for r in range(1, L + 1):
                rows.extend((1, p, r, -1, 0, t) for t in (1, 2))
        tables = [t for t in range(16) if
                  (((t >> 0) & 1) != ((t >> 1) & 1) or
                   ((t >> 2) & 1) != ((t >> 3) & 1)) and
                  (((t >> 0) & 1) != ((t >> 2) & 1) or
                   ((t >> 1) & 1) != ((t >> 3) & 1))]
        assert len(tables) == 10
        for p, q in combinations(range(n_ports), 2):
            for r, s in product(range(1, L + 1), repeat=2):
                rows.extend((2, p, r, q, s, t) for t in tables)
        data = np.asarray(rows, dtype=np.int32)
        self.kind, self.p, self.r, self.q, self.s, self.table = data.T
        self.size = len(rows)
        self.full = (1 << self.size) - 1
        self._cache: dict[tuple[int, ...], int] = {}
        self.counters = {'evaluated_contexts': 0, 'candidate_evaluations': 0,
                         'prediction_cache_hits': 0}

    def context(self, counters):
        raw_values = tuple(counters)
        c = tuple(int(v) for v in raw_values)
        if len(c) != self.n_ports or any(v < 0 or v > self.L for v in c):
            raise ValueError('context must contain n_ports counters in [0,L]')
        # Reject nonintegral numeric input rather than truncating it silently.
        if any(v != raw for v, raw in zip(c, raw_values)):
            raise ValueError('counter context must be integral')
        return c

    def prediction_mask(self, counters, value=1) -> int:
        if value not in (0, 1):
            raise ValueError('Boolean output required')
        c = self.context(counters)
        if c not in self._cache:
            a = np.asarray(c, dtype=np.int32)
            first = (a[np.maximum(self.p, 0)] >= self.r).astype(np.int32)
            second = (a[np.maximum(self.q, 0)] >= self.s).astype(np.int32)
            index = np.where(self.kind == 2, first + 2 * second, first)
            pred = ((self.table >> index) & 1).astype(np.uint8)
            pred[self.kind == 0] = self.table[self.kind == 0]
            packed = np.packbits(pred, bitorder='little').tobytes()
            self._cache[c] = int.from_bytes(packed, 'little') & self.full
            self.counters['evaluated_contexts'] += 1
            self.counters['candidate_evaluations'] += self.size
        else:
            self.counters['prediction_cache_hits'] += 1
        m = self._cache[c]
        return m if value else self.full ^ m

    def evaluate(self, hypothesis: int, counters) -> int:
        if not 0 <= hypothesis < self.size:
            raise IndexError('hypothesis ID outside catalogue')
        return (self.prediction_mask(counters) >> hypothesis) & 1

    def describe(self, hypothesis: int):
        if not 0 <= hypothesis < self.size:
            raise IndexError('hypothesis ID outside catalogue')
        k = int(self.kind[hypothesis])
        features = []
        if k:
            features.append([int(self.p[hypothesis]), int(self.r[hypothesis])])
        if k == 2:
            features.append([int(self.q[hypothesis]), int(self.s[hypothesis])])
        return {'id': int(hypothesis), 'features': features,
                'table': int(self.table[hypothesis]), 'arity': k}

    def find(self, features, table: int):
        fs = [tuple(map(int, f)) for f in features]
        if len(fs) > 2 or (len(fs) == 2 and fs[0][0] >= fs[1][0]):
            raise ValueError('provide <=2 features with strictly increasing ports')
        match = (self.kind == len(fs)) & (self.table == table)
        if fs:
            match &= (self.p == fs[0][0]) & (self.r == fs[0][1])
        if len(fs) == 2:
            match &= (self.q == fs[1][0]) & (self.s == fs[1][1])
        ids = np.flatnonzero(match)
        if len(ids) != 1:
            raise ValueError('no canonical hypothesis has that description')
        return int(ids[0])


@dataclass
class Edge:
    a: int
    b: int
    groups: dict[int, int]
    records: list = field(default_factory=list)
    zeros: int = 0
    ones: int = 0
    complements: int = 0

    def clone(self):
        return Edge(self.a, self.b, dict(self.groups), list(self.records),
                    self.zeros, self.ones, self.complements)

    def add(self, context, total, prediction_mask):
        position = len(self.records)
        bit = 1 << position
        new = {}
        for signature, candidates in self.groups.items():
            yes = candidates & prediction_mask
            no = candidates ^ yes
            if no:
                new[signature] = no
            if yes:
                new[signature | bit] = yes
        self.groups = new
        self.records.append((tuple(context), int(total)))
        if total == 0:
            self.zeros |= bit
        elif total == 2:
            self.ones |= bit
        else:
            self.complements |= bit

    def partner(self, signature):
        if signature & self.zeros or signature & self.ones != self.ones:
            return None
        return self.ones | ((~signature) & self.complements)


class ForestKnowledge:
    def __init__(self, catalogue: Catalogue, n_outputs: int):
        if n_outputs < 1:
            raise ValueError('positive n_outputs required')
        self.catalogue, self.n_outputs = catalogue, int(n_outputs)
        self.domains = [catalogue.full] * n_outputs
        self.edges: dict[tuple[int, int], Edge] = {}
        self.coordinates = []
        self.counters = {'propagation_calls': 0, 'arc_revisions': 0,
                         'signature_checks': 0, 'feasibility_queries': 0,
                         'candidate_eliminations': 0}

    def copy(self):
        other = ForestKnowledge(self.catalogue, self.n_outputs)
        other.domains = list(self.domains)
        other.edges = {k: e.clone() for k, e in self.edges.items()}
        other.coordinates = list(self.coordinates)
        other.counters = dict(self.counters)
        return other

    def _output(self, i):
        if not isinstance(i, (int, np.integer)) or not 0 <= i < self.n_outputs:
            raise ValueError('output index outside declared interface')
        return int(i)

    def _adjacency(self):
        adj = [[] for _ in range(self.n_outputs)]
        for a, b in self.edges:
            adj[a].append(b)
            adj[b].append(a)
        return adj

    def _would_cycle(self, a, b):
        if (min(a, b), max(a, b)) in self.edges:
            return False
        adj = self._adjacency()
        seen, stack = {a}, [a]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y == b:
                    return True
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return False

    def _propagate(self, domains):
        """Enforce exact tree-CSP domain projection using directed arc revision.

        On an acyclic binary constraint graph, arc consistency plus nonempty
        domains is equivalent to existence, and every remaining value extends
        to a coherent global assignment. This is false for general cycles.
        """
        self.counters['propagation_calls'] += 1
        if any(not d for d in domains):
            return False
        adj = self._adjacency()
        queue = deque((a, b) for a, bs in enumerate(adj) for b in bs)
        while queue:
            a, b = queue.popleft()
            edge = self.edges[(min(a, b), max(a, b))]
            supported = 0
            self.counters['arc_revisions'] += 1
            for sig, group in edge.groups.items():
                left = domains[a] & group
                if not left:
                    continue
                self.counters['signature_checks'] += 1
                partner = edge.partner(sig)
                if partner is not None and domains[b] & edge.groups.get(partner, 0):
                    supported |= left
            if supported != domains[a]:
                domains[a] = supported
                if not supported:
                    return False
                queue.extend((neighbor, a) for neighbor in adj[a] if neighbor != b)
        return True

    def state_key(self):
        """Hashable exact knowledge key for caller-side policy memoization.

        Duplicate evidence records do not alter this key. Catalogue dimensions
        and output count must be fixed within a memoized planning problem.
        """
        return (tuple(self.domains), tuple((key, tuple(sorted(set(edge.records))))
                for key, edge in sorted(self.edges.items())))

    def consistent(self):
        return self._propagate(list(self.domains))

    def observe_coordinate(self, i, context, value):
        """Commit evidence; contradictory evidence leaves an empty knowledge set.

        Returns consistency rather than inventing a fallback model. A caller
        may copy before acquisition if it needs transactional branch creation.
        """
        i = self._output(i)
        c = self.catalogue.context(context)
        mask = self.catalogue.prediction_mask(c, value)
        before = sum(d.bit_count() for d in self.domains)
        self.domains[i] &= mask
        self.coordinates.append((i, c, int(value)))
        valid = self._propagate(self.domains)
        self.counters['candidate_eliminations'] += before - sum(d.bit_count() for d in self.domains)
        return valid

    def observe_sum(self, i, j, context, total):
        i, j = self._output(i), self._output(j)
        if i == j or total not in (0, 1, 2):
            raise ValueError('sum needs distinct outputs and total 0,1,2')
        c = self.catalogue.context(context)
        if self._would_cycle(i, j):
            raise CycleError('aggregate would create a cycle; no approximation applied')
        key = (min(i, j), max(i, j))
        before = sum(d.bit_count() for d in self.domains)
        edge = self.edges.setdefault(key, Edge(*key, {0: self.catalogue.full}))
        edge.add(c, total, self.catalogue.prediction_mask(c))
        valid = self._propagate(self.domains)
        self.counters['candidate_eliminations'] += before - sum(d.bit_count() for d in self.domains)
        return valid

    def feasible(self, assignments=(), domain_restrictions=None):
        """Whether one fixed joint world satisfies all supplied unary claims.

        assignments consists of (output, counter_context, bit) triples. Queries
        may involve repeated variables at different contexts. A single local
        function must satisfy every query concerning that variable.
        """
        self.counters['feasibility_queries'] += 1
        domains = list(self.domains)
        if domain_restrictions:
            for i, mask in domain_restrictions.items():
                domains[self._output(i)] &= int(mask) & self.catalogue.full
        for i, c, bit in assignments:
            i = self._output(i)
            domains[i] &= self.catalogue.prediction_mask(c, bit)
        return self._propagate(domains)

    def possible_coordinate(self, i, context):
        return tuple(v for v in (0, 1) if self.feasible([(i, context, v)]))

    def possible_sum(self, i, j, context):
        i, j = self._output(i), self._output(j)
        if i == j:
            raise ValueError('sum requires distinct outputs')
        return tuple(s for s in (0, 1, 2) if any(
            self.feasible([(i, context, a), (j, context, b)])
            for a, b in product((0, 1), repeat=2) if a + b == s))

    def possible_vectors(self, queries):
        """Exact joint outcomes for a caller-bounded set of coordinate queries.

        Exponential in len(queries), explicitly not a polynomial planning claim.
        """
        queries = list(queries)
        return tuple(bits for bits in product((0, 1), repeat=len(queries)) if
                     self.feasible([(i, c, bit) for (i, c), bit in zip(queries, bits)]))

    def guarantees(self, assignments):
        """Universal conjunction, false on inconsistent evidence (no vacuity)."""
        if not self.consistent():
            return False
        for i, c, bit in assignments:
            if bit not in (0, 1):
                raise ValueError('Boolean output required')
            if self.feasible([(i, c, 1 - bit)]):
                return False
        return True

    def discovered_interface(self, i):
        """Conservative union interface and recursive run-counter caps.

        This is task-sufficient support, not unique physical ownership. Each
        local hypothesis has no dummy inputs; ambiguity remains explicit.
        """
        i = self._output(i)
        d = self.domains[i]
        caps = [0] * self.catalogue.n_ports
        scopes = set()
        for h in iter_ids(d):
            desc = self.catalogue.describe(h)
            scopes.add(tuple(p for p, _ in desc['features']))
            for p, r in desc['features']:
                caps[p] = max(caps[p], r)
        return {'output': i, 'candidates': d.bit_count(),
                'ports': [p for p, r in enumerate(caps) if r],
                'counter_caps': caps, 'candidate_scopes': [list(s) for s in sorted(scopes)],
                'unique_scope': len(scopes) == 1,
                'unique_response': d.bit_count() == 1,
                'empty_knowledge': not bool(d)}

    def metrics(self):
        edge_metrics = []
        for (a, b), edge in sorted(self.edges.items()):
            active_a = sum(bool(self.domains[a] & g) for g in edge.groups.values())
            active_b = sum(bool(self.domains[b] & g) for g in edge.groups.values())
            compatible = sum(bool(self.domains[a] & g) and
                             edge.partner(sig) is not None and
                             bool(self.domains[b] & edge.groups.get(edge.partner(sig), 0))
                             for sig, g in edge.groups.items())
            edge_metrics.append({'outputs': [a, b], 'observations': len(edge.records),
                                 'catalogue_signatures': len(edge.groups),
                                 'active_signatures': [active_a, active_b],
                                 'compatible_signature_pairs': compatible})
        return {'catalogue_size': self.catalogue.size,
                'outputs': self.n_outputs, 'local_domain_sizes': [d.bit_count() for d in self.domains],
                'diagnostic_constraint_edges': len(self.edges),
                'diagnostic_treewidth_upper_bound': 1 if self.edges else 0,
                'full_joint_product_enumerated': False,
                'coordinate_observations': len(self.coordinates), 'edges': edge_metrics,
                'domain_bitset_payload_bytes': sum((d.bit_length() + 7) // 8 for d in self.domains),
                'edge_group_bitset_payload_bytes': sum((g.bit_length() + 7) // 8
                    for edge in self.edges.values() for g in edge.groups.values()),
                'operation_counts': dict(self.counters),
                'catalogue_operation_counts': dict(self.catalogue.counters)}
