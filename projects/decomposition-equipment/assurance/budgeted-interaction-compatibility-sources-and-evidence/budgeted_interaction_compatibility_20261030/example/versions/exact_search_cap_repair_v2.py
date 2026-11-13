"""Exact finite-horizon robust AND/OR search, with explicit incomplete status.

Model contract: terminal returns None or (WIN|LOSE, reason); actions is the
complete allowed action list; transition returns an unsafe witness or every
feasible observation and its successor. Search has no actual-world argument.
"""
from __future__ import annotations
from dataclasses import dataclass
import json, time, hashlib
from typing import Any

WIN, LOSE, UNKNOWN = 'WIN', 'LOSE', 'UNKNOWN'

class BudgetExhausted(Exception):
    pass

@dataclass(frozen=True)
class Step:
    unsafe: Any = None
    outcomes: tuple = ()  # tuple of (observation, successor)

class ExactSearch:
    def __init__(self, model, max_nodes=100000, max_seconds=60.0):
        self.model = model
        self.max_nodes = max_nodes
        self.max_seconds = max_seconds
        self.memo = {}
        self.cert = {}
        self.active = set()
        self.started = None
        self.stats = dict(expanded=0, memo_hits=0, transition_calls=0,
                          outcome_edges=0, unsafe_actions=0, limits_hit=0,
                          peak_depth=0)

    def node_id(self, state):
        blob = json.dumps(self.model.encode_state(state), sort_keys=True,
                          separators=(',', ':')).encode()
        return hashlib.sha256(blob).hexdigest()

    def solve(self, state):
        if self.started is not None:
            raise RuntimeError('ExactSearch is single-use; create a new query instance')
        self.started = time.perf_counter()
        try:
            status = self._visit(state, 0)
        except BudgetExhausted:
            status = UNKNOWN
            self.stats['limits_hit'] += 1
        elapsed = time.perf_counter() - self.started
        root = self.node_id(state)
        used = {}
        if status != UNKNOWN:
            def keep(n):
                if n in used: return
                c = self.cert[n]
                used[n] = c
                if c['kind'] == 'choice':
                    for edge in c['outcomes']: keep(edge['next'])
                elif c['kind'] == 'refutation':
                    for a in c['actions']:
                        if 'next' in a: keep(a['next'])
            keep(root)
        self.stats.update(elapsed_seconds=elapsed, memo_size=len(self.memo),
                          certificate_nodes=len(used))
        return dict(status=status, root=root, statistics=self.stats.copy(),
                    certificate=used)

    def _store(self, state, status, **record):
        self.memo[state] = status
        nid = self.node_id(state)
        self.cert[nid] = dict(status=status, state=self.model.encode_state(state),
                              **record)
        return status

    def _visit(self, state, depth):
        self.stats['peak_depth'] = max(self.stats['peak_depth'], depth)
        if state in self.memo:
            self.stats['memo_hits'] += 1
            return self.memo[state]
        terminal = self.model.terminal(state)
        if terminal is not None:
            status, reason = terminal
            assert status in (WIN, LOSE)
            return self._store(state, status, kind='terminal', reason=reason)
        if (self.stats['expanded'] >= self.max_nodes or
            time.perf_counter() - self.started >= self.max_seconds):
            raise BudgetExhausted
        if state in self.active:
            raise ValueError('Model violated finite-horizon acyclicity')
        self.active.add(state)
        self.stats['expanded'] += 1
        rejected, saw_unknown = [], False
        for action in self.model.actions(state):
            if time.perf_counter() - self.started >= self.max_seconds:
                raise BudgetExhausted
            self.stats['transition_calls'] += 1
            step = self.model.transition(state, action)
            encoded_action = self.model.encode_action(action)
            if step.unsafe is not None:
                self.stats['unsafe_actions'] += 1
                rejected.append(dict(action=encoded_action, unsafe=step.unsafe))
                continue
            if not step.outcomes:
                raise ValueError('Safe allowed action has no feasible outcome')
            self.stats['outcome_edges'] += len(step.outcomes)
            edges, unknown, losing = [], False, None
            for observation, successor in step.outcomes:
                if time.perf_counter() - self.started >= self.max_seconds:
                    raise BudgetExhausted
                status = self._visit(successor, depth + 1)
                edge = dict(observation=self.model.encode_observation(observation),
                            next=self.node_id(successor))
                edges.append(edge)
                if status == LOSE:
                    losing = edge
                    break
                if status == UNKNOWN:
                    unknown = True
            if losing is not None:
                rejected.append(dict(action=encoded_action, **losing))
            elif unknown:
                saw_unknown = True
            else:
                self.active.remove(state)
                return self._store(state, WIN, kind='choice',
                                   action=encoded_action, outcomes=edges)
        self.active.remove(state)
        if saw_unknown:
            return UNKNOWN
        return self._store(state, LOSE, kind='refutation', actions=rejected)
