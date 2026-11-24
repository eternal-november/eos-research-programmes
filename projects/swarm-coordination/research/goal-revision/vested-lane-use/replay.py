#!/usr/bin/env python3
"""Discrete civil warehouse goal revision; compare installed local guards to exact cuts."""
import json
from itertools import product


class Gate:
    def __init__(self, window, lasts_until, duration):
        self.stock = 'A'
        self.token = None
        self.old_until = None
        self.forward_due = None
        self.return_due = None
        self.trace = []
        self.window = window
        self.lasts_until = lasts_until
        self.duration = duration
        self.goal = 'store-B'
        self.restored_at = None
        self.old_result = None

    def log(self, t, event, *payload):
        self.trace.append([t, event, *payload])

    def frozen_snapshot(self):
        return [self.stock, self.old_until is not None, self.token]

    def advance(self, t):
        # Release before start: [s,s+d), so acceptance frees A at s+d.
        if self.forward_due == t:
            self.forward_due = None
            self.stock = 'B'
            self.log(t, 'placed', 'B', 'original-load')
        if self.old_until == t:
            self.old_until = None
            self.old_result = 'served'
            self.log(t, 'released', 'old-service-1')
        if self.return_due == t:
            self.return_due = None
            self.stock = 'A'
            self.restored_at = t
            self.log(t, 'placed', 'A', 'restoration-load')
        if self.token == 'unexercised' and t >= self.lasts_until:
            self.token = 'expired'
            self.old_result = 'expired-unused'
            self.log(t, 'start-authority-closed', 'old-service-1')

    def start_old(self, t, d):
        assert t < self.window and self.token == 'unexercised'
        assert self.stock == 'B' and self.old_until is None and self.return_due is None
        self.token = 'consumed'
        self.old_until = t + d
        self.log(t, 'old-service-start', 'old-service-1', t + d)

    def attempt_return(self, t, controller_has_notice, protection=True):
        if (self.goal != 'restore-A' or not controller_has_notice or self.stock != 'B' or self.old_until is not None
                or self.forward_due is not None or self.return_due is not None
                or (protection and self.token == 'unexercised')):
            self.log(t, 'rejected-return')
            return False
        self.stock = 'in-return'
        self.return_due = t + self.duration
        self.log(t, 'return-start', self.return_due)
        return True


def simulate(*, pairs, expiry, use, old_right, revise, notice, deadline, duration,
             signed=True, roster_visible=True, certificate_delay=None,
             policy='sealed-envelope', release=None):
    """The operator revises load storage; only the old right-holder can waive unused service."""
    assert pairs and all(0 <= a < expiry and d >= 1 for a, d in pairs)
    g = Gate(expiry, max(a for a, _ in pairs) + 1, duration)
    g.forward_due = -1
    g.log(-2, 'forward-start', 'A', 'B', 'original-load')
    g.advance(-1)
    if old_right:
        g.token = 'unexercised'
        g.log(-1, 'holder-accepted-irrevocable-right', 'old-service-1', expiry)
    assert use is None or (old_right and use in pairs)
    assert release is None or (old_right and use is None and release < g.lasts_until)
    assert notice >= revise
    # Each signed revision seals admissions for this lane: it never cancels a vested right.
    # Actor-local static operating envelope. Hidden roster does not expose any actual token.
    upper = max([revise] + [a + d for a, d in pairs])
    observed_head = None
    cert_arrival = None
    certified = False
    failed_old = False
    for t in range(max(notice, deadline, upper, expiry, revise) + duration + (certificate_delay or 0) + 2):
        g.advance(t)
        if t == revise:
            g.log(t, 'goal-cut', *g.frozen_snapshot())
            if signed:
                g.goal = 'restore-A'
                g.log(t, 'authorized-effective-revision', 'storage-operator', 'A', deadline)
                g.log(t, 'close-new-issuance-on-lane-A')
            else:
                g.log(t, 'unauthenticated-revision-no-effect')
        if t == notice and signed:
            observed_head = old_right if roster_visible else None
            g.log(t, 'local-authenticated-revision-notice', observed_head)
        if t == release:
            assert g.token == 'unexercised' and g.old_until is None
            g.token = 'waived'
            g.old_result = 'released-by-right-holder'
            g.log(t, 'holder-authorized-waiver', 'old-service-1')
        if (cert_arrival is None and certificate_delay is not None and g.goal == 'restore-A'
                and g.token != 'unexercised' and g.old_until is None):
            # Exact irreversible lane-clearance witness after issuance has sealed.
            cert_arrival = t + certificate_delay
            g.log(t, 'signed-clearance-issued', 'sealed-revision')
        if t == cert_arrival:
            certified = True
            g.log(t, 'signed-clearance-received', 'sealed-revision')
        delivered = signed and t >= notice
        if delivered and g.stock == 'B' and not any(e[1] == 'return-start' for e in g.trace):
            if policy == 'vacancy-only':
                if g.old_until is None:
                    g.attempt_return(t, delivered, protection=False)
            else:
                assert policy == 'sealed-envelope'
                if observed_head is False or certified or t >= upper:
                    assert g.attempt_return(t, delivered)
        if use is not None and use[0] == t:
            if g.stock != 'B' or g.return_due is not None:
                failed_old = True
                g.log(t, 'old-service-refused', 'old-service-1')
            else:
                g.start_old(t, use[1])
        assert not (g.old_until is not None and g.stock != 'B')
        assert not (g.return_due is not None and g.old_until is not None)
    return dict(accepted_revision=signed, restored=g.restored_at,
                deadline_met=g.restored_at is not None and g.restored_at <= deadline,
                old_preserved=not failed_old and (use is None or g.old_result == 'served'),
                old_outcome=g.old_result, final_stock=g.stock, trace=g.trace)


def reference_worst(*, pairs, revise, notice, duration, old_right):
    """Exhaust candidate start times against earliest blocked intervals on all continuations."""
    states = [None] + (list(pairs) if old_right else [])
    for s in range(notice, notice + duration + max([revise] + [a + d for a, d in pairs]) + 1):
        # A return occupies A forever from s. For each possible start, this
        # excludes even later service, not merely overlap with travel itself.
        if all(event is None or all(u < s for u in range(event[0], sum(event))) for event in states):
            return s + duration
    raise AssertionError('reference scan too small')


def pair_set(expiry, dwell, law):
    return [(a, d) for a in range(expiry) for d in range(1, dwell + 1)
            if law == 'start-by' or a + d <= expiry]


def main():
    base = dict(pairs=pair_set(3, 2, 'start-by'), expiry=3, revise=2, notice=2, duration=1, deadline=3)
    featured = {}
    for k, kwargs in {
        'no_right_goals_met': dict(old_right=False, use=None),
        'unexercised_same_stock': dict(old_right=True, use=(2, 2)),
        'positive_later_deadline': dict(old_right=True, use=(2, 2), deadline=5),
        'vacancy_only_denies_old': dict(old_right=True, use=(2, 2), policy='vacancy-only'),
        'waiver_authorized_before_start': dict(old_right=True, use=None, release=2, certificate_delay=0),
        'settled_before_revision': dict(old_right=True, use=(0, 1), certificate_delay=0),
        'pending_occupancy_outlives_start_authority': dict(old_right=True, use=(2, 2), revise=3, notice=3, deadline=5),
        'last_eligible_phase_precedes_outer_expiry': dict(old_right=True, use=(0, 1), pairs=[(0, 1)], expiry=5),
        'late_notice': dict(old_right=False, use=None, notice=3),
        'unsigned_goal_does_not_apply': dict(old_right=True, use=(2, 2), signed=False),
        'sealed_roster_not_visible': dict(old_right=False, use=None, roster_visible=False),
        'sealed_roster_not_visible_but_timely_clear': dict(old_right=False, use=None, roster_visible=False, certificate_delay=0),
    }.items():
        featured[k] = simulate(**(base | kwargs))
    def chosen(k, result, goal, preserved=True):
        v=featured[k]
        assert (v['restored'], v['deadline_met'], v['old_preserved']) == (result, goal, preserved), k
    chosen('no_right_goals_met', 3, True)
    chosen('unexercised_same_stock', 5, False)
    chosen('positive_later_deadline', 5, True)
    chosen('vacancy_only_denies_old', 3, True, False)
    chosen('waiver_authorized_before_start', 3, True)
    chosen('settled_before_revision', 3, True)
    chosen('pending_occupancy_outlives_start_authority', 5, True)
    chosen('last_eligible_phase_precedes_outer_expiry', 3, True)
    chosen('late_notice', 4, False)
    chosen('unsigned_goal_does_not_apply', None, False)
    chosen('sealed_roster_not_visible', 5, False)
    chosen('sealed_roster_not_visible_but_timely_clear', 3, True)

    equal_prefixes = [next(row[:4] for row in featured[k]['trace'] if row[1]=='goal-cut')
                      for k in ('no_right_goals_met','unexercised_same_stock')]
    assert equal_prefixes[0] == equal_prefixes[1] == [2,'goal-cut','B',False]
    aged = next(row for row in featured['pending_occupancy_outlives_start_authority']['trace'] if row[1]=='goal-cut')
    assert aged == [3,'goal-cut','B',True,'consumed']
    assert featured['unsigned_goal_does_not_apply']['final_stock']=='B'
    assert [r for r in featured['pending_occupancy_outlives_start_authority']['trace'] if r[1]=='released'] == [[4,'released','old-service-1']]

    scenarios=checks=0
    for expiry, dwell, duration, revise, lag, law, old_right in product(
            range(1,6), range(1,5), range(1,4), (0,2,5), (0,1,3), ('start-by','finish-by'), (False,True)):
        pairs=pair_set(expiry,dwell,law)
        notice=revise+lag
        worst=reference_worst(pairs=pairs, revise=revise, notice=notice, duration=duration, old_right=old_right)
        closed=max(notice, (expiry-1+dwell if law=='start-by' else expiry) if old_right else notice)+duration
        assert worst==closed
        for use in ([None]+pairs if old_right else [None]):
            r=simulate(pairs=pairs, expiry=expiry, use=use, old_right=old_right, revise=revise, notice=notice,
                       deadline=worst, duration=duration)
            assert r['restored']==worst and r['deadline_met'] and r['old_preserved']
            checks+=1
        scenarios+=1
    # Exhibit identical latest-start and dwell maxima but a distinct joint envelope.
    end={}
    for law in ('start-by', 'finish-by'):
        ps=pair_set(3,2,law)
        end[law] = dict(latest=max(a for a,d in ps), longest=max(d for a,d in ps),
                        worst=reference_worst(pairs=ps, revise=2, notice=2, duration=1, old_right=True))
    assert end == {'start-by':{'latest':2,'longest':2,'worst':5}, 'finish-by':{'latest':2,'longest':2,'worst':4}}
    print(json.dumps(dict(scenarios=scenarios, traces_replayed=checks, featured=featured,
                          same_marginals_different_joint_envelope=end), sort_keys=True, indent=1))


if __name__=='__main__':
    main()
