"""Development checker for sealed, paired simulation comparisons (not an authenticator)."""
import hashlib
import json


def digest(kind, *objects):
    # This is the representation for the Python reference, not generic JSON canonicalization.
    raw = json.dumps((kind, *objects), sort_keys=True, ensure_ascii=True,
                     separators=(',', ':'), allow_nan=False).encode('ascii')
    return hashlib.sha256(raw).hexdigest()


def index(rows):
    result = {row['id']: row for row in rows}
    if len(result) != len(rows):
        raise ValueError('duplicate identity')
    return result


def check_transcript(plan, seal, roster, opening, reports):
    """Hashes bind bytes; nothing here attests who saw what or when."""
    if roster['plan'] != digest('plan-v1', plan):
        raise ValueError('wrong plan')
    if seal != digest('roster-v1', opening, roster):
        raise ValueError('roster mismatch')
    cases = index(roster['cases'])
    arms = index(plan['arms'])
    if len(arms) < 2 or not cases:
        raise ValueError('empty comparison')
    if len({c['source'] for c in cases.values()}) != len(cases):
        raise ValueError('duplicate declared primitive input')
    seen = {}
    for row in reports:
        key = row['case'], row['arm']
        case, arm = cases.get(key[0]), arms.get(key[1])
        if not case or not arm or key in seen:
            raise ValueError('unknown or repeated attempt')
        if (row['source'] != case['source'] or row['build'] != arm['build']
                or row['interface'] != plan['interface']):
            raise ValueError('unmatched version or primitive input')
        if row['status'] not in ('complete', 'terminal-failure', 'unresolved'):
            raise ValueError('unknown status')
        seen[key] = row['status']
    return {key: seen.get(key, 'unresolved') for key in
            ((c, a) for c in cases for a in arms)}


def compare_supports(row_supports, threshold):
    """Exact bounded comparison conditional on a product across case blocks.

    Per-case alternatives are JOINT (nondeterminism, ambiguity or missing rows).
    Each member is (candidate safety, candidate service floor, paired improvement).
    Improvement is a frozen signed integer endpoint (positive favours candidate).
    """
    if not row_supports or any(not s for s in row_supports):
        raise ValueError('empty experiment or inconsistent evidence')
    eligible = all(safe and floor for support in row_supports for safe, floor, _ in support)
    certain_failure = any(all(not (safe and floor) for safe, floor, _ in support)
                          for support in row_supports)
    lo = sum(min(v for _, _, v in s) for s in row_supports)
    hi = sum(max(v for _, _, v in s) for s in row_supports)
    feasible = [[v for safe, floor, v in s if safe and floor] for s in row_supports]
    best_eligible = sum(max(s) for s in feasible) if not certain_failure else None
    verdict = ('certain-pass' if eligible and lo >= threshold else
               'ruled-out' if best_eligible is None or best_eligible < threshold else
               'unresolved')
    return lo, hi, verdict
