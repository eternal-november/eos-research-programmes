#!/usr/bin/env python3
"""Check native range/receipt distinctions against a stipulated crossing model."""
from collections import Counter
from pathlib import Path
import json

def main():
    rows = [tuple(map(int, line.split())) for line in
            Path(__file__).with_name("EXPECTED.txt").read_text().splitlines()]
    assert len(rows) == len(set(row[:6] for row in rows)) == 108
    findings = Counter()
    for renew, stale, boundary, fold, revoke, exercised, current, incoming, ready, grant, other in rows:
        if exercised:
            assert stale and not revoke
        assert current == (2 if renew == 1 else 1)
        assert incoming == (1 if stale else current)
        assert grant == (2 if ready and boundary else 1)
        assert other == (2 if boundary else 1)
        if fold:
            expected = not stale and (not revoke or fold == 2)
            assert bool(ready) == expected
            findings[f"forward arm {fold} wrong"] += expected != (not stale and not revoke)
            continue
        # Serial native paths are wrapped by a separate runtime admission
        # check, before starting the offered x=-2 to x=+2 segment.
        # On the scored attempt cut, B is at (0,-4),(0,0),(0,4).
        # Midpoint of traversal is (0,0); minimum modeled distance is
        # 4 or 0, respectively, because B waits there through the attempt.
        physical_exit = boundary == 2
        legitimate = not stale and not revoke
        should_serve = legitimate and physical_exit and grant == 2
        for mode, claimed in (
            ("grant", True),
            ("qualified only", legitimate),
            ("exit only", physical_exit),
            ("joint", legitimate and physical_exit),
        ):
            serves = grant == 2 and claimed
            if serves:
                findings[mode + " starts"] += 1
            if serves and boundary == 1:
                findings[mode + " overlap"] += 1
            if serves and not legitimate:
                findings[mode + " retired intent"] += 1
            if serves != should_serve:
                findings[mode + " wrong"] += 1
    assert findings["joint starts"] == 3
    assert findings["joint wrong"] == 0
    assert findings["qualified only overlap"] == 3
    assert findings["exit only retired intent"] == 7
    assert findings["forward arm 1 wrong"] == 0
    assert findings["forward arm 2 wrong"] == 9
    # At the prospective return gate, processed requests with reused
    # reservation IDs have identical wire and moderate-state effects.
    by = {r[:6]: r[6:] for r in rows}
    for renew in (0, 2):
        for boundary in (0, 1, 2):
            assert by[(renew,0,boundary,0,0,0)] == by[(renew,1,boundary,0,0,0)]
            assert by[(renew,1,boundary,0,0,0)] == by[(renew,1,boundary,0,0,1)]
        assert by[(renew,1,1,0,0,0)] == by[(renew,1,2,0,0,0)]
    print(json.dumps(dict(findings), sort_keys=True))

if __name__ == "__main__":
    main()
