# Upgrading the exact motion audit

[Upgrade.tex](Upgrade.tex) proves the fixed-width supplement for later
singleton queries and the exact capacity trade-off if the original code
can be redesigned. With 100 rounds and all width-five queries, the existing
54-bit export can need 98 extra bits. An initially redesigned 54-bit code
can reduce that to 53 only when it is permitted to convey additional
history distinctions before the audit changes.

Run python3 -B upgrade.py and compare stdout with results.json. This is a
standalone standard-library exact replay using the source family established
in the parent study. The receiver must not confuse exact qualified history
with equal endpoint or reusable simulator identity.
