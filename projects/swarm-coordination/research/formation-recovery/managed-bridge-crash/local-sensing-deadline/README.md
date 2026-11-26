# When passive sensing comes too late to reconnect

[Proof and source bounds](Local_Sensing_Deadline.tex). Two authored
extensions of the same published planar cut both have bounded recovery
motions that meet the deadline. Even ideal passive range sensing cannot
reveal the hidden direction in time to guarantee both outcomes. The
upper/lower comparison does not assume a blackout after contact.

Fetch the pinned source in `UPSTREAM.txt` and verify `PINNED.tsv`.
Use Python 3.10+, NumPy and SciPy:

    set -o pipefail
    sh replay.sh /path/to/pinned-source-root | cmp expected.json -

The cut perturbations, observation regime, and alternate evidence path
are modeled. `Disk_Midpoint.lean` checks the enclosure arithmetic.
No independent mission or physical sensing claim.
