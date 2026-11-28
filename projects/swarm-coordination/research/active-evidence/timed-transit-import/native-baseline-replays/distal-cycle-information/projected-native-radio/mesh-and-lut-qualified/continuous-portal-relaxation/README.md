# Cave01 portal contact and flight evidence

Use the `up/` inputs of the preceding **actual LUT and collision** archive. This
addendum intentionally does not duplicate the unchanged 8 MiB input package.
ASSETS.tsv and COLLISION.sha256 retain the exact model provenance. The
first line verifies conservative voxel contacts and distance bounds;
the second gives the checked positive routes from heuristic discovery.

```sh
bash replay.sh /path/to/qualified/up | cmp - EXPECTED.jsonl
```

Requires Python 3 with NumPy and Git. No physical lower bound outside the
declared center authorization domain is implied.
