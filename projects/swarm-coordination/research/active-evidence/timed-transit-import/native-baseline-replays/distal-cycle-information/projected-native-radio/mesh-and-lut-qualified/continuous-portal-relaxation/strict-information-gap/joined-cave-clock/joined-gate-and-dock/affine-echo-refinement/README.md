# Same-epoch rate uncertainty at the cave gate

Civilian finite clock model on the pinned PR 881 portal certificates.
Python 3 and Git suffice. The exact small inputs are in the Space bundle.

```sh
bash replay.sh up | cmp - EXPECTED.jsonl
```

Echo times and rate bounds are fixture inputs, not empirical hardware
clock accuracy or delay estimates. This PR checks the admission interface;
it does not replace the integrated worker replay.
