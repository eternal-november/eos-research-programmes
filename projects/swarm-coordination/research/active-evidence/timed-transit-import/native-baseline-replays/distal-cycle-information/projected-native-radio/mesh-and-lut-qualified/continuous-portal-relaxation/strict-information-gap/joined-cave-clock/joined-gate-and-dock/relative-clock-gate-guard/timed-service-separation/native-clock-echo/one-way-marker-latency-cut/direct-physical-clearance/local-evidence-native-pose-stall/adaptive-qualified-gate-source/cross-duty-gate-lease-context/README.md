# Shared actuator occupancy is not an owner-local fact

Small executable continuation of the context/content gate kernel.
Two semantically distinct commands share one modeled actuator slot.
Use Python 3 and SQLite.

```sh
python3 -B verify.py | cmp - EXPECTED.json
```

This is a direct native SQLite test, not the distributed cave radio
replay, a real gate, or a concession that physical closure demands
must always be modeled as exclusive.
