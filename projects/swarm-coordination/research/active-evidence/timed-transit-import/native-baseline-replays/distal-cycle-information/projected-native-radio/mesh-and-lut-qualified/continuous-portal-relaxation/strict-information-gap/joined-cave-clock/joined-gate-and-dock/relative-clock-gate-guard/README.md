# Relative gate-clock knowledge on the joined mission

Use the pinned official cave assets under `up` (Space 666) and the
included exact `parent` source inputs. Python 3 with NumPy and NetworkX,
C++17, SQLite and Git required.

```sh
bash replay.sh up parent | cmp - EXPECTED.jsonl
```

Clock echoes and offset law are modeled independently of the native
radio receiver. They are not measurements of hardware timing. The
durable simulated gate and native radio/dock replay are held-in, not
independent mission acceptance.
