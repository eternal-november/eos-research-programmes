# Gate rays and a native pre-departure receipt

Requires the exact same `up/` as the mesh/LUT-qualified archive (#872).
Run `bash replay.sh /path/to/qualified/up | cmp - EXPECTED.txt`.
Python 3 with NumPy, Git and C++17 are needed.

The authored ray geometry supplies the tested local gate result. Byte
delivery and debits are native; sensor optics, world timing, and travel
remain simulation assumptions.
