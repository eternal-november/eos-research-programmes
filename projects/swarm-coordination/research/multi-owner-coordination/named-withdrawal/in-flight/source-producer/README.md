# Ordered native scope producer

A concrete source gate derives predecessor scope from its accepted
suffix and holds the acquired resources across actual changes.
Physical unload and carrier clearance are different events.

[Assumptions, proof and comparator](Ordered_Scope_Producer.tex).
Use the named-withdrawal and in-flight studies at the pinned main
revision 3ed19fb47ffa4cd795e40a7dca67d6f6f6bb4160, along with
the upstream native inputs they declare. Python 3 and NumPy:

    python3 -B native.py /path/to/upstream /path/to/named-withdrawal /path/to/in-flight | cmp expected.json -

The native dependency's hash is checked at load. The three abstract
statements in Fence.lean were checked with AXLE Lean 4.35.0.
