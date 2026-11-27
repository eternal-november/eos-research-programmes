# Egress fixture and backup upload (I2 development)

[Technical note](Hold_Before_Upload.tex). Already viewed source layout; no
independent benchmark or implementation freeze. This replay checks the
exact cost of uncertain timed backup uploads after releasing a real
modeled physical dependency. Allocation and sensing are fixture assumptions.

```sh
python3 -B replay.py ../development-topology.json | cmp expected.json -
```

An archive of this study instead contains `topo.json` pinned in `SOURCE.tsv`.
The equally informed timed return/data-mule policy game ties. The physical
hold, copied report, transport attempt and final acknowledgment are not
interchangeable states.
