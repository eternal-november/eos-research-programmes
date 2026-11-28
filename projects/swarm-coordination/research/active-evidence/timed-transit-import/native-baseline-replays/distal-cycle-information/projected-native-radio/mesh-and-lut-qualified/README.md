# Distal Cave01 pose, collision and native lookup correspondence

Reconstruct `up/vis` from `SOURCE.tsv`. Under `up/geom` place the versioned
SDF and COLLADA files named by ASSETS.tsv, the matching world.sdf, and
`PINS.txt` copied from `COLLISION.sha256`. Also place the official
`cave_circuit_01.dat` at the same OSRF world revision; its exact Git
blob is checked by `replay.sh`. The complete Space archive already
has these inputs. Python 3 with NumPy, Git and C++17 are required.

```sh
bash replay.sh up | cmp - EXPECTED.txt
```

This is a local pose and radio certificate in the tested partial scene,
not a physically traveled trajectory or certified full cave map.
