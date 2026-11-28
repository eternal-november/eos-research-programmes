# Time-aligned aperture capacity from Open-RMF target recurrences

Populate `up/` with the pinned `SOURCE.tsv` blobs or use the Space archive. Requires Python 3, Git and C++20; Lean 4 for the proof file.

```sh
bash replay.sh up | cmp - EXPECTED.json
lean Aperture.lean
```

The selected native functions compute target velocities on two independent controls. The plant, common aperture geometry, authorized pulse options and update law are stated simulation assumptions, not stock hardware behavior. Report-only, individual-alone, separate-peak and common-time guarantees are different.
