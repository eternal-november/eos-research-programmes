# MRWS movement fidelity

[Study and checked scope](MRWS_Movement_Fidelity_Audit.tex). Use the pinned MRWS checkout from the prior development campaign with `PYTHONHASHSEED=0` and its native `simu` on `PYTHONPATH`. Supply the sibling guarded-replan and native-calibration modules on the Python import path, or use the standalone Space archive.

```sh
PYTHONHASHSEED=0 PYTHONPATH=/path/to/MRWS/simu:/path/to/mrws-guarded-replan:/path/to/mrws-native-calibration python3 -B audit.py /path/to/MRWS/simu/data/whouse7x11.txt results.json | diff -u audit.txt -
sha256sum results.json
```
