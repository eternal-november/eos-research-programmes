# RIFL recovery ordering and named negative evidence

Pin the files in SOURCE.tsv under `source/` from `PlatformLab/RAMCloud` commit `b1866af19124325a6dfd8cbc267e2e3ef1f965d1`, paths `src/<filename>`, or use the complete archive.

```sh
bash server.sh | cmp - SERVER.txt
python3 -B check.py | cmp - EXPECTED.json
```

The method extraction is exact. The context is a serial harness, not the full RAMCloud service or a supported early request execution path. The separate exact finite check concerns closed-copy sets, not live replication.
