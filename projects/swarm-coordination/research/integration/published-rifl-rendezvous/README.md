# RIFL retry rendezvous and acknowledgement lanes

Source: `PlatformLab/RAMCloud`, commit `b1866af19124325a6dfd8cbc267e2e3ef1f965d1`, files under `src/` named in SOURCE.tsv. Reconstruct them under `source/` or use the complete archive. Use a C++17 compiler and Python 3.

```sh
bash client.sh | cmp - CLIENT.txt
bash server.sh | cmp - SERVER.txt
```

The fixtures do not run the complete RAMCloud system. Their role is to check which parts of scoped progress an established mechanism already supplies.
