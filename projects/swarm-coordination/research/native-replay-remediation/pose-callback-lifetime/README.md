# Restore the stable native pose callback after temporary remediation

This small overlay applies only to the original replay archives for
PRs 898, 899, 900, 902 and 904. Each row pins original PR/path,
old and replacement source digests, and the unchanged exact expected
transcript digest. Use an unpacked copy of the original archive.

```sh
python3 apply.py 904 /path/to/unpacked/exact-904
cd /path/to/unpacked/exact-904
sha256sum -c MANIFEST.sha256
bash replay.sh /path/to/pinned/up parent | cmp - EXPECTED.jsonl
```

Not a model or physical change. Use these corrected C++ sources when
relying on the affected replay results.

For PR 904, leave an untouched unpacked original as well as the
corrected copy and run `bash sanitizer.sh ORIGINAL CORRECTED UP` with
a compiler supporting AddressSanitizer. It checks one matched case.
