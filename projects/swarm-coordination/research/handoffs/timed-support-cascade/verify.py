"""Reconstruct bulky derived outputs in a temporary copy and check their hashes."""
from pathlib import Path
from tempfile import TemporaryDirectory
from shutil import copytree
from subprocess import check_call
import sys

root = Path(__file__).resolve().parent
with TemporaryDirectory() as tmp:
    tmp = Path(tmp)
    for name in ('primary','interface','transfer'):
        d = 'swarm-c11-' + name
        copytree(root / d, tmp / d)
    commands = (
        ('primary', 'replay.py', (), 'results.json'),
        ('interface', 'interface.py', (), 'checks.json'),
        ('transfer', 'transfer.py', ('--export',), 'results.json'),
    )
    for name, script, args, output in commands:
        directory = tmp / ('swarm-c11-' + name)
        # Retain the shipped summary for compare if present; manifests also
        # authenticate the detailed outputs that only exist after replay.
        out = directory / output
        before = out.read_bytes() if out.exists() else None
        with out.open('wb') as result:
            check_call([sys.executable, '-B', script, *args], cwd=directory, stdout=result)
        if before is not None and before != out.read_bytes():
            raise RuntimeError(f'{name}: replay summary changed')
        check_call(['sha256sum', '-c', 'SHA256SUMS'], cwd=directory)
