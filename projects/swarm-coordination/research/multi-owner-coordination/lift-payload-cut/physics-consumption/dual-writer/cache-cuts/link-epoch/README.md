# Scoped link replacement and outstanding velocity effects

See [Link_Rebind.tex](Link_Rebind.tex). This development study runs extracted,
pinned Gazebo link, velocity-control, and linear physics-dispatch source in a
serial fixture. Changing the entity behind a configured link name does not
change the cached map size. The stock publisher can keep addressing the old
entity. Retargeting only the identifier may carry old motion to the successor;
a source-buffer reset alone may leave a component already staged on the old
entity. The proposed selective, phase-scoped guard is authored, not stock.

Stage the exact blobs in INPUTS.tsv as a sibling pins directory. Run
python3 -B probe.py ../pins and compare stdout with results.txt. Inputs are
immutable source bytes; a source-complete project backup includes the replay.

[World-reset identity](reset-id/README.md) tests when a native entity number
can recur; non-reusable appointment identity cannot rely on that number alone.
