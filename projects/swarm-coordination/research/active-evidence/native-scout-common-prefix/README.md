# Scouting that frees a common prefix

A native scouting move makes the actual local occupancy crop informative. It also frees a cell the other crew can reach before receiving the cue. With that common prefix open, a cue one tick later still works; with it closed, it does not.

- [Scope, proof and transport limits](Scout_Prefix_Cut.tex)
- 96 native selected simulator traces, plus exhaustive finite prefix/suffix checks.
- Materialize exact `SOURCE.tsv` paths under INPUT. Run `sh replay.sh INPUT > actual.json`, then `cmp expected.json actual.json`. Requires C++17, Python 3 and NumPy, and Git.

An authored joint development trial, not a field sensor result or independent mission. The occupation view is an actual selected simulator crop, and a hypothetical earlier hint or paid-but-erased radio attempt does not count as a usable observation.
