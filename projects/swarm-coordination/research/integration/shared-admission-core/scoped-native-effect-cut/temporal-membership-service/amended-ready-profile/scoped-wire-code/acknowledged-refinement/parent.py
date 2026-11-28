from pathlib import Path

p = Path("selector.cpp").read_text()
assert p.count("int main(){") == 1
Path("parent.inc").write_text(p.replace("int main(){", "int reference_fixture_suite(){"))
