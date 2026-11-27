"""Replace the old harness's fixed sentinel; not the pinned radio body."""
from pathlib import Path
p=Path("replay.cpp")
s=p.read_text(); old="int demo_draw(){return 500;}"
assert s.count(old)==1
p.write_text(s.replace(old, """std::vector<int> controlled;
size_t draws_consumed=0;
void reset_draws(std::vector<int> marks){controlled=marks;draws_consumed=0;}
int demo_draw(){return controlled.at(draws_consumed++);}"""))
