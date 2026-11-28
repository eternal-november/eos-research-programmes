from pathlib import Path
def extract(s, marker):
    at=s.index(marker);start=s.index("{",at);depth=0
    for i in range(start,len(s)):
        if s[i]=="{":depth+=1
        elif s[i]=="}":
            depth-=1
            if depth==0:return s[at:i+1]+"\n"
    raise ValueError(marker)
h=Path("helpers.cpp").read_text(); c=Path("range.cpp").read_text()
head=lambda s:s[:s.index("///")]
parts=[head(h),"namespace internal {\n",extract(h,"void check_and_swap_limits("),"}\n"]
for k in ("void update_prev_command(","bool is_limited(","VelocityLimits compute_velocity_limits("): parts.append(extract(h,k))
parts += [head(c),extract(c,"template <>\nbool JointSaturationLimiter<JointControlInterfacesData>::on_enforce(")]
Path("slice.inc").write_text("".join(parts))
