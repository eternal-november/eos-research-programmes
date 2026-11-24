from fractions import Fraction as F
g=F(1); r=F(7,2); T=F(2)
x0=F(2); y0=F(8); L=F(10)

def left_limit(f): return min(f-g,r,x0+T)
def right_limit(f): return max(f+g,L-r,y0-T)
low,high=F(4),F(6)
for f in (low,high):
    x,y=left_limit(f),right_limit(f)
    assert abs(x-x0)<=T and abs(y-y0)<=T
    assert x<=f-g and y>=f+g
    assert all(g<=b-a<=r for a,b in [(0,x),(x,y),(y,L)])
    print("known stop",f,"supports terminal pair",x,y)
robust_left=min(map(left_limit,(low,high)))
assert right_limit(high)-robust_left>r
print("hidden stop: safe common leftmost-side choice is at most",robust_left,
      "but high-world right side is at least",right_limit(high),
      "requiring gap",right_limit(high)-robust_left,">",r)
