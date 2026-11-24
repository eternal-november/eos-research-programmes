from functools import cache
# Units are half metres and half ticks at speed one. Outer anchors 0,20.
# Right follows its shortest safe motion to 13 (stop=8) or 14 (stop=12).
# Only evidence at the left is a reliable receipt from radio contact,
# scheduled when the physical gap first falls within 7, then delivered
# after delay half-ticks. Silence before that cut is not unique evidence.
def exact(deadline,delay):
    @cache
    def visit(t,x,worlds):
        groups={}
        for f,arrival in worlds:
            y=max(16-t,max(f+2,13))
            if arrival<0 and y-x<=7:arrival=t+delay
            sofar=(0<=arrival<=t)
            groups.setdefault(sofar,[]).append((f,arrival))
        for ws in groups.values():
            if t==deadline:
                if not all(max(16-t,max(f+2,13))-x<=7 for f,_ in ws):return False
            elif not any(2<=nx<=7 and all(nx<=f-2 for f,_ in ws)
                         and visit(t+1,nx,tuple(ws)) for nx in (x-1,x,x+1)):
                return False
        return True
    return visit(0,4,((8,-1),(12,-1)))

n=0
for delay in range(9):
    for deadline in range(15):
        assert exact(deadline,delay)==(deadline>=4+delay),(deadline,delay)
        n+=1
print(n,"timed contact-policy checks match lower bound and construction")
print("minimum half-ticks for delays 0..8:",[next(t for t in range(15) if exact(t,d)) for d in range(9)])
