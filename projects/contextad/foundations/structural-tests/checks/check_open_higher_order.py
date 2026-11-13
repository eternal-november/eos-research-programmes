"""Regression witnesses, NOT an exhaustive check over all client contexts."""
def require(condition):
    if not condition: raise RuntimeError("regression check failed")

class A:
    def __init__(self, late=False): self.store=[]; self.events=[]; self.late=late
    def new(self):
        h=[True, len(self.store)]; self.store.append(h); self.events.append(('new',h[1])); return h
    def same(self,h,g): return h is g
    def label(self,h): return h[1]
    def run(self,h,k):
        self.events.append(('call',self.label(h)))
        if not h[0]: self.events.append(('spent',self.label(h))); return False
        if not self.late: h[0]=False
        self.events.append(('enter',self.label(h))); k()
        self.events.append(('leave',self.label(h))); h[0]=False
        self.events.append(('done',self.label(h))); return True
class B:
    def __init__(self): self.store={}; self.events=[]
    def new(self):
        # Different concrete name supply; traces expose only consistent canonical names.
        h=7+13*len(self.store); self.store[h]=True; self.events.append(('new',self.label(h))); return h
    def same(self,h,g): return h==g
    def label(self,h): return (h-7)//13
    def run(self,h,k):
        self.events.append(('call',self.label(h)))
        if not self.store[h]: self.events.append(('spent',self.label(h))); return False
        self.store[h]=False; self.events.append(('enter',self.label(h))); k()
        self.events.append(('leave',self.label(h))); self.events.append(('done',self.label(h))); return True

def client(lib, depth, allocate):
    h=lib.new(); aliases=[h,h]; callbacks=[]
    def inner(d):
        if allocate:
            g=lib.new()
            require(not lib.same(h,g))
            lib.run(g,lambda:inner(d-1) if d else lib.events.append(('emit',False)))
        require(lib.same(aliases[0],aliases[1]))
        if d:
            callbacks.append(lambda: inner(d-1))
            lib.run(aliases[d%2],callbacks[-1])
        else: lib.events.append(('emit',True))
    lib.run(h,lambda:inner(depth))
    lib.run(h,lambda:lib.events.append(('impossible',)))
    return lib.events

count=0
for d in range(100):
    for allocate in (False,True):
        a,b=A(),B(); ta,tb=client(a,d,allocate),client(b,d,allocate)
        require(ta==tb)
        require(all(sum(e==('enter',h) for e in ta)<=1 for h in range(len(a.store))))
        count+=1
for d in range(1,100):
    good,bad=A(),A(late=True)
    tg,tl=client(good,d,False),client(bad,d,False)
    require(('emit',True) not in tg and ('emit',True) in tl)
    require(sum(e==('enter',0) for e in tl)==d+1)
print(f'{count} A/B client trace comparisons passed; 99 late-consumption distinguishing families passed.')
print('These are executable sanity witnesses; the all-context/all-prefix claim rests on the operational proof, not bounded enumeration.')
