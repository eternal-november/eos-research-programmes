"""Pure deterministic row recipes; traces include all evaluated reads."""
from collections import defaultdict

def evaluate(e, cells):
    op,*a=e
    if op=='constant':
        return a[0],frozenset()
    if op=='read':
        return cells[a[0]],frozenset({a[0]})
    if op=='if':
        b,r=evaluate(a[0],cells)
        assert type(b) is bool
        x,s=evaluate(a[1 if b else 2],cells)
        return x,r|s
    if op=='equal':
        u,r=evaluate(a[0],cells); v,s=evaluate(a[1],cells)
        assert type(u) is type(v)
        return (u==v),r|s
    if op=='pair':
        u,r=evaluate(a[0],cells); v,s=evaluate(a[1],cells)
        return (u,v),r|s
    raise ValueError(f'Uncertified operation {op}')

class Producer:
    def __init__(self,recipes,cells):
        self.recipes=dict(recipes)
        self.cells=dict(cells)
        self.memo={}
        self.consumers=defaultdict(set)
        for name,code in self.recipes.items():
            self._set(name,evaluate(code,self.cells))

    def _set(self,name,new):
        if name in self.memo:
            for ref in self.memo[name][1]:
                self.consumers[ref].discard(name)
        self.memo[name]=new
        for ref in new[1]:
            self.consumers[ref].add(name)

    def update(self,cell_delta,code_delta):
        assert cell_delta.keys()<=self.cells.keys()
        assert code_delta.keys()<=self.recipes.keys()
        dirty=set(code_delta)
        for k,v in cell_delta.items():
            if self.cells[k]!=v:
                dirty.update(self.consumers[k])
        self.cells.update(cell_delta)
        self.recipes.update(code_delta)
        result={}
        for named in sorted(dirty):
            new=evaluate(self.recipes[named],self.cells)
            if new[0]!=self.memo[named][0]:
                result[named]=new[0]
            self._set(named,new)
        return result, dirty
