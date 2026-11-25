"""Independent serial state graph compared with the one-pass frontier law."""
from itertools import product
from functools import lru_cache

def search(held,empty,n):
    @lru_cache(None)
    def visit(i,stock,pool):
        if i==n:return True
        if stock[i]>=0:
            r=stock[i]
            return visit(i+1,stock[:i]+(-1,)+stock[i+1:],tuple(sorted((*pool,r))))
        for r in pool:
            # A visit picks with r, accepts the whole current segment, and
            # then returns r to the available set. No unconstrained prefetch.
            if visit(i+1,stock,pool):return True
        return False
    return visit(0,held,empty)

def main():
    tested=0
    for n in range(9):
        for flags in product((0,1),repeat=n):
            held=tuple(i if k else -1 for i,k in enumerate(flags))
            for e in (0,1,2):
                empty=tuple(range(n,n+e))
                assert search(held,empty,n)==(not flags or flags[0] or bool(empty))
                tested+=1
    print('finite independent graph checks',tested)
if __name__=='__main__':main()
