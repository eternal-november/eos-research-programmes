"""Independent direct search for the minimum legal replay prefix."""
from itertools import product

def advance(values,j):
    values[j]=values[j-1]

def solve(m,passed,available):
    count=0
    for k in range(m+1):
        possible=False
        for order in product(available,repeat=k):
            count+=1
            v=[1]+[0]*m
            for i in order:advance(v,i)
            for i in range(passed+1,m+1):advance(v,i)
            if v[m]==1:
                possible=True
                break
        if possible:return k,count
    return None,count

def main():
    checks=visited=0
    for m in range(1,6):
        for passed in range(m+1):
            for mask in range(1<<m):
                avail=tuple(j for j in range(1,m+1) if mask&(1<<(j-1)))
                expected=passed if all(j in avail for j in range(1,passed+1)) else None
                answer,count=solve(m,passed,avail)
                assert answer==expected,(m,passed,avail,expected,answer)
                checks+=1;visited+=count
    return checks,visited
if __name__=='__main__':print(*main())
