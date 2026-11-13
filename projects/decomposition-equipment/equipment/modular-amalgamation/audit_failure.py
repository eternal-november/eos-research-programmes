import json

def table(n,side):
    elements=['e','z']+[f'x{i}' for i in range(n)]+(['p'] if side=='A' else [f's{i}' for i in range(1,n)])
    def mul(a,b):
        if a=='e': return b
        if b=='e': return a
        if 'z' in (a,b): return 'z'
        if a[0]=='x' and b[0]=='x': return 'z'
        if side=='A':
            if a==b=='p': return 'p'
            return 'x0'
        if a[0]==b[0]=='s':
            k=(int(a[1:])+int(b[1:]))%n
            return f's{k}' if k else 'e'
        return f'x{(int(a[1:])+int(b[1:]))%n}'
    return elements,mul
out=[]
for n in range(2,24):
    sides={s:table(n,s) for s in ['A','B']}
    for s,(els,mul) in sides.items():
        assert all(mul(a,b) in els for a in els for b in els)
        assert all(mul(mul(a,b),c)==mul(a,mul(b,c)) for a in els for b in els for c in els)
    K=['e','z']+[f'x{i}' for i in range(n)]
    ma,mb=sides['A'][1],sides['B'][1]
    assert all(ma(a,b)==mb(a,b) for a in K for b in K)
    for j in range(n):
        sj='e' if not j else f's{j}'
        assert ma('p',mb('x0',sj))=='x0'
        assert mb(ma('p','x0'),sj)==f'x{j}'
    out.append({'n':n,'A_size':len(sides['A'][0]),'B_size':len(sides['B'][0]),'K_size':len(K),'associative_and_shared_embedding':True,'collapse_derivation_all_j':True})
print(json.dumps(out,indent=2))
