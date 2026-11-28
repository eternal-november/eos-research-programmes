from itertools import product
T,H=3,3
cdf=list(product(range(T),repeat=H))
stats=[0,0,0,0]
for obs in range(1<<(T*H)):
    views=[(obs>>(T*i))&7 for i in range(H)]
    same=[[sum(1<<j for j,v in enumerate(views) if (v^views[i])&((2<<t)-1)==0)
           for t in range(T)] for i in range(H)]
    possible=[]
    for act in cdf:
        if all(all(act[j]==act[i] for j in range(H) if same[i][act[i]]>>j&1) for i in range(H)):
            possible.append((act,sum(1<<(act[i]*H+i) for i in range(H))))
    for mask in range(1<<(T*H)):
        allow=[(mask>>(t*H))&7 for t in range(T)]
        first=[next((t for t in range(T) if same[i][t]&allow[t]==same[i][t]),None)
               for i in range(H)]
        acts=[act for act,m in possible if mask&m==m]
        assert (None not in first)==bool(acts)
        if acts:
            assert tuple(first) in acts
            assert all(all(f<=a for f,a in zip(first,act)) for act in acts)
        stats[0]+=1
        stats[1]+=bool(acts)
        stats[2]+=not acts and all(any(u>>i&1 for u in allow) for i in range(H))
        stats[3]+=bool(acts) and not any(u==7 for u in allow)
print(f'{stats[0]} finite timing families; {stats[1]} causal wins; '
      f'{stats[2]} per-history-only wins; {stats[3]} causal wins without a fixed cut')
