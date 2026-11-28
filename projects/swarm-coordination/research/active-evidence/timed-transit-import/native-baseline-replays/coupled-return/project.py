from pathlib import Path
import re,heapq
from collections import deque
from xml.etree.ElementTree import parse
def data(path):
    edge=[tuple(map(int,m)) for m in re.findall(r'(\d+)\s*--\s*(\d+)\s*\[label=(\d+)\]',
           (path/'world.dot').read_text())]
    pose={}
    for x in parse(path/'world.sdf').findall('.//include'):
      title=x.findtext('name','')
      if re.fullmatch(r'tile_\d+',title) or title=='staging_area':
        pose[0 if title=='staging_area' else int(title[5:])]=tuple(map(float,x.findtext('pose').split()[:3]))
    assert len(pose)==158
    adj={v:[] for v in pose}
    for a,b,w in edge:
        adj[a].append((b,w));adj[b].append((a,w))
    def shortest(start,w=True):
      d={start:0};pq=[(0,start)]
      while pq:
        c,u=heapq.heappop(pq)
        if c!=d[u]:continue
        for v,k in adj[u]:
          c1=c+(k if w else 1)
          if c1<d.get(v,10**9):
            d[v]=c1;heapq.heappush(pq,(c1,v))
      return d
    return pose,adj,shortest
def project(path):
    pose,adj,shortest=data(path)
    # B starts at 16. The longest modeled finish horizon is 13.
    ids=sorted({u for u,t in shortest(16,False).items() if t<=13}|{18,39,13,42})
    coord=[tuple(int(x) for x in pose[u]) for u in ids]
    assert len(set(coord))==len(ids)
    d={u:shortest(u) for u in ids}
    lines=[f'{len(ids)} {len(ids)}']+[' '.join(map(str,(u,*pose[u]))) for u in ids]
    lines+=[' '.join(map(str,ids))]
    lines+=[' '.join(str(d[u][v]) for v in ids) for u in ids]
    (path/'all-sampled.tsv').write_text('\n'.join(lines)+'\n')
    return ids

if __name__=='__main__':
    import sys
    project(Path(sys.argv[1]))
