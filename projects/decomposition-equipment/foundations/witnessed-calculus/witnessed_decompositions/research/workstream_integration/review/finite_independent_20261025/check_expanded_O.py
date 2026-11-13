from pathlib import Path
import json,hashlib,time
import check_x_label_mins as X
import check_noimport as I
P=Path(__file__).parent
start=time.monotonic()
for name,M in I.TABLES.items():
    for rule,l,r in X.pairs(M):
        sibling=I.val(0,I.leaf((),(),(l.arrow[0],l.arrow[0],0)));host=I.cut(sibling,l,l.edges)
        a=I.rewrite(host,(0,),'D0',M);ab=I.rewrite(a,(1,),rule,M)
        b=I.rewrite(host,(1,),rule,M);ba=I.rewrite(b,(0,),'D0',M);assert ab==ba
        I.square(host,(I.eq(a,(0,),'D0',M),I.eq(ab,(1,),rule,M)),(I.eq(b,(1,),rule,M),I.eq(ba,(0,),'D0',M)),M,'expanded_disjoint')
        for i,(addr,x) in enumerate(I.occurrences(l)):
            F=tuple(I.val(0,q) if j==i else q for j,(z,q) in enumerate(I.occurrences(l)));host=I.graft(l,F)
            a=I.rewrite(host,addr,'D0',M);ab=I.rewrite(a,(),rule,M)
            b=I.rewrite(host,(),rule,M);addr2=I.occurrences(r)[i][0];ba=I.rewrite(b,addr2,'D0',M);assert ab==ba
            I.square(host,(I.eq(a,addr,'D0',M),I.eq(ab,(),rule,M)),(I.eq(b,(),rule,M),I.eq(ba,addr2,'D0',M)),M,'expanded_variable')
r={'status':'PASS','counts':dict(I.COUNT),'elapsed_seconds':time.monotonic()-start,'domain_sha256':hashlib.sha256((P/'REVIEW_ADDENDUM_DOMAIN.md').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'dependencies':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (P/'check_x_label_mins.py',P/'check_noimport.py')}}
(P/'ExpandedOCertificate.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
