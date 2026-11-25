"""Extract only the three named NIST function bodies, requiring the exact blob."""
import hashlib
import pathlib
import sys
p=pathlib.Path(sys.argv[1]).read_bytes()
assert hashlib.sha1(f'blob {len(p)}\0'.encode()+p).hexdigest()=='4b6bc2cea406d4813145d9f565318a4ebe345be8'
s=p.decode()
for name in ('HandleFaultyParts','CheckQuadrantQuality','PerformQualityCheck'):
    i=s.index('TaskManagerPluginPrivate::'+name+'(')
    a=s.rfind('\n',0,i)+1
    b=s.index('\n    }',i)+len('\n    }')
    print(s[a:b])
