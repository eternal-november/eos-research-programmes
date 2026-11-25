import re, subprocess, tempfile
from hashlib import sha1
from pathlib import Path

PINS = {
"CommAdapterImpl": "8f177b9d9431199d803f6eb04b5c1a1cc5404bc0",
"EdgeMapping": "35d06a00e9f14c71eefab2ec08cce57c39884d21",
"MessageResponseMatcher": "cebb1e12a356277d9f74f8a967f0d333e691fcc0",
"NodeMapping": "f2c2baf49c7cfe3a3aa70c0ff887cf5e98c8e29c",
"OrderMapper": "56555c1ad509ab24c428ba5f95589de6772c5d9d",
}
source={}
for name,want in PINS.items():
    b=Path(name+".java").read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==want
    source[name]=b.decode()

def body(name,method):
    s=source[name]
    m=re.search(r'^  (?:public|private) [^\n]*\b'+method+r'\([^;\{]*\) \{',s,re.M)
    depth=1
    for i,x in enumerate(s[m.end():],m.end()):
        depth+=(x=="{")-(x=="}")
        if not depth: return s[m.start():i+1]
    raise ValueError(method)

# Preserve the full matcher class from its declaration and compile it against
# local data carriers. Only package, imports and surrounding stubs differ.
t=Path("PublicationHarness.java.in").read_text()
t=t.replace("/* MATCHER */","public class "+source["MessageResponseMatcher"].split("public class ",1)[1])
t=t.replace("/* SEND */","\n".join(body("CommAdapterImpl",n) for n in ("sendOrder","sendMessage")))
t=t.replace("/* EDGE */","\n".join(body("EdgeMapping",n) for n in ("toBaseEdge","toHorizonEdge")))
with tempfile.TemporaryDirectory() as root:
    p=Path(root)/"PublicationHarness.java";p.write_text(t)
    subprocess.run(["java",str(p)],check=True)
