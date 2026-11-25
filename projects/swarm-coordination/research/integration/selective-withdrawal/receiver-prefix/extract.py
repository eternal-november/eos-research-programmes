from pathlib import Path
from hashlib import sha1

for line in Path("SOURCE.tsv").read_text().splitlines()[1:]:
    name,_,pin=line.split("\t")
    b=Path(name).read_bytes()
    assert sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()==pin

def body(src, marker):
    i=src.index(marker)
    j=src.index("\n}",i)+2
    return src[i:j]+"\n"

v=Path("validator.upstream").read_text()
a=Path("acceptance.upstream").read_text()
s=Path("stitcher.upstream").read_text()
Path("release_validate.inc").write_text(body(v,"  const types::State current_state = "))
Path("release_apply.inc").write_text(body(a,"void apply_order_update"))
Path("release_master.inc").write_text(body(s,"std::optional<uint32_t> last_released_seq")+"\n"+
                                      body(s,"StitchResult OrderStitcher::decide"))
