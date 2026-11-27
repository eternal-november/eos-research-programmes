"""Execute selected Gazebo bodies with an authored pitch-only rotation stand-in."""
from pathlib import Path
import subprocess,sys,tempfile
here=Path(__file__).resolve().parent
up=Path(sys.argv[1]).resolve()
s=(up/'cache.inc').read_text()
assert s.count('\nint main(){')==1
fixture=s.split('\nint main(){')[0]+'\n'+(here/'cases.inc').read_text()
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    (d/'cache.inc').write_text(fixture)
    (d/'replay.py').write_bytes((up/'cache.py').read_bytes())
    base=d/'base';base.mkdir()
    parent=up/'base'
    source=(parent/'fixture.inc').read_text()
    key='  bool quarter=false;\n  Vector3d operator*(Vector3d v)const{return quarter?Vector3d{v.z,v.y,-v.x}:v;}'
    assert source.count(key)==1
    source=source.replace(key,'''  double pitch=0;
  Vector3d operator*(Vector3d v)const{
    return {v.x*std::cos(pitch)+v.z*std::sin(pitch),v.y,
            v.z*std::cos(pitch)-v.x*std::sin(pitch)};
  }''')
    (base/'fixture.inc').write_text('#include <cmath>\n'+source)
    (base/'replay.py').write_bytes((parent/'replay.py').read_bytes())
    child=base/'dual-writer';child.mkdir()
    (child/'replay.py').write_bytes((parent/'dual-writer'/'replay.py').read_bytes())
    subprocess.run([sys.executable,'-B',d/'replay.py',up,base],check=True)
