import hashlib,sys
from pathlib import Path
ranges=[
 ('MSDriveWay.cpp',279,368,'5016aff676c96126a37e80814b8d337fa7648277'),
 ('MSDriveWay.cpp',385,408,'5016aff676c96126a37e80814b8d337fa7648277'),
 ('MSRailSignal.cpp',615,654,'d9afd7c0b0837b18766bea7d635586b3f33d43f4'),
 ('MSLink.cpp',2330,2355,'7bb461955b8d5441b757aa94b7e92a06621d9206')]
parts=[]
for name,a,b,oid in ranges:
    data=(Path(sys.argv[1])/name).read_bytes()
    assert hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()==oid,name
    parts.append('\n'.join(data.decode().split('\n')[a-1:b])+'\n')
Path(sys.argv[2]).write_text('\n'.join(parts))
