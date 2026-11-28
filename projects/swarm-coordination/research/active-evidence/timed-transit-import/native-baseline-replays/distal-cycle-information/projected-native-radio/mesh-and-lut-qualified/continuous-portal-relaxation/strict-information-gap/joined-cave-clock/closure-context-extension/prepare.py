from pathlib import Path
p=Path('mission.cpp')
s=p.read_text()
def swap(a,b):
    global s
    assert s.count(a)==1
    s=s.replace(a,b)
swap('Radio(const Scene& s,unsigned cap):s(s),w(cap)',
     'Radio(const Scene& s,unsigned cap,bool staged=true):s(s),w(cap)')
swap('   for(size_t i:{3,4,5})','   if(staged){\n   for(size_t i:{3,4,5})')
swap('   assert(m.rebuilds==1);','   assert(m.rebuilds==1);\n   }')
p.write_text(s[:s.index('int main(int argc,char** argv)')])
