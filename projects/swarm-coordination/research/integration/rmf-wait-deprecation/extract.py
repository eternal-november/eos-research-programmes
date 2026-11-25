import hashlib
from pathlib import Path
BLOBS = ['bcc8faea65f56a8f942ebadb3be048cf55d57aec','41715b45b83c1cd6a90d277b1bc885c1472533d0','574ed7f6ba1ca867382d528e6bf4c12d3a7c53f8','b860c95e0336d95fcedf8a51c15b4cc76a8eed2d','5dffdcb16fa34fa7ca672975fdf731b6d97228cc','956e618610fcdc4659486057dd75c595874010f4','a66d37d655f8da82457d59afbf75326907af0420','ca8397c74efe4b0886afb331975eab698c16cb2e']
sources=[]
for p,sha in zip([f'src{i}' for i in range(7)]+['rmf_utils/Modular.hpp'], BLOBS):
    b=Path(p).read_bytes()
    assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==sha, p
    sources.append(b.decode())

def section(s,a,b):
    return s[s.index(a):s.index(b,s.index(a))]
def function(s, a):
    i=s.index(a)
    j=s.index('\n{',i)
    end=s.index('\n}',j)+2
    return s[i:end]+'\n'
# No substitutions in selected bodies. Header below supplies types/fixtures,
# not database/physical effects. Use a stub impl_ptr factory with std::unique_ptr.
tracker=section(sources[0],'namespace rmf_traffic','} // namespace rmf_traffic')+'} // namespace rmf_traffic\n'
schema=section(sources[1],'namespace rmf_traffic','} // namespace rmf_traffic')+'} // namespace rmf_traffic\n'
viewer=section(sources[3],'namespace rmf_traffic','} // namespace rmf_traffic')+'} // namespace rmf_traffic\n'
notice=section(sources[0],'/*','\n#include')
def emit(name, content):
    Path(name).write_text(notice+'\n'+content)
emit('schema.inc',viewer+schema)
emit('tracker.inc',tracker)
emit('viewer.inc',section(sources[4],'void ItineraryViewer::DependencySubscription::Implementation::Shared::reach()', 'Dependency ItineraryViewer::DependencySubscription::dependency()')+function(sources[4],'Dependency ItineraryViewer::DependencySubscription::dependency()'))
emit('watch.inc',function(sources[5],'auto Mirror::watch_dependency('))
emit('wait.inc',function(sources[2],'void WaitForTraffic::Active::_consider_going()'))
