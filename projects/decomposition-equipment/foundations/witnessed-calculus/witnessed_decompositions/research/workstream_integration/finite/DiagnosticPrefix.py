"""Parent-authorized bounded timing diagnostic; NOT mathematical C evidence."""
from model import *
from itertools import islice
from pathlib import Path
import time,resource,json,hashlib
G=Graph(6,((0,5),(1,2),(2,3),(3,4)))
w=Flat(G,Arrow(0,2),((0,),(1,2),(3,4),(5,)),(Arrow(0,1),Arrow(1,1),Arrow(1,1),Arrow(1,2)),0)
i,j=0,2;source_profile=w.profile;mid=compose(w.arrows[i:j],w.arrows[i].a)
op=source_profile[:i]+((None,mid),)+source_profile[j:]
# Exactly100 K graphs of size6, the overwhelmingly dominant rejected block.
Ks=tuple(islice(graphs(6),1100,1200));assert len(Ks)==100 and all(K.n==6 for K in Ks)
start=time.monotonic();cpu=time.process_time();checks=matches=0
for K in Ks:
    expected=op[:i]+((K,mid),)+op[i+1:]
    for ob in partitions(w.graph.n,len(expected)):
        outer=Flat(w.graph,w.whole,ob,w.arrows[:i]+(mid,)+w.arrows[j:],0)
        checks+=1
        if outer.profile==expected:matches+=1
wall=time.monotonic()-start;ct=time.process_time()-cpu
r={'kind':'BOUNDED_TIMING_DIAGNOSTIC_NOT_C_CERTIFICATE','candidate_graphs':len(Ks),'outer_profile_checks':checks,'matches':matches,'wall_seconds':wall,'process_cpu_seconds':ct,'cpu_over_wall':ct/wall,'checks_per_wall_second':checks/wall,'current_mib_maxrss':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024,'domain_source_unchanged':hashlib.sha256(Path(__file__).with_name('DOMAIN.md').read_bytes()).hexdigest(),'model_source_unchanged':hashlib.sha256(Path(__file__).with_name('model.py').read_bytes()).hexdigest(),'extrapolation_check_count':33868*(3*729+2*64),'estimated_seconds_for_five_six_vertex_intervals_at_sample_rate':33868*(3*729+2*64)/(checks/wall),'limits':'Sample rate under current load; no inference of actual progress/remaining K index; no candidate graph omitted from released full runs.'}
Path(__file__).with_name('DiagnosticPrefix.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
