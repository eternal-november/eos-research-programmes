"""Selected unchanged COPS flow model with a fixture graph and HiGHS backend."""
from types import ModuleType
from pathlib import Path
from hashlib import sha1
import sys
import numpy as np
import scipy.sparse as sp
from scipy.optimize import milp, Bounds, LinearConstraint

def unavailable(*args,**kwargs):
    raise RuntimeError('out-of-scope COPS operation in fixture adapter')

def initialize(root):
    root=Path(root)
    for file,expected in (line.split('\t') for line in
            Path(__file__).with_name('SOURCE.tsv').read_text().splitlines()):
        raw=(root/file).read_bytes()
        actual=sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()
        assert actual==expected,(file,actual)
    sys.path.insert(0,str(root))
    # Only the following unused imports would otherwise require the packages
    # below. Fail loudly on use; no fake implementation of a selected method.
    for name,attrs in (
            ('networkx',{'diameter':unavailable}),
            ('colorama',{'Fore':None,'Style':None}),
            ('cops.graph',{'Graph':unavailable}),
            ('cops.constr_cluster',{'constraint_static_master':unavailable})):
        mod=ModuleType(name)
        mod.__dict__.update(attrs)
        sys.modules[name]=mod
    from cops import optimization_wrappers as optimizer
    import cops.problem as original
    # Retain native input defaults, indexer, objective, model generation and
    # decoder. Replace only numerical backend used by the stock wrapper.
    optimizer._solve_gurobi=highs
    return original.ConnectivityProblem, optimizer.Constraint

def highs(c,ai,bi,ae,be,jint,jbin,output):
    c=np.asarray(c,float)
    n=len(c)
    lo=np.zeros(n)
    hi=np.full(n,np.inf)
    hi[jbin]=1
    kinds=np.zeros(n,np.uint8)
    kinds[jint]=kinds[jbin]=1
    constraints=[]
    if ai.shape[0]:
        constraints.append(LinearConstraint(ai.tocsc(),-np.inf,np.asarray(bi,float)))
    if ae.shape[0]:
        constraints.append(LinearConstraint(ae.tocsc(),np.asarray(be,float),np.asarray(be,float)))
    result=milp(c,integrality=kinds,bounds=Bounds(lo,hi),constraints=constraints,
                options={'mip_rel_gap':0.,'disp':bool(output)})
    if result.status==2:return {'rcode':3}
    assert result.status==0,result.message
    x=result.x
    assert max(abs(x[j]-round(x[j])) for j in jint+jbin)<1e-6
    assert np.all(x>=-1e-7) and np.all(x[jbin]<=1.+1e-7)
    assert np.all(np.asarray(ai@x).ravel()<=np.asarray(bi,dtype=float)+1e-7)
    assert np.allclose(ae@x,be,atol=1e-7,rtol=0)
    return {'rcode':2,'x':np.rint(x),'primal objective':result.fun}

class NodeView(dict):
    def __call__(self):return self.keys()

class FixtureGraph:
    """Explicit finite graph-shaped data rather than the optional NX layer."""
    def __init__(self,moves,links,agents):
        names=sorted(set(agents.values())|{v for a in moves+links for v in a})
        self.nodes=NodeView({v:{'small':False} for v in names})
        self.agents=agents
        self.moves=tuple(sorted(set(moves)|{(v,v) for v in names}))
        self.links=tuple(sorted(set(links)))
    def number_of_nodes(self):return len(self.nodes)
    def __len__(self):return len(self.nodes)
    def tran_edges(self):return self.moves
    def conn_edges(self):return self.links
    def edges(self,data=False):
        assert data is True
        return tuple((a,b,dict(type='transition',weight=int(a!=b))) for a,b in self.moves)+tuple(
               (a,b,dict(type='connectivity',weight=1)) for a,b in self.links)
    def tran_in_edges(self,v):return tuple((a,b) for a,b in self.moves if b==v)
    def tran_out_edges(self,v):return tuple((a,b) for a,b in self.moves if a==v)
    def conn_in_edges(self,v):return tuple((a,b) for a,b in self.links if b==v)
    def conn_out_edges(self,v):return tuple((a,b) for a,b in self.links if a==v)

def scoped_solver(problem_type,constraint_type,requirements,contacts=(),report_late=()):
    """Add declared actuation/task/closure constraints to native matrix."""
    class Restricted(problem_type):
        def _solve(self,obj,constraint,**kwargs):
            idx=[]; columns=[]; values=[]; rhs=[]
            def require(ids,coeffs,b):
                idx.extend([len(rhs)]*len(ids));columns.extend(ids);values.extend(coeffs);rhs.append(b)
            for agent,t,allowed in requirements:
                require([self.get_z_idx(agent,v,t) for v in allowed],[1]*len(allowed),1)
            for t,a,b in contacts:
                # Optional authored temporal contact erasure of report AND master flow.
                require([self.get_fbar_idx(0,a,b,t),self.get_mbar_idx(a,b,t)],[1,1],0)
            for t,a,b in report_late:
                require([self.get_fbar_idx(0,a,b,t)],[1],0)
            neq=sp.coo_matrix((values,(idx,columns)),shape=(len(rhs),len(obj)))
            return super()._solve(obj,constraint & constraint_type(A_eq=neq,b_eq=np.array(rhs)),**kwargs)
    return Restricted
