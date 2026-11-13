"""Exact residual builder for the fixed-budget joint layer-native encoding.

The ten residual families D,H,P,G,T,N,C,L,W,O are the displayed construction.
Activity e_v is the selector sum and is not an independent variable.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from exact_polynomial import Poly, objective, rational


@dataclass(frozen=True)
class NativeData:
    # S and E explicitly store tuples of local retained and hidden indices.
    J: int
    S: tuple
    E: tuple
    A: tuple              # A[i][j][h_i]
    B: tuple              # B[i][h_i][s_i]
    Q: tuple              # Q[s][u]
    w: tuple              # w[s]
    R: tuple              # R[j][u]

    @property
    def modules(self):
        return len(self.A)

    @property
    def observed(self):
        return len(self.Q[0])

    @property
    def local_hidden_sizes(self):
        return [len(b) for b in self.B]

    @property
    def local_retained_sizes(self):
        return [len(b[0]) for b in self.B]

    def validate(self):
        """Validate finite normalized input and cheap marginal consistency."""
        def require(condition,message):
            if not condition:
                raise ValueError(message)
        require(self.J>0 and self.modules>0 and len(self.S)>0 and len(self.E)>0,'empty input carrier')
        require(len(self.B)==self.modules,'module count mismatch')
        require(len(self.w)==len(self.S) and len(self.Q)==len(self.S),'retained shape mismatch')
        require(len(self.R)==self.J,'observed row count mismatch')
        p = [sum(map(rational,row),F(0)) for row in self.A[0]]
        require(len(p)==self.J and sum(p,F(0))==1,'root law not normalized')
        for i in range(self.modules):
            require(len(self.A[i])==self.J,'local root row count mismatch')
            require([sum(map(rational,row),F(0)) for row in self.A[i]]==p,'announcement marginal mismatch')
            require(all(len(row)==len(self.B[i]) for row in self.A[i]),'local hidden shape mismatch')
            for row in self.B[i]:
                require(len(row)==self.local_retained_sizes[i] and sum(map(rational,row),F(0))==1,'local continuation not stochastic')
            for x in range(self.local_retained_sizes[i]):
                native=sum((F(self.A[i][j][h])*F(self.B[i][h][x]) for j in range(self.J) for h in range(len(self.B[i]))),F(0))
                joint=sum((F(self.w[s]) for s,tag in enumerate(self.S) if tag[i]==x),F(0))
                require(native==joint,'retained local marginal mismatch')
        require(all(len(row)==self.observed and sum(map(rational,row),F(0))==1 for row in self.Q),'Q not stochastic')
        require(sum(map(rational,self.w),F(0))==1,'w not normalized')
        require(all(len(row)==self.observed for row in self.R),'R column mismatch')
        require([sum(map(rational,row),F(0)) for row in self.R]==p,'R announcement marginal mismatch')
        for u in range(self.observed):
            require(sum((F(self.R[j][u]) for j in range(self.J)),F(0))==sum((F(self.w[s])*F(self.Q[s][u]) for s in range(len(self.S))),F(0)),'observed marginal mismatch')
        for tag in self.E:
            require(len(tag)==self.modules and all(0<=tag[i]<self.local_hidden_sizes[i] for i in range(self.modules)),'bad E tuple')
        for tag in self.S:
            require(len(tag)==self.modules and all(0<=tag[i]<self.local_retained_sizes[i] for i in range(self.modules)),'bad S tuple')
        def scalar_entries(x):
            if isinstance(x,(tuple,list)):
                return [v for entry in x for v in scalar_entries(entry)]
            return [rational(x)]
        require(all(v>=0 for v in scalar_entries((self.A,self.B,self.Q,self.w,self.R))),'negative input coefficient')
        return True


def name(prefix,*indices):
    return prefix+'['+','.join(map(str,indices))+']'


class Encoding:
    def __init__(self,data,K):
        data.validate()
        if not isinstance(K,int) or K<0:
            raise ValueError('K must be a nonnegative integer middle-state budget')
        self.data,self.K,self.variables,self.residuals=data,K,{},{}
        def var(prefix,*indices):
            key=name(prefix,*indices)
            self.variables[key]=Poly.variable(key)
            return self.variables[key]
        d={(v,h):var('d',v,h) for v in range(K) for h in range(len(data.E))}
        eta={v:var('eta',v) for v in range(K)}
        a={(j,v):var('a',j,v) for j in range(data.J) for v in range(K)}
        rho={(j,v):var('rho',j,v) for j in range(data.J) for v in range(K)}
        sigma={(j,v):var('sigma',j,v) for j in range(data.J) for v in range(K)}
        b={(v,s):var('b',v,s) for v in range(K) for s in range(len(data.S))}
        tau={(v,s):var('tau',v,s) for v in range(K) for s in range(len(data.S))}
        e={v:sum((d[v,h] for h in range(len(data.E))),Poly.constant(0)) for v in range(K)}
        self.blocks=dict(d=d,eta=eta,a=a,rho=rho,sigma=sigma,b=b,tau=tau,e=e)
        r=self.residuals
        for v in range(K):
            for h in range(len(data.E)):
                r[name('D',v,h)]=d[v,h]**2-d[v,h]
            r[name('H',v)]=1-e[v]-eta[v]**2
            for j in range(data.J):
                r[name('P',j,v)]=a[j,v]-rho[j,v]**2
                r[name('G',j,v)]=e[v]-a[j,v]-sigma[j,v]**2
            for s in range(len(data.S)):
                r[name('T',v,s)]=b[v,s]-tau[v,s]**2
            r[name('N',v)]=sum((b[v,s] for s in range(len(data.S))),Poly.constant(0))-e[v]
            for i in range(data.modules):
                for x in range(data.local_retained_sizes[i]):
                    r[name('C',v,i,x)]=sum((b[v,s] for s,tag in enumerate(data.S) if tag[i]==x),Poly.constant(0))-sum((d[v,h]*F(data.B[i][tag[i]][x]) for h,tag in enumerate(data.E)),Poly.constant(0))
        for i in range(data.modules):
            for j in range(data.J):
                for u in range(data.local_hidden_sizes[i]):
                    r[name('L',i,j,u)]=sum((a[j,v]*sum((d[v,h] for h,tag in enumerate(data.E) if tag[i]==u),Poly.constant(0)) for v in range(K)),Poly.constant(0))-F(data.A[i][j][u])
        for s in range(len(data.S)):
            r[name('W',s)]=sum((a[j,v]*b[v,s] for j in range(data.J) for v in range(K)),Poly.constant(0))-F(data.w[s])
        for j in range(data.J):
            for u in range(data.observed):
                r[name('O',j,u)]=sum((a[j,v]*b[v,s]*F(data.Q[s][u]) for v in range(K) for s in range(len(data.S))),Poly.constant(0))-F(data.R[j][u])
        self.objective=objective(r)

    def inactive_point(self):
        point={v:F(0) for v in self.variables}
        for v in range(self.K):
            point[name('eta',v)]=F(1)
        return point

    def lift_rational(self,slots):
        """Lift slot factors when all required square roots are rational.

        A slot is None (unused) or (E_index, root_column, continuation_row).
        This helper does not claim every rational implementation has a
        rational slack lift. An irrational square root raises ValueError.
        """
        if len(slots)!=self.K:
            raise ValueError('wrong number of slots')
        point=self.inactive_point()
        for v,slot in enumerate(slots):
            if slot is None:
                continue
            h,root,row=slot
            point[name('d',v,h)]=F(1)
            point[name('eta',v)]=F(0)
            for j,value in enumerate(root):
                value=F(value)
                point[name('a',j,v)]=value
                point[name('rho',j,v)]=rational_sqrt(value)
                point[name('sigma',j,v)]=rational_sqrt(1-value)
            for s,value in enumerate(row):
                value=F(value)
                point[name('b',v,s)]=value
                point[name('tau',v,s)]=rational_sqrt(value)
        return point

    def residual_values(self,point):
        return {k:p.evaluate(point) for k,p in self.residuals.items()}

    def decoded(self,point):
        """Decode and verify exact zero points; never interpret an approximate zero."""
        nonzero={k:v for k,v in self.residual_values(point).items() if v}
        if nonzero:
            raise ValueError('cannot decode nonzero residuals: '+str(nonzero))
        active=[v for v in range(self.K) if sum((point[name('d',v,h)] for h in range(len(self.data.E))),F(0))==1]
        return {'active_slots':active,'total_native_states':len(active)+2,
                'A':[[point[name('a',j,v)] for v in active] for j in range(self.data.J)],
                'B':[[point[name('b',v,s)] for s in range(len(self.data.S))] for v in active],
                'f':[self.data.E[next(h for h in range(len(self.data.E)) if point[name('d',v,h)]==1)] for v in active]}


def rational_sqrt(value):
    value=F(value)
    if value<0:
        raise ValueError('negative square-root argument')
    p,q=isqrt(value.numerator),isqrt(value.denominator)
    if p*p!=value.numerator or q*q!=value.denominator:
        raise ValueError(f'{value} has no rational square root')
    return F(p,q)


def singleton_data():
    return NativeData(1,((0,),),((0,),),(((F(1),),),),(((F(1),),),),((F(1),),),(F(1),),((F(1),),))


def empty_cross_tag_data():
    p,q=F(9,25),F(16,25)
    A=(((p,q),),((p,q),))
    B=(((F(1),F(0)),(F(0),F(1))),)*2
    return NativeData(1,((0,0),(1,1)),((0,0),(0,1),(1,0),(1,1)),A,B,
                      ((F(1),F(0)),(F(0),F(1))),(p,q),((p,q),))


def rank_two_data():
    """A two-state instance with a fully rational lift, and impossible K=1.

    Each of two local modules has one hidden state, with uniform continuation
    on four states. The first announcement selects diagonal correlation;
    the second selects the cyclic-shift correlation. All nonzero conditional
    probabilities are 1/4, so every continuation square root is rational.
    """
    p,q=F(9,25),F(16,25)
    S=tuple((i,j) for i in range(4) for j in range(4))
    row0=tuple(F(1,4) if i==j else F(0) for i,j in S)
    row1=tuple(F(1,4) if j==(i+1)%4 else F(0) for i,j in S)
    R=(tuple(p*x for x in row0),tuple(q*x for x in row1))
    w=tuple(R[0][s]+R[1][s] for s in range(len(S)))
    A=(((p,),(q,)),)*2
    B=(((F(1,4),)*4,),)*2
    Q=tuple(tuple(F(i==j) for j in range(len(S))) for i in range(len(S)))
    return NativeData(2,S,((0,0),),A,B,Q,w,R),row0,row1
