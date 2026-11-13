#!/usr/bin/env python3
"""Exact-rational checks for the finite-budget residual construction.

Run with both `python3 run_checks.py` and `python3 -O run_checks.py`.
No test relies on Python assert statements, random sampling, or floats.
"""
from fractions import Fraction as F
import argparse
import json
import sys
from itertools import product
from math import isqrt
from native_encoding import Encoding, NativeData, name, singleton_data, empty_cross_tag_data, rank_two_data
from exact_polynomial import Poly, objective, gradient, jacobian_gradient


class CheckFailure(Exception):
    pass


class Suite:
    def __init__(self):
        self.checks = []
        self.results = {}

    def equal(self, name, actual, expected):
        if actual != expected:
            raise CheckFailure(f'{name}: expected {expected!r}, found {actual!r}')
        self.checks.append(name)

    def true(self, name, condition):
        if not condition:
            raise CheckFailure(name)
        self.checks.append(name)


def matvec(matrix, vector):
    return [sum((F(a) * F(b) for a, b in zip(row, vector)), F(0)) for row in matrix]


def transpose(matrix):
    return list(map(list, zip(*matrix)))


def matmul(a, b):
    return [[sum((F(x) * F(y) for x, y in zip(row, col)), F(0))
             for col in zip(*b)] for row in a]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def subtract(a, b):
    return [x - y for x, y in zip(a, b)]


def transport_increment(phi, update):
    """T_phi(U)(y) = y + phi^T (U(phi y) - phi y)."""
    def transported(y):
        x = matvec(phi, y)
        return add(y, matvec(transpose(phi), subtract(update(x), x)))
    return transported


def test_polynomial_arithmetic(suite):
    x, y = Poly.variable('x'), Poly.variable('y')
    p = (x + 2 * y - F(3, 4)) ** 3
    point = {'x': F(1, 2), 'y': F(2, 3)}
    suite.equal('exact arithmetic value', p.evaluate(point), F(2197, 1728))
    suite.equal('exact arithmetic symbolic derivative', p.derivative('x'), 3 * (x + 2*y-F(3,4))**2)
    suite.equal('exact arithmetic repeated-variable derivative', (x*x*y).derivative('x'), 2*x*y)
    suite.equal('exact arithmetic renaming accumulates terms', (x*x+y*y).renamed({'x':'z','y':'z'}), 2*Poly.variable('z')**2)
    try:
        Poly.constant(0.5)
    except TypeError:
        suite.checks.append('float inputs rejected')
    else:
        raise CheckFailure('float inputs must be rejected')


def test_shared_gradient(suite):
    a, b_left, c, b_right = map(Poly.variable, ['a','b_left','c','b_right'])
    left = (a*b_left-F(1,2))**2
    right = (c*b_right-F(3,4))**2
    assembled = (left+right).renamed({'b_left':'b','b_right':'b'})
    local_point = {'a':F(1),'b_left':F(1,3),'c':F(2),'b_right':F(1,3)}
    common_point = {'a':F(1),'b':F(1,3),'c':F(2)}
    left_gradient = left.derivative('b_left').evaluate(local_point)
    right_gradient = right.derivative('b_right').evaluate(local_point)
    shared_gradient = assembled.derivative('b').evaluate(common_point)
    suite.equal('left shared-coordinate contribution', left_gradient, F(-1,3))
    suite.equal('right shared-coordinate contribution', right_gradient, F(-1,3))
    suite.equal('assembled shared-coordinate gradient sums both contributions', shared_gradient, left_gradient+right_gradient)
    suite.equal('assembled shared-coordinate exact gradient', shared_gradient, F(-2,3))
    step = F(1,10)
    synchronized = common_point['b'] - step*shared_gradient
    suite.equal('synchronized shared-coordinate Euler step', synchronized, F(2,5))
    suite.results['shared_gradient'] = {'contributions':[left_gradient,right_gradient], 'sum':shared_gradient,'step':synchronized}


def test_euler_transport(suite):
    phi = [[F(1)], [F(1)]]
    y = [F(3)]
    epsilon = F(1,4)
    def update(x):
        return [(1-epsilon)*v for v in x]
    naive = matvec(transpose(phi), update(matvec(phi,y)))
    correct = transport_increment(phi,update)(y)
    assembled = [y[0] - epsilon*2*y[0]]
    suite.equal('naive transported Euler value', naive, [F(9,2)])
    suite.equal('correct transported Euler value', correct, [F(3,2)])
    suite.equal('correct increment equals Euler after assembling vector field', correct, assembled)
    suite.true('naive Euler does not commute with variable identification', naive != assembled)
    identity = lambda x: list(x)
    suite.equal('naive transport duplicates identity baseline', matvec(transpose(phi),identity(matvec(phi,y))), [F(6)])
    suite.equal('increment transport preserves identity update', transport_increment(phi,identity)(y), y)

    # Arbitrary rational linear maps, including a non-isometric map.
    phi2 = [[F(1),F(2)],[F(-1),F(1)],[F(1,2),F(-3,2)]]
    psi = [[F(2)],[F(-1)]]
    def nonlinear_update(x):
        return [x[0]+x[1]*x[2], x[1]-x[0]**2, x[2]+F(3,7)]
    z = [F(2,3)]
    sequential = transport_increment(psi,transport_increment(phi2,nonlinear_update))(z)
    direct = transport_increment(matmul(phi2,psi),nonlinear_update)(z)
    suite.equal('increment transport composition law', sequential, direct)
    eye = [[F(i==j) for j in range(3)] for i in range(3)]
    x = [F(1,2),F(-2,3),F(4,5)]
    suite.equal('increment transport identity law', transport_increment(eye,nonlinear_update)(x), nonlinear_update(x))
    suite.results['euler_transport'] = {'naive':naive,'correct':correct,'composition_value':direct}


def require_native(suite, data, model, prefix):
    A,B,tags=model['A'],model['B'],model['f']
    n=len(tags)
    suite.true(prefix+' nonempty counted middle carrier',n>0)
    suite.equal(prefix+' counts root and terminal',model['total_native_states'],n+2)
    suite.true(prefix+' native probabilities nonnegative',all(x>=0 for rows in [A,B] for row in rows for x in row))
    suite.equal(prefix+' root normalization',sum((x for row in A for x in row),F(0)),F(1))
    for v in range(n):
        suite.equal(prefix+f' continuation normalization {v}',sum(B[v],F(0)),F(1))
    for i in range(data.modules):
        for j in range(data.J):
            for h in range(data.local_hidden_sizes[i]):
                suite.equal(prefix+f' native root square {i},{j},{h}',sum((A[j][v] for v in range(n) if tags[v][i]==h),F(0)),F(data.A[i][j][h]))
        for v in range(n):
            for x in range(data.local_retained_sizes[i]):
                suite.equal(prefix+f' native row square {i},{v},{x}',sum((B[v][s] for s,tag in enumerate(data.S) if tag[i]==x),F(0)),F(data.B[i][tags[v][i]][x]))
    T=matmul(A,B)
    suite.equal(prefix+' retained marginal',[sum((T[j][s] for j in range(data.J)),F(0)) for s in range(len(data.S))],list(data.w))
    suite.equal(prefix+' complete observed law',matmul(T,data.Q),list(map(list,data.R)))


def test_native_zero_and_stationarity(suite):
    encoding=Encoding(singleton_data(),1)
    suite.equal('singleton variable count',len(encoding.variables),7)
    suite.equal('singleton scalar residual count',len(encoding.residuals),10)
    suite.true('singleton residual degree at most two',all(r.degree<=2 for r in encoding.residuals.values()))
    suite.equal('singleton objective quartic',encoding.objective.degree,4)
    inactive=encoding.inactive_point()
    feasible=encoding.lift_rational([(0,[F(1)],[F(1)])])
    suite.equal('genuine feasible singleton exact residual zero',encoding.residual_values(feasible),{k:F(0) for k in encoding.residuals})
    suite.equal('genuine feasible singleton objective zero',encoding.objective.evaluate(feasible),F(0))
    require_native(suite,encoding.data,encoding.decoded(feasible),'singleton')
    inactive_gradient=gradient(encoding.objective,inactive,encoding.variables)
    suite.equal('all-inactive objective positive',encoding.objective.evaluate(inactive),F(3))
    suite.equal('all-inactive exact full gradient zero',inactive_gradient,{v:F(0) for v in encoding.variables})
    suite.equal('all-inactive symbolic gradient matches Jacobian formula',inactive_gradient,jacobian_gradient(encoding.residuals,inactive,encoding.variables))
    trial={v:F(i-2,7) for i,v in enumerate(sorted(encoding.variables))}
    suite.equal('nonstationary exact gradient matches Jacobian formula',gradient(encoding.objective,trial,encoding.variables),jacobian_gradient(encoding.residuals,trial,encoding.variables))
    # A legitimate weighted residual objective keeps the same zero set.
    weighted=sum(((100 if k[0] in 'DHPGTNC' else 1)*r**2 for k,r in encoding.residuals.items()),Poly.constant(0))
    suite.equal('weighted strict-local-min example positive value',weighted.evaluate(inactive),F(3))
    suite.equal('weighted strict-local-min example full stationary gradient',gradient(weighted,inactive,encoding.variables),{v:F(0) for v in encoding.variables})
    suite.equal('weighted example still has feasible zero',weighted.evaluate(feasible),F(0))
    # Exact Hessian block is a check, not a substitute for the quartic proof.
    coordinates=[name('d',0,0),name('a',0,0),name('b',0,0),name('eta',0)]
    hessian=[[weighted.derivative(v).derivative(w).evaluate(inactive) for w in coordinates] for v in coordinates]
    expected=[[1000,-202,-400,400],[-202,400,-4,0],[-400,-4,600,0],[400,0,0,800]]
    suite.equal('weighted stationary Hessian nonflat block',hessian,expected)
    # Verify the exact identity behind the strict local minimum proof.
    # Each term on the right is nonnegative on |d|<1/2; the A-bound
    # is proved by the cases a<0 and a>=0 in README.md, not by sampling.
    d=encoding.variables[name('d',0,0)]; a=encoding.variables[name('a',0,0)]
    b=encoding.variables[name('b',0,0)]
    D=encoding.residuals[name('D',0,0)]; H=encoding.residuals[name('H',0)]
    L=encoding.residuals[name('P',0,0)]; G=encoding.residuals[name('G',0,0)]
    T=encoding.residuals[name('T',0,0)]; N=encoding.residuals[name('N',0)]
    lower=14*d**2+94*G**2+97*L**2+96*N**2+a**2*d**2+2*a**2*b**2
    remainder=100*(D**2-d**2/4)+(a-d)**2+2*(a-b)**2+3*(2*d**2+2*G**2+L**2-a**2)+2*(b-2*d)**2+100*(H**2+T**2+N**2)
    suite.equal('strict local minimum lower-bound exact polynomial identity',weighted-3-lower,remainder)
    zero_budget=Encoding(singleton_data(),0)
    suite.equal('zero middle-state budget has no variables',len(zero_budget.variables),0)
    suite.equal('zero middle-state budget constant obstruction',zero_budget.objective,Poly.constant(3))
    suite.results['singleton']={'feasible_objective':F(0),'inactive_objective':F(3),'inactive_gradient':inactive_gradient,'weighted_hessian':hessian}


def test_unused_empty_slots(suite):
    data=empty_cross_tag_data()
    encoding=Encoding(data,4)
    p,q=F(9,25),F(16,25)
    point=encoding.lift_rational([(0,[p],[1,0]),(3,[q],[0,1]),None,None])
    suite.equal('padded native example exact zero',encoding.objective.evaluate(point),F(0))
    suite.equal('padded native example every scalar residual zero',encoding.residual_values(point),{k:F(0) for k in encoding.residuals})
    model=encoding.decoded(point)
    suite.equal('two occupied slots within budget four',model['active_slots'],[0,1])
    require_native(suite,data,model,'padded')
    suite.equal('unused slots have zero continuation rows',[[point[name('b',v,s)] for s in range(len(data.S))] for v in [2,3]],[[F(0),F(0)],[F(0),F(0)]])
    suite.equal('unused slots do not require normalized continuation',sum((point[name('b',2,s)] for s in range(len(data.S))),F(0)),F(0))
    # If an unused slot is activated with an off-diagonal tag, two required
    # local x=0 residuals differ identically by -1. Both cannot vanish.
    cross={name('d',2,h):F(h==1) for h in range(len(data.E))}
    mismatch=(encoding.residuals[name('C',2,0,0)]-encoding.residuals[name('C',2,1,0)]).substituted(cross)
    suite.equal('empty cross-tag coupling exact contradiction',mismatch,Poly.constant(-1))
    # Build the actual time-homogeneous phase generator and verify cylinders.
    A,B=model['A'],model['B']
    middle=len(B)
    size=middle+2
    terminal=size-1
    alphabet=['a'+str(j) for j in range(data.J)]+['b'+str(u) for u in range(data.observed)]+['#']
    matrices={label:[[F(0) for _ in range(size)] for _ in range(size)] for label in alphabet}
    for j in range(data.J):
        for v in range(middle): matrices['a'+str(j)][0][v+1]=A[j][v]
    BQ=matmul(B,data.Q)
    for v in range(middle):
        for u in range(data.observed): matrices['b'+str(u)][v+1][terminal]=BQ[v][u]
    matrices['#'][terminal][terminal]=F(1)
    tested=0
    for length in range(5):
        for word in product(alphabet,repeat=length):
            distribution=[F(1)]+[F(0)]*(size-1)
            for symbol in word:
                distribution=matvec(transpose(matrices[symbol]),distribution)
            actual=sum(distribution,F(0))
            if length==0: expected=F(1)
            elif word[0].startswith('a') and length==1: expected=sum(data.R[int(word[0][1:])],F(0))
            elif word[0].startswith('a') and word[1].startswith('b') and all(s=='#' for s in word[2:]): expected=data.R[int(word[0][1:])][int(word[1][1:])]
            else: expected=F(0)
            if actual!=expected:
                raise CheckFailure(f'native cylinder {word}: {actual} != {expected}')
            tested+=1
    suite.true('actual normalized native generator cylinders through length four',tested==341)
    suite.results['unused_slots']={'budget':4,'occupied':2,'total_native_states':4,'objective':F(0),'empty_tag_contradiction':str(mismatch),'cylinders_checked':tested}


def test_rank_budget_obstruction(suite):
    data,row0,row1=rank_two_data()
    encoding=Encoding(data,2)
    p,q=F(9,25),F(16,25)
    point=encoding.lift_rational([(0,[p,0],row0),(0,[0,q],row1)])
    suite.equal('rank-two full rational lift zero',encoding.objective.evaluate(point),F(0))
    require_native(suite,data,encoding.decoded(point),'rank-two')
    # A feasible linear tensor with E singleton is exactly R (Q is identity).
    for j in range(data.J):
        for i in range(data.modules):
            for x in range(data.local_retained_sizes[i]):
                observed=sum((data.R[j][s] for s,tag in enumerate(data.S) if tag[i]==x),F(0))
                suite.equal(f'linear tensor mechanism equation {j},{i},{x}',observed,[p,q][j]*F(1,4))
    c0,c1=data.S.index((0,0)),data.S.index((0,1))
    target_minor=data.R[0][c0]*data.R[1][c1]-data.R[0][c1]*data.R[1][c0]
    suite.equal('rank-two target nonzero minor',target_minor,F(9,625))
    a0,a1,b0,b1=map(Poly.variable,['a0','a1','b0','b1'])
    factor_minor=(a0*b0)*(a1*b1)-(a0*b1)*(a1*b0)
    suite.equal('every one-state factor minor vanishes identically',factor_minor,Poly.constant(0))
    suite.true('budget one impossible by exact rank certificate',target_minor!=0 and factor_minor==0)
    suite.results['rank_budget']={'linear_tensor_feasible':True,'minimum_middle_states':2,'target_minor':target_minor,'one_state_factor_minor':str(factor_minor),'two_state_objective':F(0),'variables':len(encoding.variables),'residuals':len(encoding.residuals)}


def test_small_infeasible_residual(suite):
    # Square-root coordinates need not be rational. This family has exact
    # rational squares, and every residual is even in those coordinates.
    # Evaluate those squares symbolically, never approximating a radical.
    z=Poly.variable('z')
    suite.equal('algebraic squared-coordinate evaluation exact',(z**4+z**2).evaluate_with_squared_coordinates({}, {'z':F(1,2)}),F(3,4))
    try:
        z.evaluate_with_squared_coordinates({}, {'z':F(1,2)})
    except ValueError:
        suite.checks.append('algebraic squared-coordinate evaluator rejects odd powers')
    else:
        raise CheckFailure('odd radical powers must not be approximated')
    records=[]
    for epsilon in [F(1,2),F(1,10),F(1,100),F(1,1000)]:
        half=F(1,2)
        data=NativeData(1,((0,0),(1,1)),((0,0),(1,1)),
                        (((half,half),),)*2,
                        (((F(1),F(0)),(F(0),F(1))),
                         ((1-epsilon,epsilon),(epsilon,1-epsilon))),
                        ((F(1),F(0)),(F(0),F(1))),
                        (half,half),((half,half),))
        encoding=Encoding(data,2)
        point=encoding.inactive_point()
        squared={}
        for v in range(2):
            point[name('eta',v)]=F(0)
            point[name('d',v,v)]=F(1)
            point[name('a',0,v)]=half
            squared[name('rho',0,v)]=half
            squared[name('sigma',0,v)]=half
            for s in range(2):
                b=1-epsilon/2 if s==v else epsilon/2
                point[name('b',v,s)]=b
                squared[name('tau',v,s)]=b
        for coordinate in squared: point.pop(coordinate)
        values={k:r.evaluate_with_squared_coordinates(point,squared) for k,r in encoding.residuals.items()}
        objective_value=encoding.objective.evaluate_with_squared_coordinates(point,squared)
        prefix=f'small infeasible residual epsilon={epsilon}'
        suite.equal(prefix+' exact objective law',objective_value,2*epsilon**2)
        suite.equal(prefix+' objective equals scalar square sum',objective_value,sum((v*v for v in values.values()),F(0)))
        suite.equal(prefix+' exactly eight row residuals nonzero',len([v for v in values.values() if v]),8)
        suite.true(prefix+' all other residual families vanish',all(value==0 for key,value in values.items() if not key.startswith('C[')))
        suite.true(prefix+' row residual magnitudes',all(abs(value)==epsilon/2 for key,value in values.items() if key.startswith('C[')))
        for tag in range(2):
            selector={name('d',0,h):F(h==tag) for h in range(2)}
            mismatch=(encoding.residuals[name('C',0,0,0)]-encoding.residuals[name('C',0,1,0)]).substituted(selector)
            suite.equal(prefix+f' empty selected coupling {tag}',mismatch,Poly.constant(-epsilon if tag==0 else epsilon))
        records.append({'epsilon':epsilon,'objective':objective_value,'nonzero_row_residuals':8,'all_allowed_coupling_polytopes_empty':True})
    suite.results['small_infeasible_residual']={'evaluation':'exact rational square values of algebraic slack coordinates','instances':records}


def test_coercivity_bounds(suite):
    encoding=Encoding(singleton_data(),1)
    variables=sorted(encoding.variables)
    points=[encoding.inactive_point(),encoding.lift_rational([(0,[1],[1])])]
    points += [{v:F(t+i,3) for i,v in enumerate(variables)} for t in [-8,-2,0,5]]
    records=[]
    for index,point in enumerate(points):
        value=encoding.objective.evaluate(point)
        # epsilon=q(q-1) makes D_epsilon=q exactly, avoiding irrational roots.
        q=1
        while F(q*q*(q-1)*(q-1))<value: q+=1
        epsilon=F(q*(q-1)); bound=epsilon**2
        suite.true(f'coercivity example {index} in stated sublevel',value<=bound)
        residuals=encoding.residual_values(point)
        suite.true(f'coercivity example {index} each residual bounded',all(abs(r)<=epsilon for r in residuals.values()))
        d=point[name('d',0,0)]; eta=point[name('eta',0)]
        a=point[name('a',0,0)]; rho=point[name('rho',0,0)]; sigma=point[name('sigma',0,0)]
        b=point[name('b',0,0)]; tau=point[name('tau',0,0)]
        suite.true(f'coercivity example {index} selector bound',abs(d)<=q)
        suite.true(f'coercivity example {index} cap slack bound',eta**2<=1+q+epsilon)
        suite.true(f'coercivity example {index} root coefficient bound',-epsilon<=a<=1+2*epsilon)
        suite.true(f'coercivity example {index} root square-slack bounds',rho**2<=1+3*epsilon and sigma**2<=1+3*epsilon)
        suite.true(f'coercivity example {index} row coefficient bound',-epsilon<=b<=1+2*epsilon)
        suite.true(f'coercivity example {index} row square-slack bound',tau**2<=1+3*epsilon)
        records.append({'objective':value,'M':bound,'epsilon':epsilon,'D_epsilon':q})
    # Optional redundant circles: exact Cauchy-Schwarz algebraic identity.
    n=3
    x=list(map(Poly.variable,['x0','x1','x2']))
    z=list(map(Poly.variable,['z0','z1','z2']))
    u=[x[i]**2+z[i]**2-1 for i in range(n)]
    left=n*sum((v**2 for v in u),Poly.constant(0))-sum(u,Poly.constant(0))**2
    right=sum(((u[i]-u[j])**2 for i in range(n) for j in range(i+1,n)),Poly.constant(0))
    suite.equal('circle coercivity bound exact polynomial SOS identity',left,right)
    # Generic polynomial SOS without these gates need not attain infimum.
    aa,bb=Poly.variable('aa'),Poly.variable('bb')
    escaping=(aa*bb-1)**2+aa**2
    for n in [1,2,5,10,100]:
        suite.equal(f'ungated noncoercive escape at n={n}',escaping.evaluate({'aa':F(1,n),'bb':F(n)}),F(1,n*n))
    suite.results['coercivity']={'sublevel_examples':records,'circle_SOS_identity':True,'ungated_escape_values':['1','1/4','1/25','1/100','1/10000']}


def jsonable(value):
    if isinstance(value,F):
        return str(value)
    if isinstance(value,dict):
        return {k:jsonable(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [jsonable(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', help='Write a machine-readable report to this path.')
    args = parser.parse_args()
    suite = Suite()
    test_polynomial_arithmetic(suite)
    test_shared_gradient(suite)
    test_euler_transport(suite)
    test_native_zero_and_stationarity(suite)
    test_unused_empty_slots(suite)
    test_rank_budget_obstruction(suite)
    test_coercivity_bounds(suite)
    test_small_infeasible_residual(suite)
    report = {'status':'PASS','optimization_level':sys.flags.optimize,
              'exact_arithmetic':'fractions.Fraction','check_count':len(suite.checks),
              'checks':suite.checks,'results':jsonable(suite.results)}
    if args.json:
        with open(args.json,'w',encoding='utf-8') as stream:
            json.dump(report,stream,indent=2,sort_keys=True)
            stream.write('\n')
    print(f"PASS: {len(suite.checks)} exact-rational checks; Python optimization={sys.flags.optimize}")
    for name, result in suite.results.items():
        print(name + ': ' + json.dumps(jsonable(result),sort_keys=True))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except CheckFailure as error:
        print('FAIL: ' + str(error),file=sys.stderr)
        sys.exit(1)
