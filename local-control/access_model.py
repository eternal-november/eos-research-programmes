"""Exact access/compensation comparison arithmetic, not a new global simulator."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def margins(m, b, p, cap, hostile, collar):
    weight = b+(cap-1)*p
    upper = F(23,100)-hostile-(F(186,100)*b+(cap-1)*p)/m-collar*(2*(1-F(b,m))+F(6,100))
    lower = F(23,100)-hostile-(F(66,100)*b+(cap-1)*p)/m-collar*(2*(1-F(b,m))+F(6,100))
    service = F(3,10)-(F(13,10)*b+(cap-1)*p)/m
    # Independently compute from actual interval sums, not the simplified law.
    up_sum = (F(86,100)*(m-b)-weight-2*collar*(m-b))/m
    low_sum = (F(34,100)*(m-b)+weight+2*collar*(m-b))/m
    require(upper == up_sum-(F(61,100)+hostile+F(2,100)+F(6,100)*collar), 'Upper capacity translation')
    require(lower == F(59,100)-hostile-F(2,100)-F(6,100)*collar-low_sum, 'Lower capacity translation')
    require(service == (F(3,10)*(m-b)-weight)/m, 'Service capacity translation')
    return upper, lower, service


def check():
    cases = 0
    for m in (72, 80, 144, 720):
        for b in range(7):
            for p in range(min(1,b)+1):
                for cap in (F(1), F(2), F(4)):
                    for hostile in (F(0), F(1,100), F(1,50)):
                        for collar in (F(0), F(1,100), F(1,200)):
                            margins(m,b,p,cap,hostile,collar)
                            cases += 1
    point = margins(72,6,1,F(4),F(1,100),F(1,100))
    require(point == (F(11,2500), F(261,2500), F(3,20)), 'Current positive source point changed')
    threshold = F(1,100)+point[0]
    require(threshold == F(9,625), 'Wrong sufficient hostile-input threshold')
    require(margins(72,6,1,F(4),threshold,F(1,100))[0] == 0, 'Threshold is not exact for chosen certificate')
    # Same actuators, constant-output policy, symmetric coupling cancels.
    exit_time = (F(65,100)-F(6,10))/F(1,100)
    require(exit_time == 5, 'Constant-output comparison drift')
    # Grant full physical unit capacity to all controllable sources.
    unavoidable_drift = F(61,100)+F(1,2)-1-F(18,1000)-F(2,100)
    require(unavoidable_drift == F(9,125), 'Finite-capacity obstruction')
    unavoidable_exit = F(5,100)/unavoidable_drift
    require(unavoidable_exit == F(25,36), 'Wrong unavoidable exit bound')
    # Finite stock model checks only the monotone-code-count/exposure argument.
    # It does not assert the raw cofinal-access premise for another architecture.
    stocks = []
    for count in (2,3,7,32):
        intact = set(range(count))
        previous = len(intact)
        for body in range(count):
            intact.discard(body)
            require(len(intact) == previous-1, 'One new useful-body corruption did not consume stock')
            previous = len(intact)
        require(not intact, 'Finite reserve gained a new correct body without a supplier')
        stocks.append(count)
    return dict(parameter_translations=cases,
                positive_point=[str(x) for x in point],
                chosen_collar_hostile_threshold=str(threshold),
                matched_constant_output_exit_time=str(exit_time),
                stronger_source_capacity_drift=str(unavoidable_drift),
                stronger_source_exit_time=str(unavoidable_exit),
                finite_code_stock_counts=stocks,
                scope='Parameterized interval proof and explicit changed-capacity source obstruction; source suppliers and cofinal code exposure remain stated hypotheses')


def digest(name):
    return sha256((HERE/name).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode('utf-8')).hexdigest()


def main():
    require(not sys.flags.optimize, 'Optimized Python is not a checking mode')
    p=argparse.ArgumentParser()
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--write',action='store_true')
    g.add_argument('--check',action='store_true')
    args=p.parse_args()
    names=('INTERNAL-ACCESS.md','access_model.py','FAULT-MAP.md','Effects.lean')
    before={name:digest(name) for name in names}
    result=dict(status='derived conditional access/compensation comparison',sources=before,checks=check())
    require(before=={name:digest(name) for name in names}, 'Inputs changed during checking')
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    record=HERE/'access_results.json'
    if args.write:
        record.write_text(text,encoding='utf-8')
    else:
        require(record.read_text(encoding='utf-8')==text,'Access record stale')
    print('access record written' if args.write else 'access record matches')


if __name__=='__main__':
    main()
