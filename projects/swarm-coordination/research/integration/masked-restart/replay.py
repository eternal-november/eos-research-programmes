"""Qualification of one upstream label transform and two civil design fixtures."""
import ast
import hashlib
import sys
from itertools import product
from pathlib import Path


TARGET = '6dde97dff447ee6f6d8fdb0e4c22423014a091b8'


def source_probe(filename):
    import pandas as pd
    raw = Path(filename).read_bytes()
    blob = hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()
    assert blob == TARGET, blob
    fn = next(n for n in ast.parse(raw).body if isinstance(n, ast.FunctionDef)
              and n.name == 'mask_inactive_faults')
    scope = {'pd': pd}
    exec(compile(ast.Module(body=[fn], type_ignores=[]), '<pinned mask>', 'exec'), scope)
    mask = scope[fn.name]
    index = pd.Index([0, 1, 2, 3], name='simulationTime')
    state = pd.DataFrame({'AMR_1.CurrentState':['Busy', 'Idle', 'Idle', 'Busy']}, index=index)
    def labels(raw):
        return mask(pd.DataFrame({'AMR_1.BlockedFault':raw}, index=index), state).iloc[:, 0].tolist()
    retained, removed, missing = (labels(x) for x in ([1,1,1,1],[1,0,0,0],[1,None,None,0]))
    assert retained[:3] == removed[:3] == missing[:3] == [1,0,0]
    assert [retained[-1], removed[-1], missing[-1]] == [1,0,0]
    print('Pinned TwinFlow transform: persistent, cleared and missing agree while idle; persistent returns active')


def earliest(rest, window, release, readback, probe, extra, job, isolated, latest=31):
    start_probe = finish_probe = start_job = None
    for k in range(latest+1):
        if start_probe is None and k >= rest and k >= window:
            if isolated or k >= release + readback:
                start_probe = k
                finish_probe = k + probe + (extra if isolated else 0)
        if finish_probe is not None and k >= finish_probe and k >= release + readback:
            if start_job is None:
                start_job = k
        if start_job is not None and k >= start_job + job:
            return k
    return None


def matched_timing():
    n = bonuses = ties = penalties = 0
    # Same plant family across the two fixture interpretations.
    for rest, window, release, c, u, d, h in product(
        range(6), range(6), range(8), range(4), range(1,5), range(4), range(1,4)
    ):
        x, y = max(rest, window), release + c
        shared = max(x, y) + u + h
        isolated = max(x + u + d, y) + h
        assert shared == earliest(rest,window,release,c,u,d,h,False)
        assert isolated == earliest(rest,window,release,c,u,d,h,True)
        assert (isolated < shared) == (d < y-x)
        if isolated < shared:
            assert shared-isolated == min(u,y-x-d)
            bonuses += 1
        elif isolated > shared: penalties += 1
        else: ties += 1
        n += 1
    print(n, 'source event schedules; wins/ties/losses', bonuses,ties,penalties)
    for sec in (False, True):
        print('isolated' if sec else 'shared', 'finish', earliest(3,2,6,1,2,1,1,sec))


if __name__ == '__main__':
    if len(sys.argv)>1:
        source_probe(sys.argv[1])
    matched_timing()

