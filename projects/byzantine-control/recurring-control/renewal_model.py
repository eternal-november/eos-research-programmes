"""Operational checks for recurring peer reconstruction; see RENEWAL.md.

The physical copy checks use actual mutable donor bits, delayed emitter settings,
contact dynamics and a target store. They are component checks, not the complete
bytecode, information/control or resource realization owned by other modules.
"""
from __future__ import annotations
import sys
if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
import argparse
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re
import subprocess

HERE=Path(__file__).resolve().parent
LEAN=Path(r'C:\Users\Sean\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe')
N=34
M=65536
S=M+64
PERIOD=N*S
D=M+30
H=PERIOD+D
G=28
BAD=5
CLOCK=128
ID=160
DRAIN=166


def require(ok,message):
    if not ok: raise RuntimeError(message)


def clipq(q): return min(96,max(0,q))


def cell(old,z,opened):
    if not opened: return old
    return 1 if z>42 else (0 if z < -42 else old)


@lru_cache(maxsize=256)
def encoded_bits(width,value):
    return bytes((value>>k)&1 for k in range(width))


def put(mem,offset,width,value):
    # Host-side reuse of a pure bit encoding does not alter simulated memory.
    mem[offset:offset+width]=encoded_bits(width,value)


def get(mem,offset,width):
    return sum(mem[offset+k]<<k for k in range(width))


def image(m,target,phase):
    require(m>=192,'Test layout needs its explicit finite fields')
    mem=bytearray(m)
    for a in range(1,128): mem[a]=((a*73)^(a>>2)^0x5A)&1
    mem[0]=0  # abstract conditional-protocol dispatch, not full production bytecode
    put(mem,CLOCK,32,phase)
    put(mem,ID,6,target)
    put(mem,DRAIN,5,16)
    mem[-1]=0
    return mem


def template_bit(donor,phase,m,k,target,P):
    # Actual resident common code is copied. Volatile state is initialized by the
    # finite nominal routine; the evaluator never passes a canonical image oracle.
    if k<128: return donor[k]
    if CLOCK<=k<CLOCK+32:
        return (((phase+m+1-k)%P)>>(k-CLOCK))&1
    if ID<=k<ID+6: return (target>>(k-ID))&1
    if DRAIN<=k<DRAIN+5: return (16>>(k-DRAIN))&1
    return 0


def conditional_copy(m,attack,initial_q=0,raw_at=None,omit_address=None):
    """Exact q/field/store projection of one delayed two-emitter copy sequence.

    G actual donor stores remain nominal during this conditional check. Five
    adverse contributors exercise a conservative local field envelope. Its worst
    placement is not asserted to be a complete reachable global raw-fault trace.
    """
    P=N*(m+64)
    donor=[image(m,j+1,0) for j in range(G)]
    phases=[0]*G
    target=image(m,0,0)
    target[:]=bytes(1-b for b in target)
    q=initial_q
    sigma=1
    pending_sigma=1
    held_good=[]
    pending_good=[]
    held_bad=[]
    pending_bad=[]
    first_off=None
    first_full=None
    first_boot=None
    boot_phase=None
    installed=False
    post_raw=False
    cells_written=set()
    history=sha256()
    max_budget=0
    for tick in range(m+9):
        sigma=pending_sigma
        held_good,pending_good=pending_good,[]
        held_bad,pending_bad=pending_bad,[]
        if raw_at is not None and tick==raw_at:
            target[:]=bytes([1])*m
            q=0
            sigma=1
            post_raw=True
        # All fields are actual delayed settings. Contact and bit allocations are
        # disjoint terms of the same two-emitter budget, never separately doubled.
        force=sum(f for f,a,b in held_good+held_bad)
        q=clipq(q+force-42-1)
        if first_off is None and q>=16: first_off=tick
        if first_full is None and q==96: first_full=tick
        z=defaultdict(int)
        for f,a,b in held_good+held_bad:
            if a is not None: z[a]+=b
        if q>=80:
            for a,value in z.items():
                # Adverse quarter-unit disturbance within the nominal source law.
                noise=-1 if value>=0 else 1
                before=target[a]
                target[a]=cell(before,value+noise,True)
                if abs(value+noise)>42: cells_written.add(a)
        powered=q<16
        if powered:
            if tick>0 and first_off is not None and first_boot is None and q<16:
                first_boot=tick
                boot_phase=get(target,CLOCK,32)
                installed=target==image(m,0,(m+5)%P)
            # Explicit abstract poisoned instruction changes its own code while
            # powered; no validity/cure flag selects the operational branch.
            if target[0]: target[0]=1
            else:
                put(target,CLOCK,32,(get(target,CLOCK,32)+1)%P)
        pending_sigma=target[-1]
        for j in range(G):
            r=phases[j]%(m+64)
            if r<4: setting=(4,None,0)
            elif r<m+4:
                k=r-4
                bit=template_bit(donor[j],phases[j],m,k,0,P)
                setting=(4,None,0) if k==omit_address else (4,k,4 if bit else -4)
            elif r==m+4: setting=(-8,None,0)
            else: setting=(0,None,0)
            max_budget=max(max_budget,abs(setting[0])+abs(setting[2]))
            pending_good.append(setting)
            phases[j]=(phases[j]+1)%P
            put(donor[j],CLOCK,32,phases[j])
        # A causal finite malicious field program, timed by its own initialized
        # phase; no need to see future physical outcomes.
        r=tick%(m+64)
        selected=r-4 if 4<=r<m+4 else None
        for j in range(BAD):
            if attack=='contact': setting=(-8,None,0)
            elif selected is not None:
                nominal=template_bit(donor[0],tick%P,m,selected,0,P)
                if attack=='split': setting=(-4,selected,-4 if nominal else 4)
                elif attack=='selected': setting=(0,selected,-8 if nominal else 8)
                elif attack=='old_prefix': setting=(0,0,8)
                else: raise ValueError(attack)
            else: setting=(8,None,0)
            max_budget=max(max_budget,abs(setting[0])+abs(setting[2]))
            pending_bad.append(setting)
        history.update(bytes((q,sigma,int(powered),target[0])))
    require(max_budget<=8,'Two unit emitters overspent')
    if raw_at is None and omit_address is None:
        require(first_off<=1 and first_full<=4,'Contact/power timing')
        require(first_boot==m+5 and installed,'Actual complete image/phase not restored')
        require(sigma==0 and boot_phase==(m+5)%P,'Route/phase mismatch')
        require(len(cells_written)==m,'Not every addressed cell was written')
    else:
        require(not installed,'Countercase unexpectedly installed image')
    return dict(bits=m,attack=attack,raw_at=raw_at,omitted_address=omit_address,
                first_unpowered=first_off,first_full_contact=first_full,first_powered_boot=first_boot,
                actual_image_at_boot=installed,boot_phase=boot_phase,selector_at_end=sigma,
                addresses_written=len(cells_written),max_quarter_unit_emitter_budget=max_budget,
                trace_sha256=history.hexdigest())


def finite_physics():
    # Unknown missing incoming maintenance edge: actual field margins survive.
    weakened_donors=27
    selected=4*weakened_donors-8*BAD-1
    opening=selected-42
    closing=-8*weakened_donors+8*BAD+1-42
    require(selected>42 and opening*4>=96 and closing < -96,'Missing-edge transport')
    idle_cases=0
    for z in range(-41,42):
        require(clipq(z-42)==0,'Subthreshold contact opening')
        for old,opened in product((0,1),(False,True)):
            require(cell(old,z,opened)==old,'Subthreshold cell alteration')
            idle_cases+=1
    for q in range(97):
        value=q
        for _ in range(4): value=clipq(value+29)
        require(value==96,'Four opening ticks')
        require(clipq(q-225)==0,'One closing tick')
    P=N*(M+64)
    checked=0
    for c0 in (0,1,P-1,P-M,12345):
        for k in range(M):
            require((((c0+4+k)%P)+(M+1-k))%P==(c0+M+5)%P,'Mixed clock copy')
            checked+=1
    # Same field that cannot flip the hysteretic cell eventually flips an
    # integrating replacement while the rest of the image is being written.
    dose=0
    ticks=0
    while dose<=42:
        dose+=8
        ticks+=1
    require(ticks==6,'Integrating-cell witness')
    return dict(idle_cell_cases=idle_cases,contact_initial_states=97,
                one_missing_incoming_edge={'donors':weakened_donors,
                    'selected_field':selected,'opening_increment':opening,
                    'closing_increment':closing},
                phase_bit_positions_checked=checked,creep_flip_after_ticks=ticks,
                full_period=P,full_duration=D,full_horizon=H,
                horizon_below_raw_separation=H<10_000_000)


def projection_checks():
    """Check the raw-history certificate calculation, not a repair-success oracle."""
    # A0 releases exactly at boundary zero and a different role is acquired
    # there. Entry occupancy must survive the closed-window projection even
    # though post-event active occupancy contains only the new role.
    boundary_cases=[]
    for t in (0, H-1, H, H+1):
        left=max(0,t-H)
        initial=(0,0,2)
        acquired=(0,6,3)
        W={i for a,b,i in (initial,acquired) if a<=t and b>=left}
        E={0}|W|{4}|({1} if t<H else set())
        expected_window={2,3} if left==0 else {3}
        require(W==expected_window,'Entry A0 lost at release/acquisition boundary')
        require(len(E)==(5 if t<H else 4 if t==H else 3),'Distinct initial supports')
        boundary_cases.append(dict(t=t,left=left,window=sorted(W),cover=sorted(E)))
    count=0
    for horizon in range(1,8):
        gap=horizon+1
        for first in range(0,2*gap):
            for length in range(1,gap+1):
                events=[(first,first+length,3),(first+gap,first+gap+length,4),
                        (first+2*gap,first+2*gap+length,5)]
                for t in range(4*gap+2):
                    left=max(0,t-horizon)
                    W={i for a,b,i in events if a<=t and b>=left}
                    require(len(W)<=2,'Current/boundary plus one-event window')
                    Mset={t%N}
                    E={0}|W|Mset|({1} if t<horizon else set())
                    require(len(E)<=(5 if t<horizon else 4),'Union-support cardinality')
                    count+=1
    # A nonzero-rate continuing schedule visits every role, twice. This verifies
    # raw admissibility and support accounting; physical return follows the proof.
    events=[(100+k*10_000_000,106+k*10_000_000,k%N) for k in range(2*N)]
    sample_times={0,H,H+1}
    for a,b,i in events: sample_times.update((a,b,a+H,b+H,a+PERIOD+D))
    max_window=0
    for t in sorted(sample_times):
        left=max(0,t-H)
        W={i for a,b,i in events if a<=t and b>=left}
        max_window=max(max_window,len(W))
        require(len(W)<=2,'Numerical raw history')
    return dict(distinct_initial_occupant_boundary_cases=boundary_cases,
                exact_small_interval_cases=count,rotation_acquisitions=len(events),
                distinct_acquired_roles=len({i for _,_,i in events}),
                sampled_numerical_boundaries=len(sample_times),max_window=max_window,
                scope='raw-history projection checks; not a full source simulation')


def queue_checks():
    # First new command arrives early; a preceding old one arrives late and can
    # overwrite it. Bounded residence alone is not FIFO.
    deliveries={t:t for t in range(16,20)}
    deliveries[15]=19
    deliveries.update({t:t+4 for t in range(20,29)})
    held=None
    records={}
    for t in range(15,33):
        due=[s for s,d in deliveries.items() if d==t]
        for s in sorted(due,reverse=True): held=s
        records[t]=held
    require(records[20]==15 and records[23]==15 and records[24]>=16,'NonFIFO witness')
    # Quiet drain: only the boot baseline can arrive before the new class starts.
    for boot_delay,new_delay in product(range(5),repeat=2):
        require(boot_delay<16 and 16+new_delay<=20,'Quiet-drain ordering')
    require(M+5+24 < D,'Conservative return does not include generic flush')
    return dict(nonFIFO_old_hold_at_tick20=records[20],first_all_new_hold_tick=24,
                quiet_drain_delay_cases=25,steady_hold_age_bound=8,
                conservative_half_open_duration=D)


def check_lean(path):
    version=subprocess.run([str(path),'--version'],capture_output=True,text=True,encoding='utf-8')
    require(version.returncode==0 and 'version 4.33.0,' in version.stdout,'Pinned Lean required')
    source=(HERE/'Renewal.lean').read_text(encoding='utf-8-sig')
    require(not re.search(r'\b(sorry|admit|axiom|unsafe)\b',source),'Forbidden proof admission')
    names=re.findall(r'^theorem\s+(\w+)',source,re.M)
    printed=re.findall(r'^#print axioms\s+(\w+)',source,re.M)
    require(names==printed,'Incomplete axiom inventory')
    result=subprocess.run([str(path),str(HERE/'Renewal.lean')],capture_output=True,text=True,encoding='utf-8')
    require(result.returncode==0 and not result.stderr.strip(),result.stdout+'\n'+result.stderr)
    require('sorryAx' not in result.stdout and ': warning:' not in result.stdout,'Proof diagnostic')
    axioms={}
    for name in names:
        match=re.search(r"'ByzantineRecurringRenewal\."+name+r"' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",result.stdout)
        require(match is not None,'Missing dependency report: '+name)
        deps=[] if match.group(1) is None else [x.strip() for x in match.group(1).split(',') if x.strip()]
        require(set(deps)<= {'propext','Classical.choice','Quot.sound'},'Unexpected dependency')
        axioms[name]=deps
    return dict(version=version.stdout.strip(),declarations=len(names),axioms=axioms,
                scope='selected field/store/timing/count lemmas; written global induction is separate')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    mode=ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write-results',action='store_true')
    mode.add_argument('--check',action='store_true')
    ap.add_argument('--lean',type=Path,default=LEAN)
    args=ap.parse_args()
    require(sys.version_info[:2]==(3,12),'Python3.12 required')
    names=('RENEWAL.md','Renewal.lean','renewal_model.py','INSTANCE.md','SOURCE.md','ASSUMPTIONS.md')
    fingerprints=lambda:{n:sha256((HERE/n).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for n in names}
    before=fingerprints()
    physics=finite_physics()
    copies=[conditional_copy(M,strategy) for strategy in ('contact','split','selected','old_prefix')]
    copies += [conditional_copy(256,'split',q) for q in (0,16,80,96)]
    counter=[conditional_copy(256,'split',raw_at=250),conditional_copy(256,'old_prefix',omit_address=0)]
    result=dict(status='passed',scope='component physical operations and raw-history certificates; not the integrated RN/IA theorem',
                physics=physics,physical_copy_cases=copies,countercases=counter,
                projections=projection_checks(),queues=queue_checks(),lean=check_lean(args.lean))
    require(before==fingerprints(),'Sources changed during checking')
    result['sources_sha256_lf']=before
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    output=HERE/'renewal_results.json'
    if args.check: require(output.read_text(encoding='utf-8')==rendered,'Record differs; inspect before refresh')
    else: output.write_text(rendered,encoding='utf-8',newline='\n')
    print(json.dumps({'status':'passed','declarations':result['lean']['declarations'],
                      'physical_copy_cases':len(copies),'full_bits_per_copy':M,
                      'countercases':len(counter),'horizon':H,'record':output.name},sort_keys=True))

if __name__=='__main__': main()
