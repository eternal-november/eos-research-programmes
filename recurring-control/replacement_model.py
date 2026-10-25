"""Actual trimmed-mean program substitution and assembly witness checks.

This is a design-time image substitution, not an unproved live code upgrade.
The written correspondence and all-history proof remain in COMPOSITION/ASSEMBLY.
"""
from __future__ import annotations
import sys
if sys.flags.optimize:
    raise RuntimeError('Unoptimized Python is required')
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import random

HERE=Path(__file__).resolve().parent


def load_runtime():
    spec=importlib.util.spec_from_file_location('recurring_replacement_runtime',HERE/'runtime_model.py')
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    return module


def install_trimmed_builder(m):
    """Generate ordinary instructions, relocating jumps with the same assembler."""
    base=m.Assembler
    class TrimAssembler(base):
        def emit(self,op,a=0,b=0,c=0,imm=0):
            group=None
            if op==m.LOAD and a==26 and b==0 and imm==m.SORT+8*4:
                group=0
            if op==m.LOAD and a==27 and b==0 and imm==m.SORT+25*4:
                group=17
            if group is None:
                return super().emit(op,a,b,c,imm)
            start=len(self.code)
            self.li(a,0)
            for rank in range(group+5,group+12):
                super().emit(m.LOAD,14,0,imm=m.SORT+rank*4)
                super().emit(m.ADD,a,a,14)
            self.li(15,7);self.li(16,3);self.li(17,1)
            prefix='trim_'+str(a)
            self.jump(m.JSLT,prefix+'_negative',a,0)
            self.jump(m.JMP,prefix+'_magnitude')
            self.label(prefix+'_negative')
            self.li(17,-1);super().emit(m.SUB,a,0,a)
            self.label(prefix+'_magnitude')
            super().emit(m.ADD,a,a,16)
            super().emit(m.DIV,a,a,15)
            super().emit(m.MUL,a,a,17)
            return start
    original=m.PROGRAM
    m.Assembler=TrimAssembler
    m.PROGRAM,m.LABELS=m.assemble_program()
    m.CODE_BYTES,m.CODE_BITS=len(m.PROGRAM),len(m.PROGRAM)*8
    assert m.CODE_BYTES<m.ID and m.PROGRAM!=original
    return original


def trim(values):
    retained=sorted(values)[5:12]
    total=sum(retained)
    return (1 if total>=0 else -1)*((abs(total)+3)//7)


def actual_replacement_checks():
    m=load_runtime();base=m.PROGRAM
    install_trimmed_builder(m)
    rng=random.Random(67301)
    cases=0;changed=0;worst=0
    for n in range(180):
        actor=m.Machine(n%m.N,100+n)
        m.wr(actor.mem,m.DRAIN,0)
        rows=[]
        for center in (rng.randrange(-750,751),rng.randrange(-750,751)):
            group=[center+rng.randrange(-2,3) for _ in range(17)]
            for index in rng.sample(range(17),n%6):
                group[index]=rng.choice((-4000,4000,0))
            rows.extend(group)
        actor.capture([m.packet(x) for x in rows])
        action=actor.step()
        expected=tuple(m.correction(trim(rows[g:g+17])) for g in (0,17))
        old=tuple(m.correction(sorted(rows[g:g+17])[8]) for g in (0,17))
        assert action.u==expected and not action.timed_out
        assert action.word_work<=m.WORD_LIMIT
        assert m.rd(actor.mem,m.PHASE)==(101+n)%m.P
        worst=max(worst,action.word_work);changed+=expected!=old;cases+=1
    assert changed>0
    admitted_rows=[99]*8+[101]*9
    assert trim(admitted_rows)==100 and sorted(admitted_rows)[8]==101
    assert m.correction(101)==76 and m.correction(100)==75
    # Each retained rank is in the honest interval for <=5 arbitrary rows.
    # Exhaust these extremal counts; the general ranked-count proof is written.
    rank_cases=0
    for bad in range(6):
        for low in range(bad+1):
            for center in (-750,0,750):
                values=[-4000]*low+[center-2]*(17-bad)+[4000]*(bad-low)
                ordered=sorted(values)
                assert all(center-2<=v<=center+2 for v in ordered[5:12])
                assert abs(F(trim(values))-F(sum(ordered[5:12]),7))<=F(3,7)
                rank_cases+=1
    image=m.image_and_phase_checks()
    # The same code-copy interface actually consumes the substituted code.
    donor=m.Machine(7,13*m.S+4)
    for bit in range(m.CODE_BITS):
        m.wr(donor.mem,m.PHASE,13*m.S+4+bit)
        out=donor._execute(0,m.LABELS['after_fields'])
        assert out.fields[1]==m.Field(1,13,bit,2*m.getbit(donor.mem,bit)-1)
    extra_instructions=(len(m.PROGRAM)-len(base))//8
    bound=154528+32*extra_instructions
    assert bound<=m.WORD_LIMIT and worst<=bound
    # Full original CPU cap is already paid, so new nominal work adds no stock debit.
    error=F(2,1000)+F(3,7000)+22*F(1,10**8)*F(52441,20000)
    assert error<F(3,1000)
    # This replacement has a five-row, not eight-row, robust interface.
    eight_bad=[4000]*8+[0]*9
    assert sorted(eight_bad)[8]==0 and trim(eight_bad)>0
    return dict(actual_vm_cases=cases,different_command_cases=changed,
        rank_corner_cases=rank_cases,all_actual_code_copy_bits=m.CODE_BITS,
        base_program_bytes=len(base),replacement_program_bytes=len(m.PROGRAM),
        extra_nonloop_instructions=extra_instructions,uniform_word_bound=bound,
        observed_maximum_word_work=worst,information_effect_error=str(error),
        image=image,eight_bad_counterexample={'median':0,'trimmed':trim(eight_bad)},
        program_sha256=sha256(m.PROGRAM).hexdigest(),
        source_admitted_difference={'true_milliunits':100,'rows':admitted_rows,
            'median_command_milliunits':76,'trimmed_command_milliunits':75},
        scope='actual local replacement and finite image interface, not a full rotating source simulation')


def rotating_history_checks():
    m=load_runtime();D=m.M+30;H=m.P+D
    previous=None;mingap=None;cases=0
    for k in range(3*m.N):
        i=k%m.N;j=(i+1)%m.N;t=6*k*m.P+j*m.S+10
        own_start=t-10-m.S
        assert own_start%m.P==i*m.S
        assert t-(own_start+D)==44
        if previous is not None:
            gap=t-previous
            mingap=gap if mingap is None else min(mingap,gap)
            assert gap>10**7 and gap>H+6
        next_start=own_start+m.P
        assert next_start>t+6 and next_start+D<t+H
        # A finite persistent hostile program targets the actual next repair.
        a=m.Assembler();a.li(0,0);a.li(1,-2000);a.emit(m.SETU,1,1)
        a.li(2,-1);a.emit(m.SETG,2);a.li(3,j)
        a.field(0,0,3,0,2);a.field(1,0,3,0,2)
        a.li(4,0x80000000);a.emit(m.STORE,4,0,imm=m.IMAGE_BYTES-4);a.emit(m.HALT)
        actor=m.Machine(i);actor.mem[:len(a.finish())]=a.finish()
        action=actor.step()
        assert action.fields==[m.Field(0,j,0,-1),m.Field(0,j,0,-1)]
        assert action.u==(-2000,-2000) and action.g==-1
        assert m.getbit(actor.mem,m.SIGMA_BIT)==1
        assert action.word_work<=m.WORD_LIMIT
        previous=t;cases+=1
    return dict(cases=cases,minimum_gap=mingap,restored_useful_lead=44,
                roles=m.N,return_horizon=H,
                scope='periodic formula and actual hostile commands; usefulness follows the written all-history proof')


def boundary_arithmetic():
    T=10**9;growth=F(1,10**9)
    lower=1+T*growth+T*(T-1)*growth*growth/2
    assert lower>2 and T<2**32
    drift=F(52441,20000)
    assert 4*F(1,10**8)*drift<F(1,20)
    isolated=sum(map(F,(476,8,68,34,272,34)))+F(34,5)+F(34*4096,10**6)
    assert isolated==F(14045926,15625)<901
    joint=748+34+34+66+33
    assert joint==915 and 143*(joint-901)>2000 and 200<65536-10
    return {'delayed_ADC_ticks':T,'paired_difference_lower':str(lower),
        'four_tick_drift_below_factive_threshold':True,
        'one_optional_publisher_upper_cost':str(isolated),
        'both_actual_lower_cost_selected_selector_price_one':joint,
        'joint_cannot_complete_ticks':143,
        'scope':'exact numerical margins for written source witnesses, not a full publisher implementation'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    modes=p.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args=p.parse_args()
    names=('replacement_model.py','runtime_model.py','INSTANCE.md','COMPOSITION.md','ASSEMBLY.md','BOUNDARIES.md')
    def hashes():
        return {n:sha256((HERE/n).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for n in names}
    before=hashes()
    record={'status':'passed','replacement':actual_replacement_checks(),
            'rotation':rotating_history_checks(),'boundaries':boundary_arithmetic(),
            'sources_sha256_lf':before}
    assert hashes()==before,'Sources changed during checking'
    rendered=json.dumps(record,sort_keys=True,indent=2)+'\n'
    path=HERE/'replacement_results.json'
    if args.write:path.write_text(rendered,encoding='utf-8',newline='\n')
    else:assert path.read_text(encoding='utf-8')==rendered,'Record differs; inspect before refresh'
    print(json.dumps({'status':'passed','cases':record['replacement']['actual_vm_cases'],
        'rotation_cases':record['rotation']['cases'],'program_bytes':record['replacement']['replacement_program_bytes']}))


if __name__=='__main__':main()
