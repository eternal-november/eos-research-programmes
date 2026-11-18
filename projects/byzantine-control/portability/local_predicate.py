"""All-raw decidability and actual local comparison at a fixed B maintenance site."""
import argparse
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import subprocess

import input_lifecycle as raw
import legacy_realization as legacy
import parent_realization as parent
import threshold_design as design
import threshold_incidence_model as incidence
import threshold_program_model as program


HERE=Path(__file__).resolve().parent
SOURCE_PIN="e92a77636f43ad6d4ac22cd263f7f32eea5b504b"
BANK,_=legacy.module_at(SOURCE_PIN,"portability/shared_bank_charging.py","_local_predicate_bank")
M=12*(6+2**98)+2
RECEIVER=100
TARGET=0
SKIP=14
IMPORT_PREFIX="projects/contextual-composition/foundations/native-whole-scope-feedback/historical-diagrams-and-resources/"
IMPORTS={
    "control/Decentralized_Resource_Realization.tex":(
        "30d6f05bbb1da19b0aa9560b2a742877b599afe4","0073155adf50e9f77671f7fab135e11f5ccd73fe3eafd739c2c55c3f9eb2638c"),
    "dynamic/Universal_Total_Historical_Repair_Resources.tex":(
        "ede5af9e9ef3c2134ebf95513db48af98fb484e3","1e3d699d30e43f2ade51e42cd1c5ae5446cd6fc50a46973d51b5a652471c2fd9"),
    "dynamic/Calibrated_Online_Repair_Resources.tex":(
        "ede5af9e9ef3c2134ebf95513db48af98fb484e3","971a84f6be6cb50b5c543b98d77ffefcebed2d352fa133df3134818507d7c2b6"),
}


def need(ok,why):
    if not ok:
        raise ValueError(why)


def minimum_tokens(mask, pair):
    return mask.bit_count()-int(mask&pair==pair)


def classify(positive, width, pair, budget):
    all_rows=(1<<width)-1
    low=minimum_tokens(positive,pair)
    high=minimum_tokens(all_rows^positive,pair)
    return tuple(h for h,cost in ((0,low),(1,high)) if cost<=budget)


def geometry():
    _host,members=incidence.maintenance_group(M,RECEIVER,TARGET)
    providers=tuple(o for o,_ in members)
    raw_pair=raw.islands.installed_pair(M,RECEIVER)
    positions=tuple(providers.index(o) for o in raw_pair)
    need(providers==tuple(range(81,96)) and raw_pair==(83,86) and positions==(2,5),
         "Changed target table or shared incident")
    events=[("source",o) for o in providers]+[("lane",RECEIVER,o) for o in providers]
    events += [("primary",RECEIVER),("execution",RECEIVER),("reset-root",providers[1])]
    singleton=tuple(frozenset(raw.support(M,RECEIVER,providers,e)) for e in events)
    need(all(len(row)==1 for row in singleton) and set(singleton)>={frozenset({j}) for j in range(15)},
         "Singleton opportunities changed")
    pair=raw.support(M,RECEIVER,providers,("pair",RECEIVER))
    need(pair==set(positions),"Wrong receiver-local pair")
    return members,sum(1<<k for k in pair)


def verify_minimum_masks(pair):
    """Solve the finite physical set-cover recurrence without the closed formula."""
    masks=[1<<j for j in range(15)]+[pair]
    cost=[0]
    for errors in range(1,1<<15):
        best=1+min(cost[errors&~event] for event in masks if errors&event)
        need(best==minimum_tokens(errors,pair),"Finite footprint assembly disagrees with min cost")
        cost.append(best)
    return len(cost)


def row_profiles(width,pair,limit):
    histogram=Counter()
    reachable=0
    for positive in range(1<<width):
        possible=classify(positive,width,pair,limit)
        histogram[len(possible)]+=1
        if width==14 and limit==6 and possible:
            singles=(positive & ~pair).bit_count()
            decision=int(singles+int(positive&pair==pair)>=7)
            need(possible==(decision,),"Implemented fourteen-row rule fails a reachable observation")
            reachable+=1
    return dict(zero=histogram[0],unique=histogram[1],ambiguous=histogram[2],compared_to_rule=reachable)


def extra_source(positions):
    """Ordinary finite source: one typed/paid physical call per bank and kept origin."""
    lines=["def fixed_row14(key, threshold):","    singles = 0"]
    for slot in range(14):
        lines.extend([f"    left = fast_cmp({slot}, 0, key, threshold)",
                      f"    right = fast_cmp({slot}, 1, key, threshold)",
                      "    hit = left or right"])
        if slot in positions:
            lines.append(f"    pair_{positions.index(slot)} = hit")
        else:
            lines.append("    singles += hit")
    lines += ["    combined = pair_0 and pair_1","    return singles + combined >= 7","",
              "def fixed_permission14(base, side):",
              "    if LOAD_MARGIN > 1000 or ISOLATION_MARGIN > 200:","        return 0",
              "    target = (base - TARGET_BASE) // TARGET_WORDS",
              "    key = 3 + target * FAST_TARGET_KEYS + VIEW_WORDS",
              "    load = fixed_row14(key + side, 1000 - LOAD_MARGIN)",
              "    gap = fixed_row14(key + 2 + side, 200 - ISOLATION_MARGIN)",
              "    return load and gap",""]
    return "\n"+"\n".join(lines)


class TextSource:
    def __init__(self,body):
        self.body=body
    def read_text(self,encoding):
        return self.body


def compiled_inputs():
    isa=program.load_isa()
    c0=program.compile_program(isa,design.design(isa))
    original=isa.SOURCE
    text=original.read_text(encoding="utf-8-sig")
    need(text==legacy.text_at(SOURCE_PIN,"portability/threshold_program_source.py"),"Compiled provider image changed")
    extension=extra_source((2,5))
    try:
        isa.SOURCE=TextSource(text+extension)
        changed=program.compile_program(isa,design.design(isa))
    finally:
        isa.SOURCE=original
    return isa,c0,changed,extension


class ReceiverRows:
    def __init__(self,isa,c,bank,members,load_positive,ledgers):
        self.selector=legacy.GroupSelector(M,RECEIVER)
        self.ports=program.ports_class(isa)(c)
        self.reader_bank=bank
        self.lanes={}
        self.payers=[]
        self.reads=[]
        for slot,(origin,target_ordinal) in enumerate(members):
            payer=ledgers[origin]
            self.payers.append(payer)
            captures={name:raw.SharedCapture((origin,RECEIVER,bank),name,payer)
                      for name in ("primary","auxiliary")}
            for serving in (0,1):
                lane=raw.RawLane(M,raw.LaneId(origin,serving,RECEIVER,bank),payer,captures)
                self.lanes[(origin,serving)]=lane
                # One genuine serving source bank. The removed row has two
                # unavailable actual records. All nonremoved gap rows qualify.
                if serving==1 and slot!=SKIP:
                    for extra,value in ((0,125 if slot in load_positive else 1500),(2,0)):
                        native_key=3+target_ordinal*50+c.constants["VIEW_WORDS"]+extra
                        mapped=3+c.constants["VIEW_WORDS"]+extra
                        need(lane.decoder.decode(native_key)==("primary" if slot==0 else "auxiliary",mapped),
                             "Actual native publication did not map to this served target key")
                        need("frame" in lane.offer_frame(native_key,value) and lane.read(mapped)==value,
                             "Framed receipt did not commit")
        self.before=sum(p.spent for p in self.payers)
    def advance(self,cpu):
        pass
    def perform(self,name,args,cpu):
        if name!="fast_cmp":
            return self.ports.perform(name,args,cpu)
        slot,serving,key,threshold=args
        found,work=self.selector.select(key,slot,serving)
        need(found is not None and work==6976,"Actual private group selection is unavailable")
        origin,actual_source_bank,role=found
        lane=self.lanes[(origin,actual_source_bank)]
        actual=lane.private_capture(key,role)
        self.reads.append((slot,actual_source_bank,key))
        return int(actual<=threshold)


def donor_ledgers(members):
    cap=Q(json.loads(legacy.text_at(SOURCE_PIN,"portability/threshold_gate_source_results.json"))["costs"]["upstream_capacity"])
    return {origin:raw.SourceWork(origin,cap,1<<40) for origin,_ in members}


def run_paid(isa,c,proc,bank,members,load_positive,ledgers):
    # All other E chargers are full or physically ineligible on this short
    # zero-inflow interval. This is a CPU-only projection of a real joint bank.
    cap=int(json.loads(legacy.text_at(SOURCE_PIN,"portability/parent_realization_results.json"))["cost_bounds"]["actual_bank_capacity"])
    E=BANK.OperatingBank((RECEIVER,bank),cap,1<<59)
    cpu=BANK.FramedParent(isa,c,bank=E)
    bus=BANK.JointCharge(E,cpu,(),parent.DELTA)
    rows=ReceiverRows(isa,c,bank,members,load_positive,ledgers)
    cpu.enter(proc,(c.constants["TARGET_BASE"],0))
    calls=0
    while not cpu.halted and calls<10000:
        bus.flow_full_delivery(2*parent.DELTA,source_powered=True)
        launched=cpu.recharge() and cpu.launch()
        calls+=1
        if not launched:
            need(cpu.halted,"Pending or unfunded request during the qualified CPU chart")
            break
        # No recharge into the occupied parent. Native service/return fits
        # this suffix at the ordinary clock. Captures occur at the IO event.
        bus.flow_full_delivery(Q(1,2**26)-2*parent.DELTA,source_powered=True)
        need(cpu.complete(rows) is True,"Paid compare did not retire")
    bus.balance()
    need(cpu.halted and cpu.C==c.image and cpu.code_writes==0 and E.supplied==calls*parent.PARENT,
         "Finite emitted code or actual CPU power accounting failed")
    steps=cpu.steps
    return dict(result=cpu.result(),retired=steps,CPU_E_including_harness_terminal=int(E.supplied),
                actual_retired_CPU_budget=steps*parent.PARENT,CPU_native_peak_per_instruction=int(cpu.max_total_work),
                nominal_elapsed_upper_q=str(cpu.nominal_work_time_upper),comparisons=len(rows.reads),
                source_affine_U_for_actual_captures=int(sum(p.spent for p in rows.payers)-rows.before),
                slots=sorted({x for x,_,_ in rows.reads}),reader_bank=bank)


def results():
    members,pair=geometry()
    verified=verify_minimum_masks(pair)
    profiles={str(w)+"/"+str(lim):row_profiles(w,pair,lim) for w,lim in ((15,6),(15,7),(14,6),(13,6))}
    # Dropping a member of Q changes the induced graph: no doubleton
    # remains on those thirteen kept rows. Six singletons fit majority.
    one_pair_member=sum(any((k if truth==0 else (8191^k)).bit_count()<=6
                            for truth in (0,1)) for k in range(8192))
    need(one_pair_member==8192,"Thirteen-singleton alternative failed")
    need(profiles["14/6"]["ambiguous"]==0 and profiles["13/6"]["ambiguous"]==924
         and profiles["15/7"]["ambiguous"]==3432,"Sharp all-raw bound failed")
    # In the thirteen visible rows 0..12, the two contexts below cause the
    # same word at an individual receiver. Every named raw fibre is retained.
    ones={0,1,2,3,4,5,6}
    other=set(range(13))-ones
    mask=sum(1<<j for j in ones)
    need(classify(mask,13,pair,6)==(0,1) and len(ones-{2,5})+1==6 and len(other)==6,
         "Two six-token explanations should be valid")
    witnesses={"visible_ones":sorted(ones),"omissions":[13,14],"for_h0_pair_sources":[83,86],
               "for_h0_singleton_sources":[members[j][0] for j in sorted(ones-{2,5})],
               "for_h1_singleton_sources":[members[j][0] for j in sorted(other)]}
    isa,pinned,extension,added=compiled_inputs()
    # Seven good ones among fourteen, all seven zeros in the union of the
    # installed two-origin island and five singleton footprints. The 15th
    # is a separate fixed unavailable observation, outside that support.
    bad={0,1,2,3,4,5,6}
    positive=set(range(14))-bad
    arms={}
    for name,c,proc in (("pinned",pinned,"permission"),("illustrated",extension,"fixed_permission14")):
        ledgers=donor_ledgers(members)
        arms[name]=[run_paid(isa,c,proc,bank,members,positive,ledgers) for bank in (0,1)]
    need(all(row["result"]==0 and row["comparisons"]==60 for row in arms["pinned"])
         and all(row["result"]==1 and row["comparisons"]==56 for row in arms["illustrated"]),
         "Real compiled local permission did not separate the unavailable input")
    # A false plateau with six class-cost false positives (including the
    # coupled apertures) still cannot pass the fourteen-row guard.
    refused=run_paid(isa,extension,"fixed_permission14",0,members,bad,donor_ledgers(members))
    need(refused["result"]==0,"Alternative falsely accepts")
    return dict(source=SOURCE_PIN,physical_support_masks_checked=verified,imported_theorems=IMPORTS,receiver=RECEIVER,target=80,target_ordinal=0,
                providers=[x for x,_ in members],pair_mask=pair,profiles=profiles,
                thirteen_with_only_one_paired_origin_decodable=one_pair_member,
                thirteen_row_separation=witnesses,old_and_alternative=arms,false_plateau=refused,
                existing_instructions=len(pinned.nodes),illustration_instructions=len(extension.nodes),
                installed_C_capacity=len(pinned.image),pinned_image=program.hash_text(json.dumps(pinned.image)),
                illustration_image=program.hash_text(json.dumps(extension.image)),new_helper_source_sha256=program.hash_text(added),
                condition="Source-local one fixed maintenance group, one unavailable uncharged origin and all-raw mask envelope; source global H/service not derived.")


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--research-repo",type=Path)
    args=parser.parse_args()
    if args.research_repo:
        for path,(revision,digest) in IMPORTS.items():
            body=subprocess.check_output(["git","show",revision+":"+IMPORT_PREFIX+path],cwd=args.research_repo).decode().replace("\r\n","\n")
            need(sha256(body.encode()).hexdigest()==digest,"Imported theorem point changed")
    data=json.dumps(results(),indent=2,sort_keys=True)+"\n"
    target=HERE/"local_predicate_results.json"
    if args.write:
        target.write_text(data,encoding="utf8",newline="\n")
    else:
        need(target.read_text(encoding="utf8")==data,"Comparison evidence changed")
    print("all-raw local predicate and both paid reader paths reproduced")


if __name__=="__main__":
    main()
