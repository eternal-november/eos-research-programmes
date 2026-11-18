"""Exact source substitutions for the conditional regional safety/service proof."""
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
FROZEN = "fb85a7606f45e52d0cd48e023ab9776dd526640c"
B_POINT = "e92a77636f43ad6d4ac22cd263f7f32eea5b504b"
CC = "20d03c97c23c99f81bf17142405d6e838058f5b7"
SOURCE = "theories-and-designs/byzantine-control/"
CC_PREFIX = "projects/contextual-composition/"
THEOREMS = {
    "applications/verified-neural-control/Verified_Neural_Control_and_Moving_Safety_Fibres.tex":
        "44d85da365b76b5b40cdee28017aca676b5dafafdb95e3549886c436a5e37608",
    "applications/quantitative-doctrine/Quantitative_Doctrine_Descent_and_Capability_Refinement.tex":
        "2b8c29b804b6be3ea1a61a4725d2d363a9a16225b9efdaa4a0a0c3fab85d4c7d",
}


def check(ok, reason):
    if not ok:
        raise ValueError(reason)


def immutable(repo, revision, path):
    return subprocess.check_output(["git", "show", revision+":"+path], cwd=repo).decode("utf-8-sig").replace("\r\n","\n")


def serial(value):
    if isinstance(value, Q):
        return str(value)
    raise TypeError(type(value))


def verify_theorem_text(repo):
    for path, expected in THEOREMS.items():
        actual = immutable(repo, CC, CC_PREFIX+path)
        check(sha256(actual.encode()).hexdigest()==expected, "The imported theorem text changed: "+path)


def image_interval(a, bias, radius):
    endpoints = [-a*radius+bias, a*radius+bias]
    return min(endpoints), max(endpoints)


def tracker(command_error, m, bad, export):
    gain = Q(1,100)
    slew = Q(1,2500000)
    eta = Q(1,25)
    fixed = command_error+slew/gain
    check(0<fixed<eta, "Command error leaves no room for lag")
    def decay(t):
        return (1+gain*t/10)**(-10)
    def error(t):
        return fixed+(2-fixed)*decay(t)
    def lower_output(t):
        return Q(3,10)-Q(13,10)*decay(t)
    # Strictly a sufficiency threshold of this exact rational ten-block estimate.
    threshold = next(t for t in range(10001) if error(t)<=eta)
    early_service = lower_output(threshold)*(1-Q(bad,m))-Q(export,m)
    check(error(threshold-1)>eta and early_service-Q(1,10)>Q(1,10), "Shorter conditional certificate changed")
    epsilon = 2*decay(10000)
    check(command_error+slew/gain+epsilon<eta, "Published 10000q supplier fails")
    # Physical retaining coordinate has signed error. Use shifted unit interval
    # u=(e/radius+1)/2, on which the single fixed feature ReLU(u) is identity.
    # Exact face pullbacks for a deliberately offset segment (a=1/2).
    for a in (Q(0), Q(1,2), Q(1)):
        for z in (-eta, Q(0), eta, (1-a)*eta):
            lo,hi=image_interval(a,z,eta)
            W=a
            bias=(1-a+z/eta)/2
            check((0<=bias and W+bias<=1)==(-eta<=lo and hi<=eta)
                  ==(a*eta+abs(z)<=eta), "Shifted-coordinate face mismatch")
    return dict(command_error=command_error,slew=slew,gain_floor=gain,
                asymptotic_error=fixed,eta=eta,epsilon=epsilon,
                at_10000_conservative=command_error+slew/gain+epsilon,
                smallest_integer_for_ten_block_error_bound=threshold,
                preceding_bound=error(threshold-1),certified_error=error(threshold),
                individual_range_floor_at_threshold=lower_output(threshold),
                regional_service_at_threshold=early_service,
                net_after_point_one_at_threshold=early_service-Q(1,10))


def derive():
    paths = {
        "A-world":(FROZEN,"local-control/primary_assembly_results.json"),
        "A-gate":(B_POINT,"portability/GATE-SOURCE-COMPLETION.md"),
        "B-world":(B_POINT,"portability/regional_coupling_results.json"),
        "B-publication":(B_POINT,"portability/publication_timing_results.json"),
        "B-entry":(B_POINT,"portability/THRESHOLD-INITIALIZATION.md"),
        "B-phase10":(B_POINT,"portability/COMMON-RESPONSE.md"),
        "RC":(B_POINT,"portability/TRACKER-ENVELOPE.md"),
    }
    texts={name:immutable(REPO,rev,SOURCE+path) for name,(rev,path) in paths.items()}
    A=json.loads(texts["A-world"])["world"]
    B=json.loads(texts["B-world"])["world"]
    publication=json.loads(texts["B-publication"])["world"]["tracker"]
    m=int(B["m"])
    M=int(B["M"])
    b,p=6,1
    W=b+p*M
    check(m==int(A["regional_population"])==12*(6+2**98)+2 and M==int(A["raw_site_export"])==2**98,
          "Actual population or physical export changed")
    upper=Q(21,25)*(1-Q(b,m))-Q(W,m)
    lower=Q(9,25)+Q(W,m)
    check(upper==Q(A["upper_flow_lower"])==Q(B["upper"]) and lower==Q(A["lower_flow_upper"])==Q(B["lower"]),
          "Regional aggregate no longer matches the common scale")
    cases={"A-prime":dict(delta=Q(A["command_error"]),upper=Q(6406,10000),lower=Q(5594,10000)),
           "B":dict(delta=Q(publication["command_error"]),upper=Q(B["robust_upper_requirement"]),lower=Q(B["robust_lower_requirement"]))}
    families={}
    for name,inputs in cases.items():
        tr=tracker(inputs["delta"],m,b,W)
        upper_margin=upper-inputs["upper"]
        lower_margin=inputs["lower"]-lower
        check(upper_margin>0 and lower_margin>0,"Lost strict regional collar")
        families[name]=dict(tracker=tr,upper_disturbance=inputs["upper"],lower_disturbance=inputs["lower"],
                            upper_margin=upper_margin,lower_margin=lower_margin)
    check(families["A-prime"]["upper_margin"]==Q(A["upper_inward_margin"])
          and families["A-prime"]["lower_margin"]==Q(A["lower_inward_margin"])
          and families["B"]["upper_margin"]==Q(B["robust_upper_margin"])
          and families["B"]["lower_margin"]==Q(B["robust_lower_margin"]),"Disturbance rows changed")
    epsilon=2*Q(1,11**10)
    service=(Q(3,10)-epsilon)*(1-Q(b,m))-Q(W,m)
    check(service==Q(B["actual_effector_service_lower"]) and service-Q(1,10)==Q(B["conservative_net_service_lower"])
          and service-Q(1,10)>Q(1,10),"Service or normalization changed")
    # Old A exact-.3 output is justified at its warm initial keeper. After a
    # general handoff, the same conservative finite residual suffices for G2.
    check(Q(A["service_lower"])-service==epsilon*(1-Q(b,m)),"Unexpected A output range premise")
    displacement=50000*Q(2,10**7)
    check(displacement==Q(A["commissioning_displacement"])==Q(B["initial_50000q_displacement"])<Q(1,20),
          "Startup can consume the initial spatial margin")
    check("11/16" in texts["B-phase10"] and "33/32" in texts["B-phase10"], "Phase-10 factual projection changed")
    return dict(source_bindings={name:dict(commit=rev,path=SOURCE+path,sha256_lf=sha256(texts[name].encode()).hexdigest())
                                 for name,(rev,path) in paths.items()},
                imported_repository_commit=CC,imported_sha256_lf=THEOREMS,
                population=m,ordinary_bad_hosts=b,physical_sites=p,hostile_flow=M,total_loss_and_export=W,
                upper_face_removal_lower=upper,lower_face_removal_upper=lower,actual_service_lower=service,
                B_net_after_interzone_bound=service-Q(1,10),commissioning_displacement=displacement,
                families=families,scope="Conditional regional output, world and service proof on proper source interfaces.",
                unconditional_family_admission=False)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--research-repo",type=Path)
    args=parser.parse_args()
    if args.research_repo is not None:
        verify_theorem_text(args.research_repo)
    content=json.dumps(derive(),sort_keys=True,indent=2,default=serial)+"\n"
    target=HERE/"service_fibres_results.json"
    if args.write:
        target.write_text(content,encoding="utf8",newline="\n")
    else:
        check(target.read_text(encoding="utf8")==content,"Service fibre record differs")
    print("regional service fibres reproduced")


if __name__=="__main__":
    main()
