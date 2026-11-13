import random
from ladder_model import Job

def pair_workload(n,seed,roomy):
    rng=random.Random(seed)
    edges=sorted({tuple(sorted((i,j))) for i in range(n) for j in [i^1]+([i+2] if i+2<n else [])})
    chosen=[rng.choice(edges)]
    used=set(chosen[0])
    while len(chosen)<3:
        options=[e for e in edges if e not in chosen and used.intersection(e)]
        e=rng.choice(options);chosen.append(e);used.update(e)
    return tuple(Job(2+2*k,2+2*k+(3 if roomy else 1),(edge,edge[::-1])) for k,edge in enumerate(chosen))

PROTOCOL=dict(sizes=[4,6,8], seeds=[731,947], powers=[2,4], roomy=[False,True],
              extra_energy=[0,1,3], max_nodes=5000,max_seconds=20.0,
              job_releases=[2,4,6],productive_energy=12,
              negative_label='NO_UNIFORM_GUARANTEE',measurement='end_of_slot',
              physics='twice_load_i=u_i+previous_u_parent_i <=3',
              probe_amplitude=1,productive_amplitude=2,
              main_method='common_exact_symbolic_planner',
              paired_checkers=['local','smart_global','full_scope'],
              repetitions=3)

def all_cases():
    for n in PROTOCOL['sizes']:
      for seed in PROTOCOL['seeds']:
       for power in PROTOCOL['powers']:
        for roomy in PROTOCOL['roomy']:
         for extra in PROTOCOL['extra_energy']:
          yield dict(id=f'n{n}_s{seed}_p{power}_r{int(roomy)}_e{extra}',n=n,seed=seed,power=power,roomy=roomy,energy=12+extra)

RICH_PROTOCOL=dict(sizes=[4,6],seeds=[731,947],powers=[2,4],roomy=[False,True],
                   energy=15,job_releases=[2,5],routes_per_job=3,stages_per_job=3,
                   max_nodes=5000,max_seconds=20.0)
def rich_workload(n,seed,roomy):
    rng=random.Random(seed+170000)
    jobs=[]
    for k in range(2):
        col=rng.randrange(n//2-1)
        ring=[2*col,2*col+1,2*col+3,2*col+2]
        shift=rng.randrange(4);ring=ring[shift:]+ring[:shift]
        a,b,c,d=ring
        routes=((a,b,c),(c,b,a),(a,d,c))
        release=2+3*k
        jobs.append(Job(release,release+(4 if roomy else 2),routes))
    return tuple(jobs)
def rich_cases():
    for n in RICH_PROTOCOL['sizes']:
      for seed in RICH_PROTOCOL['seeds']:
       for power in RICH_PROTOCOL['powers']:
        for roomy in RICH_PROTOCOL['roomy']:
          yield dict(id=f'rich_n{n}_s{seed}_p{power}_r{int(roomy)}',family='rich',n=n,seed=seed,power=power,roomy=roomy,energy=15)
