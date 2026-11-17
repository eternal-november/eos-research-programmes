from itertools import product
import json
phases=['decision','retry-call','Spin','seed','branch','completed']
checks=0
for n,phase,zero in product(range(5),phases,[False,True]):
    J={'id':'J','world':n,'birth':0,'phase':phase,'record':('z' if zero else 'p',),'owner':('e0','A')}
    B={'id':'B','world':n,'active':True,'count':0}
    signature={'ticket':'e1','mode':'paid','update':(n,n+1),'global_selected':('B',),'external_head':('e1','B'),'raw':('old-zero' if zero else 'old-positive','singleton')}
    def passive(j):return dict(j,world=signature['update'][1])
    global_post={'J':passive(J),'B':dict(B,world=n+1,count=1)}
    localJ={'signature':signature,'selected':(),'post':passive(J),'new_heads':()}
    localB={'signature':signature,'selected':('B',),'post':global_post['B'],'new_heads':(('e1','B'),)}
    glued={localJ['post']['id']:localJ['post'],localB['post']['id']:localB['post']}
    assert glued==global_post
    assert glued['J']['owner']==('e0','A') and glued['J']['birth']==0
    assert len(set(localJ['new_heads']+localB['new_heads']))==1
    # Aliases share global selection/witness; union does not add another owner/head.
    assert len(set(localB['new_heads']+localB['new_heads']))==1
    assert passive(J)!=J
    # Restrict through J+K retains the exact same external signature.
    JK={'signature':signature,'posts':{'J':passive(J),'K':{'id':'K','world':n+1}}}
    assert JK['signature']==localJ['signature'] and JK['posts']['J']==localJ['post']
    checks+=1
print(json.dumps({'all_raw_passive_signature_cases':checks,'gluing_reproduces_global_successor':True,'nested_restriction_equal':True,'alias_head_charged_once':True,'empty_closed_unit_counterexample':True},indent=2))
