"""Certified negative frames and a masked image from a civil crossing."""
from fractions import Fraction as Q
from itertools import product
from hashlib import sha256
import json,math

S=40             # pixels per unit
W=24             # half-width of coverage slab, in pixels
YMAX=48
RAD=4

def render(positions,cover='full'):
    """Orthographic projection, plain non-identifying disks, integer raster."""
    img=bytearray()
    for y in range(-YMAX,YMAX+1):
        for x in range(-W,W+1):
            exposed=cover=='full' or (cover=='upper' and y>=0) or (cover=='lower' and y<0)
            bright=exposed and any((Q(x)-u*S)**2+(Q(y)-v*S)**2<=RAD**2
                                  for u,v in positions)
            img.append(240 if bright else 0)
    return bytes(img)

def certificate(schedule,V,width):
    # All source entries already selected as validated negative exposure times.
    # Endpoints must also be known outside the closed band at their anchors.
    return bool(schedule) and all((b-a)*V<=2*width
        for a,b in zip(schedule,schedule[1:]))

def blur_at(t,swap,y):
    # Each unit of time moves no more than one unit of space.
    x=Q(-4,5)+min(max(t-Q(1,5),Q(0)),Q(8,5)) if swap else Q(-4,5)
    ypos=y*min(Q(1),5*t,5*(2-t)) if swap else 0
    return ((x,ypos),(-x,-ypos))

def detector(img):
    return 'negative' if max(img)==0 else 'objects'

def check_row(trace):
    out=[]
    for exposure,mode,status,positions in trace:
        data=render(positions,mode) if status!='dropped' else None
        dec=detector(data) if data is not None else 'unavailable'
        valid=dec=='negative' and status=='valid' and mode=='full'
        out.append((exposure,dec,valid,
                    sha256(data).hexdigest()[:12] if data is not None else None))
    return tuple(out)

def max_with_loss(h,loss,jitter,common):
    return (loss+1)*h+(0 if common else 2*jitter)

def direct_stamps(period,r,j,common):
    # Direct enumeration of all endpoints, scheduled apart by r+1 frame
    # periods. Intermediate frames are allowed to be lost.
    choices=(-j,j) if j else (0,)
    return max((r+1)*period+v-u for u,v in product(choices,repeat=2)
        if not common or u==v)

def main():
    times=(Q(0),Q(1),Q(2))
    side=Q(9,50)
    full_ok=lambda t,flip: (t,'full','valid',blur_at(t,flip,side))
    if_intact=[check_row([full_ok(t,s) for t in times]) for s in (0,1)]
    assert if_intact[0][1][1:3]==('negative',True)
    assert if_intact[1][1][1:3]==('objects',False)
    # Known discarded frame leaves exactly equal usable observation data.
    broken=[]
    full_but_covered=[]
    for swap in (0,1):
        selected=[full_ok(t,swap) for t in times]
        selected[1]=(times[1],'full','dropped',blur_at(times[1],swap,side))
        broken.append(check_row(selected))
        # A full-size decoded payload can still carry no usable photons.
        selected[1]=(times[1],'blocked','valid',blur_at(times[1],swap,side))
        full_but_covered.append(check_row(selected))
    assert broken[0]==broken[1]
    assert full_but_covered[0]==full_but_covered[1]
    assert full_but_covered[0][1][1:] == ('negative',False,if_intact[0][1][3])
    assert certificate(times,1,Q(3,5))
    assert not certificate((Q(0),Q(2)),1,Q(3,5))
    sequence=[blur_at(Q(i,80),1,side) for i in range(161)]
    assert {
       tuple((p[0],p[1]) for p in sorted(z)) for z in (sequence[0],sequence[-1])
    }=={tuple(sorted(blur_at(Q(0),0,side)))}
    assert all((a[0]-b[0])**2+(a[1]-b[1])**2>=Q(9,100) for a,b in sequence)
    assert all(sum((a-b)**2 for a,b in zip(before[0],after[0]))<=Q(1,80)**2
               for before,after in zip(sequence,sequence[1:]))
    # Synchronized shards are needed for complete cross-section evidence.
    # Two negatives in consecutive *different* half-views are not enough
    # unless a source constraint ties motion to the unchanging covered lane.
    upper=render(((Q(0),-side),),'upper')
    lower=render(((Q(0),side),),'lower')
    assert detector(upper)==detector(lower)=='negative'
    assert detector(render(((Q(0),side),),'full'))=='objects'
    checks=0
    for h,b,j,c in product((Q(1,4),Q(1,2),Q(1),Q(3,2)),range(7),
                          (Q(0),Q(1,16),Q(1,8)),(0,1)):
        assert max_with_loss(h,b,j,c)==direct_stamps(h,b,j,c)
        checks+=1
    planned=0
    for a,b in product(range(1,16),range(1,11)):
        total,gap=Q(a,3),Q(b,4)
        pieces=math.ceil(total/gap)
        anchors=tuple(total*i/pieces for i in range(pieces+1))
        assert certificate(anchors,1,gap/2)
        assert pieces==1 or total>gap*(pieces-1)
        planned+=1
    print(json.dumps(dict(timed_gap_controls=checks,
        placements_checked=planned,
        native_raster_width=2*W+1,projected_lane_separation=str(2*side),
        explicit_path_samples=len(sequence),specified_closed_band_width='6/5',
        double_cross_same_anonymous_anchors=True,
        matched_camera={'intact_middle':[[q[1],q[2]] for q in (
             if_intact[0][1],if_intact[1][1])],
             'dropped_middle_same':broken[0][1][1],
             'blocked_middle_equals_genuine_negative_pixels':True},
        equal_empty_pixels_not_equal_source_qualification=True,
        max_gap_with_one_loss=2),indent=2,sort_keys=True))
if __name__=='__main__':main()
