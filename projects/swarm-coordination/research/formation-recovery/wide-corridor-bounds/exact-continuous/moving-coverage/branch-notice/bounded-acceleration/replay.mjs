// Exact rational tests of acceleration-dependent seam geometry.
"use strict";
const abs=n=>n<0n?-n:n;
function gcd(a,b){for(;b;){[a,b]=[b,a%b]}return abs(a)}
function Q(n,d=1){n=BigInt(n);d=BigInt(d);if(!d)throw Error("zero denominator");if(d<0n){n=-n;d=-d}const g=gcd(n,d);return [n/g,d/g]}
const add=([a,b],[c,d])=>Q(a*d+b*c,b*d), neg=([a,b])=>[-a,b], sub=(a,b)=>add(a,neg(b));
const mul=([a,b],[c,d])=>Q(a*c,b*d), div=([a,b],[c,d])=>Q(a*d,b*c);
const le=([a,b],[c,d])=>a*d<=c*b, eq=(a,b)=>le(a,b)&&le(b,a), lt=(a,b)=>le(a,b)&&!eq(a,b);
const min=(a,b)=>le(a,b)?a:b,max=(a,b)=>le(a,b)?b:a;
const zero=Q(0),one=Q(1),two=Q(2),four=Q(4),six=Q(6);
const sort=(a,b)=>eq(a,b)?0:le(a,b)?-1:1, uniq=xs=>xs.sort(sort).filter((v,i,a)=>!i||!eq(v,a[i-1]));
const show=([n,d])=>d===1n?String(n):String(n)+"/"+String(d);
function assert(x,reason){if(!x)throw Error(reason)}

const square=z=>mul(z,z), half=z=>div(z,two), cmp=(a,b)=>eq(a,b)?0:le(a,b)?-1:1;
function loss(T,v,a){
 const u=sub(one,v), tail=max(zero,sub(u,mul(a,T)));
 return div(sub(square(u),square(tail)),mul(two,a))
}
const P=(T,v,a)=>sub(T,loss(T,v,a));
function bound(F,L,a){
 assert(le(zero,L)&&le(L,F)&&lt(zero,a),"duration and acceleration");
 return le(mul(a,L),one)?add(sub(F,L),mul(a,square(L))):sub(add(F,L),div(one,a))
}
function directIntegral(T,v,a){ // independent trapezoid on the exact saturation break
 const s=min(T,div(sub(one,v),a));
 return add(mul(half(add(v,min(one,add(v,mul(a,s))))),s),sub(T,s))
}
function directBest(F,L,a){
 // independent analytic optimizer by enumerating active affine derivative pieces
 const ends=uniq([neg(one),one,max(neg(one),sub(one,mul(a,F))),min(one,sub(mul(a,L),one))]);
 function slope(x){return sub(min(F,div(sub(one,x),a)),min(L,div(add(one,x),a)))}
 const xs=[...ends];
 for(let i=0;i+1<ends.length;i++){
     const b=ends[i],c=ends[i+1],db=slope(b),dc=slope(c);
     if(lt(zero,db)&&lt(dc,zero))xs.push(add(b,mul(sub(c,b),div(db,sub(db,dc)))));
 }
 return xs.map(v=>add(directIntegral(F,v,a),directIntegral(L,neg(v),a))).reduce(max)
}
function state(p,t){
 const d=sub(t,p.t);
 return [add(add(p.x,mul(p.v,d)),half(mul(p.a,square(d)))),add(p.v,mul(p.a,d))]
}
function trace(at,x,v,controls){
 const r=[];
 for(const [until,a] of controls){
    assert(lt(at,until),"positive segment");
    const p={t:at,w:until,x,v,a};r.push(p);
    [x,v]=state(p,until);at=until
 }
 return r
}
function certify(path,phases,a){
 let n=0;
 const lim=[one,Q(6)];
 const check=(p,l,r,c,s,why)=>{
   const extrema=[l,r];
   if(!eq(p.a,zero)){
     const crit=add(p.t,div(sub(s,p.v),p.a));
     if(lt(l,crit)&&lt(crit,r))extrema.push(crit)
   }
   for(const t of extrema){
     assert(le(state(p,t)[0],add(c,mul(s,t))),why);n++
   }
 };
 for(let i=0;i<path.length;i++){
   const p=path[i];
   if(i){
     const old=path[i-1], [x,v]=state(old,p.t);
     assert(eq(old.w,p.t)&&eq(x,p.x)&&eq(v,p.v),"kinematic seam")
   }
   assert(le(neg(a),p.a)&&le(p.a,a),"acceleration");
   for(const t of [p.t,p.w]){
     const v=state(p,t)[1];assert(le(neg(one),v)&&le(v,one),"speed")
   }
   check(p,p.t,p.w,lim[1],zero,"gap upper");
   const mirror={...p,x:neg(p.x),v:neg(p.v),a:neg(p.a)};
   check(mirror,p.t,p.w,neg(lim[0]),zero,"gap lower");
   for(const phase of phases){
     const l=max(p.t,phase.l), r=min(p.w,phase.r);if(!lt(l,r))continue;
     const cuts=[l,r];
     if(!eq(phase.s,zero))for(const k of [one,two]){
       const q=div(sub(k,phase.b),phase.s);if(lt(l,q)&&lt(q,r))cuts.push(q)
     }
     cuts.sort(cmp);
     for(let k=0;k+1<cuts.length;k++){
       const t=half(add(cuts[k],cuts[k+1]));
       const center=add(mul(t,phase.s),phase.b);
       if(le(center,one))continue;
       check(mirror,cuts[k],cuts[k+1],sub(one,phase.b),neg(phase.s),"far footprint lower");
       if(le(center,two))check(p,cuts[k],cuts[k+1],four,zero,"seam overlap");
       else check(p,cuts[k],cuts[k+1],add(phase.b,two),phase.s,"far footprint upper")
     }
   }
 }
 return n
}
function sharper(h,a){
 const c=Q(2,3),tc=div(four,h),eta=sub(c,tc),delta=sub(sub(Q(7),h),tc),k2=mul(mul(two,a),delta);
 const klo=Q(797193,1000000),khi=Q(797194,1000000);
 assert(lt(square(sub(one,khi)),k2)&&lt(k2,square(sub(one,klo))),"exact radical enclosure");
 assert(lt(sub(one,mul(a,eta)),klo),"minimizer is lowest seam velocity");
 assert(le(Q(2),mul(a,sub(two,tc))),"full post-seam saturation window");
 const radius=half(square(eta));
 function feasible(r){
  const L=sub(c,r);
  assert(le(zero,L),"before late phase seam");
  const q=div(mul(a,sub(square(L),radius)),eta);
  return le(one,q)||(le(zero,q)&&le(square(sub(one,q)),k2));
 }
 const before=Q(604725,1000000),after=Q(604726,1000000);
 assert(feasible(before)&&!feasible(after),"sharp isolating interval");
 const stroke=div(khi,mul(two,a)), start=sub(tc,mul(Q(5),stroke));
 const u=add(start,stroke), w=add(u,stroke);
 const far=[{l:zero,r:two,s:half(h),b:zero}];
 const late=[{l:zero,r:one,s:Q(3,2),b:zero},{l:one,r:two,s:zero,b:Q(3,2)}];
 let checks=0,pos=0,bad=0;
 const cases=uniq([...Array.from({length:51},(_,i)=>Q(590+i,1000)),before,after]);
 for(const r of cases){
     assert(lt(r,c),"before the late overlap");
     if(!feasible(r)){bad++;continue}
     assert(lt(w,r)&&lt(r,tc),"split occurs within the prepared +a stroke");
     const shared=trace(zero,four,zero,[[start,zero],[u,neg(a)],[w,zero],[r,a]]);
     const [x,v]=state(shared.at(-1),r);
     const farAfter=trace(r,x,v,[[add(tc,div(sub(one,khi),a)),a],[two,zero]]);
     const brake=trace(r,x,v,[[c,neg(a)]]);
     const [xc,vc]=state(brake.at(-1),c);
     assert(le(xc,four)&&lt(vc,zero)&&le(neg(one),vc),"late overlap entry");
     const lateAfter=trace(c,xc,vc,[[sub(c,div(vc,a)),a],[two,zero]]);
     checks+=certify([...shared,...farAfter],far,a)+certify([...shared,...brake,...lateAfter],late,a);
     assert(le(sub(h,one),state(farAfter.at(-1),two)[0]),"far peak attained");
     pos++;
 }
 return {rationalProbes:cases.length,certifiedBefore:pos,analyticRejections:bad,
         isolatingInterval:[show(before),show(after)],coefficientChecks:checks}
}
function main(){
 let trials=0;
 for(const a of [Q(1,2),one,Q(3,2),Q(3),Q(10),Q(50)]){
   for(let l=0;l<=24;l++)for(let f=0;f<=24;f++){
     if(f<l)continue;
     const L=Q(l,16),F=Q(f,16), guess=bound(F,L,a);
     assert(eq(guess,directBest(F,L,a)),"independent optimum");
     for(const v of [neg(one),Q(-9,17),zero,Q(4,7),one])
       assert(eq(P(F,v,a),directIntegral(F,v,a)),"integrals");
     trials++;
   }
 }
 const h=Q(637,100), a=Q(10), c=Q(2,3), tc=div(four,h), start=sub(tc,Q(7,20)), r=Q(1,2), reject=Q(16,25);
 const shared=trace(zero,four,zero,[[start,zero],[add(start,Q(1,10)),neg(a)],[r,a]]);
 const p=shared.at(-1),[x,v]=state(p,r);
 const farSuffix=trace(r,x,v,[[sub(tc,Q(1,20)),a],[tc,zero],[two,zero]]);
 const stop=add(r,div(v,a));
 const lateSuffix=trace(r,x,v,[[stop,neg(a)],[two,zero]]);
 const far=[{l:zero,r:two,s:half(h),b:zero}];
 const late=[{l:zero,r:one,s:Q(3,2),b:zero},{l:one,r:two,s:zero,b:Q(3,2)}];
 const aCheck=certify([...shared,...farSuffix],far,a);
 const bCheck=certify([...shared,...lateSuffix],late,a);
 assert(eq(state(farSuffix[1],tc)[0],four)&&eq(state(farSuffix[1],tc)[1],one),"attained seam");
 assert(le(reject,div(sub(Q(23,3),h),two)),"speed-only arm remains feasible");
 const target=sub(h,Q(5)), upper=bound(sub(two,reject),sub(c,reject),a);
 assert(lt(upper,target),"strict acceleration obstruction");
 return {endpointBoundComparisons:trials,fullyCertifiedEarlyBranches:2,earlyNotice:show(r),coefficientChecks:aCheck+bCheck,
   impossibleLaterNotice:show(reject),required:show(target),upper:show(upper),
   farSeam:show(tc),sameInformationSpeedOnlyAllows:show(div(sub(Q(23,3),h),two)),sharpFixture:sharper(h,a)}
}

console.log(JSON.stringify(main()));
