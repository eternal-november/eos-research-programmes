// Exact rational check for a speed-qualified inspection notice.
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

function main(){
 let cases=[], checks=0;
 const a=Q(10),h=Q(637,100),sigma=div(four,h),c=Q(2,3),eta=sub(c,sigma);
 const delta=sub(sub(Q(7),h),sigma),k2=mul(mul(two,a),delta);
 const K=Q(797194,1000000), Klo=Q(797193,1000000);
 assert(lt(square(sub(one,K)),k2)&&lt(k2,square(sub(one,Klo))),"k enclosure");
 const read=Q(604725,1000000), above=Q(604726,1000000);
 const rad0=add(div(mul(Klo,eta),a),half(square(eta)));
 const rad1=add(div(mul(K,eta),a),half(square(eta)));
 assert(lt(rad1,square(sub(c,read)))&&lt(square(sub(c,above)),rad0),"r_a enclosure");
 const k0=div(K,mul(two,a)), start=sub(sigma,mul(Q(5),k0));
 const u=add(start,k0), w=add(u,k0);
 const far=[{l:zero,r:two,s:half(h),b:zero}];
 const late=[{l:zero,r:one,s:Q(3,2),b:zero},{l:one,r:two,s:zero,b:Q(3,2)}];
 let brakesAtSeam=0;
 for(const cap of [Q(0),Q(1,10),Q(1,5),Q(2,5),Q(1,2),Q(11,20),Q(563,1000),Q(564,1000),Q(565,1000),Q(566,1000),Q(7,10),one]){
   const r=min(read,sub(sigma,div(sub(K,cap),a)));
   const upper=min(above,sub(sigma,div(sub(Klo,cap),a)));
   assert(lt(r,upper)&&le(sub(upper,r),Q(1,1000000)),"certified bracket");
   const common=trace(zero,four,zero,[[start,zero],[u,neg(a)],[w,zero],[r,a]]);
   const [x,v]=state(common.at(-1),r);
   assert(le(zero,v)&&le(v,cap),"same speed cap on both worlds at acquisition");
   const f0=trace(r,x,v,[[add(sigma,div(sub(one,K),a)),a],[two,zero]]);
   let l0;
   if(le(add(x,div(square(v),mul(two,a))),four)){
      const stop=add(r,div(v,a));
      l0=trace(r,x,v,eq(r,stop)?[[two,zero]]:[[stop,neg(a)],[two,zero]]);
   }else{
      const first=trace(r,x,v,[[c,neg(a)]]);
      const [xc,vc]=state(first[0],c);
      assert(le(xc,four)&&lt(vc,zero)&&le(neg(one),vc),"still can reach late seam");
      l0=[...first,...trace(c,xc,vc,[[sub(c,div(vc,a)),a],[two,zero]])];
      brakesAtSeam++;
   }
   assert(le(sub(h,one),state(f0.at(-1),two)[0]),"far duty complete");
   checks+=certify([...common,...f0],far,a)+certify([...common,...l0],late,a);
   cases.push([show(cap),show(r),show(upper),show(v)]);
 }
 return {qualifierCases:cases.length,certifiedBracketWidth:"1/1000000",quadraticInequalityChecks:checks,brakesAtSeam,
         rest:cases[0],oneFifthSpeedExample:cases[2],unrestricted:cases.at(-1)}
}

console.log(JSON.stringify(main()));
