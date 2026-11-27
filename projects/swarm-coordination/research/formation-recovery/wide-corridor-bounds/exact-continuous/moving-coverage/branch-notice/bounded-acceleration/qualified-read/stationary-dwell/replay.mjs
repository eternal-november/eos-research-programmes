// Exact dwell-kernel replay. All time and displacement checks are rational.
const q=(n,d=1)=>[BigInt(n),BigInt(d)];
const add=([a,b],[c,d])=>[a*d+c*b,b*d], neg=([a,b])=>[-a,b];
const sub=(a,b)=>add(a,neg(b)), mul=([a,b],[c,d])=>[a*c,b*d], div=([a,b],[c,d])=>[a*d,b*c];
const le=([a,b],[c,d])=>a*d<=c*b, eq=(a,b)=>le(a,b)&&le(b,a),sq=x=>mul(x,x);
const z=q(0),a=q(10),sig=q(400,637),sLo=q(797193939,10000000000),sHi=q(797193940,10000000000);
const k2=mul(q(20),sub(q(63,100),sig));
const assert=b=>{if(!b)throw Error("certificate failed")};
function rule(s,r,d){
 const r0=sub(sig,s),u=sub(r0,r);
 if(!le(z,u)||!le(d,r))return false;
 const m=sub(mul(q(2),sq(s)),sq(u));
 return le(m,z)||le(m,sq(sub(r,d)));
}
function direct(s,r,d){
 const k=mul(a,s),T=sub(sig,r);
 if(!le(d,r)||!le(s,T))return false;
 const turn=div(sub(T,s),q(2));
 // First velocity -a*t, then k-a*(T-t). Integrate independently by trapezoids.
 const mid=neg(mul(a,turn));
 const signed=add(mul(div(mid,q(2)),turn),mul(div(add(mid,k),q(2)),sub(T,turn)));
 const prep=sub(r,d), maxRetreat=div(mul(a,sq(prep)),q(4));
 return le(signed,maxRetreat)
}
function main(){
 assert(le(sq(sub(q(1),mul(a,sHi))),k2)&&le(k2,sq(sub(q(1),mul(a,sLo)))));
 let comparisons=0;
 for(const s of [q(5,64),sLo,sHi]) for(let i=0;i<=560;i+=4) for(let j=0;j<=450;j+=5){
   const r=q(i,1000),d=q(j,1000);
   assert(rule(s,r,d)===direct(s,r,d));comparisons++;
 }
 const d=q(42,100),times=[q(425,1000),q(47,100),q(548,1000)];
 const verdicts=times.map(r=>{const b=rule(sLo,r,d);assert(b===rule(sHi,r,d));return b});
 assert(verdicts.join()==="true,false,true");
 // Isolate d_max through (sigma-s-d_max)^2 = 2s^2 and r0 through sigma-s.
 assert(le(mul(q(2),sq(sHi)),sq(sub(sub(sig,sHi),q(435483,1000000)))));
 assert(le(sq(sub(sub(sig,sLo),q(435484,1000000))),mul(q(2),sq(sLo))));
 return {exactComparisons:comparisons,maxDwellBetween:["0.435483","0.435484"],latestRestBetween:["0.548224","0.548225"],dwell:"0.42",completionTimes:["0.425","0.470","0.548"],verdicts}
}

console.log(JSON.stringify(main()));
