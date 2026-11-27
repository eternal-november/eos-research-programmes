// Exact scalar shared-prefix synthesis; no floating point or native sensor input.
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
const clip=(a,b)=>{if(!a||!b)return null;const lo=max(a[0],b[0]),hi=min(a[1],b[1]);return le(lo,hi)?[lo,hi]:null};
const hull=(a,dt)=>a?[sub(a[0],dt),add(a[1],dt)]:null;
const exact=x=>[x,x];
const terrain=[one,six];
const far=h=>[{u:zero,v:two,s:div(h,two),b:zero}];
const late=[{u:zero,v:one,s:Q(3,2),b:zero},{u:one,v:two,s:zero,b:Q(3,2)}];
const shift=(p,t)=>add(mul(p.s,t),p.b);
const middle=(a,b)=>div(add(a,b),two);
function band(s,category){
 if(category===0)return terrain;
 if(category===1)return clip(terrain,[sub(s,one),four]);
 return clip(terrain,[sub(s,one),add(s,two)]);
}
function chain(a,b,worlds){
 const cuts=[a,b];
 for(const world of worlds)for(const p of world){
   for(const x of [p.u,p.v])if(lt(a,x)&&lt(x,b))cuts.push(x);
   if(!eq(p.s,zero))for(const k of [one,two]){
     const t=div(sub(k,p.b),p.s);
     if(le(p.u,t)&&le(t,p.v)&&lt(a,t)&&lt(t,b))cuts.push(t);
   }
 }
 const t=uniq(cuts);
 let z=t.map(()=>terrain);
 for(let i=0;i+1<t.length;i++)for(const world of worlds){
   const m=middle(t[i],t[i+1]);
   const p=world.find(p=>le(p.u,m)&&le(m,p.v));
   const s=shift(p,m), cat=le(s,one)?0:le(s,two)?1:2;
   z[i]=clip(z[i],band(shift(p,t[i]),cat));
   z[i+1]=clip(z[i+1],band(shift(p,t[i+1]),cat));
 }
 return {t,z};
}
function scan(c,first){
 const a=[clip(c.z[0],first)];
 for(let i=1;i<c.t.length;i++)a.push(clip(c.z[i],hull(a[i-1],sub(c.t[i],c.t[i-1]))));
 return a
}
function reverse(c){return {t:c.t.toReversed().map(neg),z:c.z.toReversed()}}
function points(c,first,last){
 const a=scan(c,first), top=clip(a.at(-1),last);if(!top)return null;
 let x=top[0];const seq=[[c.t.at(-1),x]];
 for(let i=c.t.length-2;i>=0;i--){
   const b=clip(a[i],hull(exact(x),sub(c.t[i+1],c.t[i])));
   assert(b,"constructive propagation");x=b[0];seq.push([c.t[i],x])
 }
 return seq.reverse()
}
function solve(h,r){
 const F=far(h), L=late, p=chain(zero,r,[F,L]);
 const f=chain(r,two,[F]), l=chain(r,two,[L]);
 // Zero-duration suffix still consumes its terminal duty.
 if(eq(r,two)){
  f.z[0]=band(h,le(h,one)?0:le(h,two)?1:2);
  l.z[0]=band(Q(3,2),1);
 }
 const c=clip(scan(p,exact(four)).at(-1),
          clip(scan(reverse(f),terrain).at(-1),scan(reverse(l),terrain).at(-1)));
 if(!c)return null;
 const seam=exact(c[0]);
 return [points(p,exact(four),seam),points(f,seam,terrain),points(l,seam,terrain)]
}
function direct(h,r,which="both"){
 const F=far(h), L=late;
 const nodes=[terrain], edges=[]; // 0 is reference, 1 is the shared physical seam
 function addChain(c,start,end){
   let j=start;nodes[j]=clip(nodes[j],c.z[0]);
   for(let i=1;i<c.t.length;i++){
     const k=(i===c.t.length-1&&end!==null)?end:nodes.push(terrain)-1;
     nodes[k]=clip(nodes[k],c.z[i]);
     const d=sub(c.t[i],c.t[i-1]);edges.push([j,k,d],[k,j,d]);j=k
   }
 }
 if(which==="both"){
   nodes.push(terrain);
   const first=nodes.push(exact(four))-1;
   const p=chain(zero,r,[F,L]),f=chain(r,two,[F]),l=chain(r,two,[L]);
   if(eq(r,zero)){nodes[1]=exact(four)}else addChain(p,first,1);
   if(eq(r,two)){
      nodes[1]=clip(nodes[1],clip(band(h,le(h,one)?0:le(h,two)?1:2),band(Q(3,2),1)));
   } else {addChain(f,1,null);addChain(l,1,null)}
 }else{
   const first=nodes.push(exact(four))-1;
   addChain(chain(zero,two,[which==="far"?F:L]),first,null)
 }
 for(let i=1;i<nodes.length;i++){const z=nodes[i];if(!z)return false;edges.push([0,i,z[1]],[i,0,neg(z[0])])}
 const d=nodes.map(()=>zero);
 for(let k=0;k<d.length;k++){
  let changed=false;
  for(const [u,v,c] of edges){const p=add(d[u],c);if(lt(p,d[v])){d[v]=p;changed=true}}
  if(!changed)return true;
 }
 return false
}
function verify(path,world){
 // Validate fresh constructive trajectories by sweeping the six
 // footprint/duty edges and both sides of every independent phase split.
 let checks=0;
 for(let i=1;i<path.length;i++){
  const [[a,x],[b,y]]=[path[i-1],path[i]];
  assert(le(sub(x,y),sub(b,a))&&le(sub(y,x),sub(b,a)),"speed");
  assert(le(one,x)&&le(x,six)&&le(one,y)&&le(y,six),"gap/radio");
  for(const phase of world){
    const u=max(a,phase.u),v=min(b,phase.v);if(lt(v,u))continue;
    const interp=t=>add(x,mul(div(sub(t,a),sub(b,a)),sub(y,x)));
    const bounds=t=>[Q(-2),two,sub(interp(t),two),add(interp(t),two),shift(phase,t),add(shift(phase,t),one)];
    const f=bounds(u),g=bounds(v), times=[u,v];
    for(let k=0;k<f.length;k++)for(let j=0;j<k;j++){
      const d=sub(f[k],f[j]),delta=sub(sub(g[k],g[j]),d);
      if(eq(delta,zero))continue;
      const alpha=div(neg(d),delta);
      if(lt(zero,alpha)&&lt(alpha,one))times.push(add(u,mul(sub(v,u),alpha)));
    }
    const p=uniq(times);const all=p.concat(p.slice(1).map((t,i)=>middle(t,p[i])));
    for(const t of all){
      const a=bounds(t);let x=a[4],end=a[5];
      for(const [l,u] of [[a[0],a[1]],[a[2],a[3]]]){
        if(le(l,x))x=max(x,u);
      }
      assert(le(end,x),"uncovered physical chord");checks++;
    }
  }
 }
 return checks
}
const physically=h=>le(h,two)||le(add(mul(h,h),Q(4)),mul(Q(7),h));
function bound(h){
 if(!physically(h))return null;
 if(le(h,Q(5)))return two;
 return le(h,Q(19,3))?sub(Q(7),h):div(sub(Q(23,3),h),two)
}
function main(){
 let n=0,physical=0,feas=0,checks=0,tight=0,accepted=[];
 const peaks=uniq([...Array.from({length:81},(_,i)=>Q(i,10)),Q(19,3),Q(637,100),Q(638,100),Q(51,8)]);
 for(const h of peaks){
  const cutoff=bound(h);
  assert(direct(h,zero,"far")===physically(h),"individual far");physical++;
  assert(direct(h,zero,"late"),"individual late");physical++;
  const r=uniq([...Array.from({length:41},(_,i)=>Q(i,20)),Q(2,3),...(cutoff?[cutoff]:[])]);
  if(cutoff)tight++;
  for(const t of r){
    const m=solve(h,t), want=cutoff?le(t,cutoff):false;
    assert(Boolean(m)===direct(h,t),"independent graph");
    assert(Boolean(m)===want,"analytic cutoff "+show(h)+" at "+show(t));
    n++;
    if(m){
      const [p,f,l]=m;const a=p.concat(f.slice(1)),b=p.concat(l.slice(1));
      for(const z of [a,b])assert(eq(z[0][1],four)&&eq(z[0][0],zero)&&eq(z.at(-1)[0],two),"end constraints");
      checks+=verify(a,far(h))+verify(b,late);feas++;
    }
  }
  if([Q(11,2),Q(19,3),Q(637,100),Q(638,100)].some(t=>eq(t,h)))
    accepted.push([show(h),cutoff&&show(cutoff)])
 }
 return {histories:n,knownWorldChecks:physical,feasible:feas,continuousCoverageChecks:checks,tightRationalCuts:tight,examples:accepted}
}

console.log(JSON.stringify(main()));
