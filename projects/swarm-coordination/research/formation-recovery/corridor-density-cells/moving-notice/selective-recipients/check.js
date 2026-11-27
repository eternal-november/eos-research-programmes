function predicted(m,h,B,C,mask) {
 if(!(mask>>m&1))return Math.min(2*m*h,2*B);
 let l=1,r=1;
 while(l<m&&(mask>>(m-l)&1))l++;
 while(r<m&&(mask>>(m+r)&1))r++;
 return Math.min(2*m*h,2*B+Math.min(2*C,h*Math.min(l,r)));
}
function exact(m,h,B,C,mask,need) {
 const n=2*m+1, zero=2*n, E=[];
 for(let i=0;i<n;i++){
  E.push([zero,i,B],[i,zero,B],[zero,i+n,B],[i+n,zero,B]);
  const q=mask>>i&1?2*C:0;
  E.push([i,i+n,q],[i+n,i,q]);
  if(i){E.push([i-1,i,h],[i,i-1,0],[i-1+n,i+n,h],[i+n,i-1+n,0]);}
 }
 E.push([m,0,-need],[2*m+n,m+n,-need]);
 const d=Array(2*n+1).fill(0);
 for(let k=0;k<d.length;k++){
  let changed=false;
  for(const [a,b,c] of E)if(d[a]+c<d[b]){d[b]=d[a]+c;changed=true;}
  if(!changed)return true;
 }
 return false;
}
let seed=17393;
const pick=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>16)%n;};
let checks=0;
for(let i=0;i<4800;i++){
 const m=1+pick(6),h=pick(5),B=pick(7),C=pick(B+1),mask=pick(1<<(2*m+1));
 for(let need=0;need<=2*m*h;need++){
  if(exact(m,2*h,2*B,2*C,mask,need)!==(2*need<=predicted(m,2*h,2*B,2*C,mask)))
    throw Error(JSON.stringify({m,h,B,C,mask,need}));
  checks++;
 }
}
function prof(H,v,t) {
 t=Math.min(H,Math.max(0,t));
 const b=Math.min(H/2,v/2),p=H-b;
 return t<=b?t*t:t<=p?b*b+2*b*(t-b):b*b+2*b*(p-b)+(H-p)**2-(H-t)**2;
}
let normalized=0;
for(const v of [1,2,4,8])for(let k=1;k<=12;k++)for(let j=0;j<=k;j++) {
 const T=k/2,tau=j/2,H=T-tau;
 for(let z=0;z<=4*k;z++) {
  const t=z/8;
  if(prof(H,v,t-tau)*prof(T,v,T)>prof(T,v,t)*prof(H,v,H))throw Error("normalized order");
  normalized++;
 }
}
const summary={checks,normalized,oneCentreOnly:predicted(2,12,16,9,4)/16,
   centreAndNeighbors:predicted(2,12,16,9,14)/16,unreachedCentre:predicted(2,12,16,9,27)/16};
if(summary.oneCentreOnly!==2.75||summary.centreAndNeighbors!==3||summary.unreachedCentre!==2)throw Error("example");
console.log(summary);
