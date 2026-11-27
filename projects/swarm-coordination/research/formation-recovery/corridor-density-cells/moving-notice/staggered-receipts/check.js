function prim(H,delay,t) {
 const u=Math.min(H,Math.max(0,t-delay));
 if(u<=H/2)return [u*u,2*u];
 return [H*H/2-(H-u)**2,2*(H-u)];
}
const n=5,h=3,cap=2;
const endL=[-2,-1,2,2,2],endR=[-2,-2,-2,1,2];
// Exact terminal-only comparator witness (displacements, not trajectories).
for(const x of [endL,endR]){
 if(x.some(v=>Math.abs(v)>2))throw Error("reach");
 if(x.slice(1).some((v,i)=>v-x[i]<0||v-x[i]>h))throw Error("gap");
}
if(endL[2]-endL[0]!==4||endR[4]-endR[2]!==4||
  endL.some((v,i)=>Math.abs(v-endR[i])>(i===2?4:(i===1||i===3?1:0))))throw Error("terminal");
function attainable(t,sign){
 const [F,U]=prim(2,0,t),[G,V]=prim(1,1,t);
 const p=[-F,-.75*F+sign*.25*G,sign*(.75*F+.25*G),.75*F+sign*.25*G,F];
 const v=[-U,-.75*U+sign*.25*V,sign*(.75*U+.25*V),.75*U+sign*.25*V,U];
 return {p,v};
}
let lastL=null,lastR=null,queries=0;
for(let i=0;i<=4096;i++){
 const t=i/2048,L=attainable(t,1),R=attainable(t,-1);
 for(const [z,last] of [[L,lastL],[R,lastR]]) {
  if(z.v.some(v=>Math.abs(v)>cap))throw Error("speed");
  if(z.p.slice(1).some((v,i)=>v-z.p[i]<0||v-z.p[i]>h))throw Error("gap");
  if(last&&z.v.some((v,i)=>Math.abs(v-last.v[i])>2/2048))throw Error("accel");
  if((t===0||t===2)&&z.v.some(v=>v!==0))throw Error("rest");
 }
 if(t<=1&&(L.p[1]!==R.p[1]||L.p[3]!==R.p[3]||L.v[1]!==R.v[1]||L.v[3]!==R.v[3]))
  throw Error("nonanticipation");
 if(t>=1.5) {
  const F=prim(2,0,t)[0],G=prim(1,1,t)[0];
  if(F-G!==1.5)throw Error("saturation");
 }
 lastL=L;lastR=R;queries++;
}
if(lastL.p[2]-lastL.p[0]!==29/8||lastR.p[4]-lastR.p[2]!==29/8)throw Error("positive");
if(1.5**2/2>=1.5)throw Error("rest comparator");
console.log({queries,terminalCandidate:4,constructive:29/8,
             provedUpper:4-((2*Math.sqrt(3)-3)/4)**2});
