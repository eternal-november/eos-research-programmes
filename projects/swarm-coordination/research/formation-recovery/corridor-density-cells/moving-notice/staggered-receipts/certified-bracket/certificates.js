
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const rep=(x,n)=>Array(n).fill(x);
function check(k,d,interior,want){
 const n=2*k;
 const out=[...rep(-2*d,k),...rep(2*d,k)];
 const seq=[out,...interior,out.map(a=>-a)];
 const rev=seq.slice().reverse().map(row=>row.map(a=>-a));
 const S=BigInt(2*d*k*k), vmax=BigInt(2*d*k), amax=BigInt(2*d);
 const end=[];
 let admissible=0;
 for(const sub of [seq,rev]){
  assert(sub.every(a=>a.length===n));
  let X=Array(5).fill(0n), V=Array(5).fill(0n);
  for(let j=0;j<n;j++){
   const A=sub.map(w=>BigInt(w[j]));
   const b=[X,X.map((v,i)=>v+V[i]),X.map((v,i)=>v+2n*V[i]+A[i])];
   assert(A.every(a=>-amax<=a&&a<=amax));
   for(let i=1;i<5;i++)for(const c of b){
    const gap=c[i]-c[i-1];
    assert(0n<=gap&&gap<=3n*S);admissible++;
   }
   X=b[2];V=V.map((v,i)=>v+A[i]);
   assert(V.every(v=>-vmax<=v&&v<=vmax));
  }
  assert(V.every(v=>v===0n));
  end.push(X);
 }
 for(let i=0;i<5;i++)for(let j=0;j<n;j++)
  if(i===0||i===4||(i!==2&&j<k))assert(seq[i][j]===rev[i][j]);
 assert((end[0][2]-end[0][0])*BigInt(want[1])===BigInt(want[0])*S);
 assert((end[1][4]-end[1][2])*BigInt(want[1])===BigInt(want[0])*S);
 return {segments:n,scale:Number(S),span:want.join("/"),
         gapControls:admissible,leftEnds:end[0].map(Number)};
}
const signed=JSON.parse(fs.readFileSync(path.join(__dirname,"certificates.json"),"utf8"));
const verified=signed.map(({k,d,interior,target})=>check(k,d,interior,target));
console.log(JSON.stringify({certificates:verified}));
