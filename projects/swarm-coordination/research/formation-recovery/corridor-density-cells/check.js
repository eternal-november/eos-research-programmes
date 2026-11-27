const INF=Infinity;
function distances(n, edges) {
 const d=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?0:INF));
 for(const [a,b,c] of edges)d[a][b]=Math.min(d[a][b],c);
 for(let k=0;k<n;k++)for(let i=0;i<n;i++)for(let j=0;j<n;j++)
  d[i][j]=Math.min(d[i][j],d[i][k]+d[k][j]);
 return d;
}
const cycle=d=>d.some((r,i)=>r[i]<0);
function intervalRadius(x,k,d){
 if(cycle(d))return [1,0]; // no feasible horizon
 let a=0,b=1;
 for(let i=0;i<x.length;i++)for(let j=0;j<x.length;j++){
  if(!Number.isFinite(d[i][j]))continue;
  const v=x[j]-x[i]-d[i][j],s=k[i]+k[j];
  if(v<=0)continue;
  if(s===0)return [1,0];
  if(v*b>a*s) {a=v;b=s;}
 }
 return [a,b];
}
function goal(x,k,d,[a,b]){return x.map((_,j)=>Math.min(...x.map((v,i)=>v*b+k[i]*a+b*d[i][j])));}
const eq=(a,b)=>a[1]&&b[1]?a[0]*b[1]===a[1]*b[0]:a[1]===b[1];

function brute(x,k,edges,a,b){
 const lo=x.map((v,i)=>v*b-k[i]*a),hi=x.map((v,i)=>v*b+k[i]*a);
 let y=[];
 function go(i){
  if(i===x.length)return true;
  for(let v=lo[i];v<=hi[i];v++){
   y[i]=v;
   if(edges.every(([j,m,c])=>j>i||m>i||y[m]-y[j]<=b*c)&&go(i+1))return true;
  }
  return false;
 }
 return go(0);
}
function append(d,[u,v,c]) {
 if(d[v][u]+c<0)return null;
 return d.map((row,i)=>row.map((val,j)=>Math.min(val,d[i][u]+c+d[v][j])));
}
let rand=20052007;
const draw=n=>{rand=(Math.imul(rand,1664525)+1013904223)>>>0;return (rand>>>9)%n;};
let fixed=0,sols=0,checks=0;
for(let q=0;q<1600;q++){
 const n=2+draw(3),x=Array.from({length:n},()=>draw(9)-4),
 k=Array.from({length:n},()=>draw(3));
 const E=Array.from({length:1+draw(8)},()=>[draw(n),draw(n),draw(9)-4]);
 const d=distances(n,E),R=intervalRadius(x,k,d);
 if(R[1]){
  const y=goal(x,k,d,R),[a,b]=R;
  if(y.some((z,i)=>Math.abs(z-b*x[i])>a*k[i])||
     E.some(([i,j,c])=>y[j]-y[i]>b*c))throw Error("bad attaining point");
  sols++;
 }
 for(let a=0;a<=6;a++)for(const b of [1,2]){
  const predicted=R[1]>0&&a*R[1]>=R[0]*b;
  if(brute(x,k,E,a,b)!==predicted)throw Error(JSON.stringify({E,x,k,R,a,b}));
  fixed++;
 }
 if(!cycle(d)){
  const next=[draw(n),draw(n),draw(11)-5],increment=append(d,next),
        full=distances(n,[...E,next]);
  if(increment===null?!cycle(full):cycle(full)||increment.some((r,i)=>r.some((z,j)=>z!==full[i][j])))
   throw Error("incremental disagreement");
  checks++;
 }
}
function deck(n,m,mask){
 const g=1,R=2,delta=1,num=n*m+1,E=[];
 for(let j=1;j<num;j++) E.push([j,j-1,-g],[j-1,j,R]);
 let count=0;
 for(let h=0;h<n;h++)if(mask>>h&1){E.push([(h+1)*m,h*m,-(m*g+delta)]);count++;}
 return {E,count,x:Array.from({length:num},(_,i)=>i*g),k:Array(num).fill(1)};
}
let group=0,capFailures=0;
for(let n=1;n<=8;n++)for(let m=2;m<=4;m++)
for(let mask=1;mask<1<<n;mask++){
 const w=deck(n,m,mask),size=w.x.length,d=distances(size,w.E);
 if(!eq(intervalRadius(w.x,w.k,d),[w.count,2]))throw Error("world grouping");
 group++;
 if(mask===1){
   const E=w.E.map(([i,j,c])=>i<j&&c===2?[i,j,1]:[i,j,c]);
   if(!cycle(distances(size,E)))throw Error("physical incompatibility");
   capFailures++;
 }
}
console.log({fixed,sols,checks,group,capFailures});
