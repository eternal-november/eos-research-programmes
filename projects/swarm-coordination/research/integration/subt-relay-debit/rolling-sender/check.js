function compressed(T,L,W=4) {
 let masks=[], lo=0, mask=3;
 for(let i=0;i<T.length;i++){
  if(i>0 && T[i]-T[i-1]>W){masks.push([lo,i-1,mask]);lo=i;mask=3;}
  if(i>=lo+2 && T[i]-T[i-2]<=W)mask=0;
  const x=L[i];
  mask &= (i-lo)%2===0 ? x : ((x&1)<<1)|((x&2)>>1);
 }
 if(T.length)masks.push([lo,T.length-1,mask]);
 return masks;
}
function verify(T,L,W=4) {
 function rec(i,assigned) {
  if(i===T.length)return true;
  for(const b of [1,2]) if((L[i]&b)&&assigned.every((x,j)=>x!==b||T[i]-T[j]>W)){
    if(rec(i+1,[...assigned,b]))return true;
  }
  return false;
 }
 return rec(0,[]);
}
let cases=0;
for(let n=1;n<=6;n++) for(let gm=0;gm<4**(n-1);gm++){
 const T=[0];let m=gm;
 for(let j=1;j<n;j++){T.push(T[j-1]+[0,2,3,5][m%4]);m=Math.floor(m/4);}
 for(let lm=0;lm<3**n;lm++){
  const L=[];let ml=lm;
  for(let i=0;i<n;i++){L.push(1+ml%3);ml=Math.floor(ml/3);}
  if(compressed(T,L).every(x=>x[2]!==0)!==verify(T,L))throw Error(JSON.stringify({T,L}));
  cases++;
 }
}
for(let n=2;n<=100;n++){
 const T=Array.from({length:n},(_,i)=>3*i);
 const A=T.map(()=>3),B=T.map(()=>3);A[n-1]=1;B[n-1]=2;
 const a=compressed(T,A),b=compressed(T,B);
 if(!a[0][2]||!b[0][2]||(a[0][2]&b[0][2]))throw Error('lookahead');
}
const original=[0,3,6], lists=[1,3,2];
const cuts=[3,4,5,6].map(u=>[u,verify([0,u,6],lists)]);
if(JSON.stringify(cuts)!=='[[3,false],[4,false],[5,true],[6,true]]')throw Error(JSON.stringify(cuts))
console.log(JSON.stringify({cases,longLookaheadCases:99,cuts}));
