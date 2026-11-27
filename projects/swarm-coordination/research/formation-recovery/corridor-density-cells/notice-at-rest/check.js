function cells(c) {return [...new Set(c)];}
function intervalWeights(c,delta,D) {
 let w=[];
 for(let i=0;i<=c.length;i++){
  let count={},m=0,b=[];
  for(let j=i;j<=c.length;j++){
   if(j>i){const k=c[j-1];count[k]=(count[k]??0)+1;m=Math.max(m,count[k]);}
   b[j]=Math.max(m*delta-D,0);
  }
  w[i]=b;
 }
 return w;
}
function prefix(c,delta,D){
 const w=intervalWeights(c,delta,D),t=[0];
 for(let j=1;j<=c.length;j++)t[j]=Math.max(...t.map((v,i)=>v+w[i][j]));
 return {cost:t.at(-1),s:t.slice(1).map((v,i)=>v-t[i])};
}
function allSuffix(c,delta,cap,s,D) {
 return cells(c).every(h=>{
   for(let start=0;start<=D;start++){
     function all(i,prev) {
       if(i===c.length)return true;
       for(let y=0;y<=D;y++)if(y-prev+s[i]>=(c[i]===h?delta:0)&&
                                y-prev+s[i]<=cap&&all(i+1,y))return true;
       return false;
     }
     if(all(0,start))return true;
   }
   return false;
 });
}
function brute(c,delta,cap,D) {
 let best=Infinity,s=[];
 function go(i,n){
  if(n>=best)return;
  if(i===c.length){if(allSuffix(c,delta,cap,s,D))best=n;return;}
  for(let x=0;x<=cap;x++){s[i]=x;go(i+1,n+x);}
 }
 go(0,0);return best;
}
function alphabetFormula(n,M,delta,D){
 if(D>=delta)return Math.max(0,Math.ceil(n/M)*delta-D);
 return Math.max(...Array.from({length:n},(_,i)=> {
   const p=i+1;return p*(delta-D)+delta*Math.floor((n-p)/M);
 }));
}
let queries=0, alphabet=0,assignments=0;
for(let n=1;n<=5;n++)for(let M=1;M<=3;M++){
 let layouts=Array.from({length:M**n},(_,mask)=>
  Array.from({length:n},(_,j)=>Math.floor(mask/M**j)%M));
 for(let delta=1;delta<=2;delta++)for(let D=0;D<=4;D++){
   let opt=Infinity;
   for(const c of layouts){
    const a=prefix(c,delta,D),limit=delta;
    if(a.s.some(x=>x<0||x>delta)||!allSuffix(c,delta,limit,a.s,D))throw Error("construct");
    if(brute(c,delta,limit,D)!==a.cost)throw Error(JSON.stringify({c,delta,D,a}));
    queries++;
    opt=Math.min(opt,a.cost);assignments++;
   }
   if(opt!==alphabetFormula(n,M,delta,D)||opt!==prefix(Array.from({length:n},(_,i)=>i%M),delta,D).cost)
     throw Error("alphabet formula");
   alphabet++;
 }
}
const contiguous=prefix([0,0,1,1],1,1),interleaved=prefix([0,1,0,1],1,1);
if(contiguous.cost!==2||interleaved.cost!==1)throw Error("example");
console.log({queries, alphabet,assignments,contiguous,interleaved});
