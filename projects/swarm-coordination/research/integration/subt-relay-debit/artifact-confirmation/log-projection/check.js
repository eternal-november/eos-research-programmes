const six=(x)=>Number(x.toPrecision(6)).toString();
const math6=(x)=>six(Math.sign(x)*Math.round(Math.abs(x)*1e6)/1e6);
const sourceKey=(xyz)=>"artifact_"+xyz.map(x=>x.toFixed(6)).join("_");
const directions=[[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]];
function cls(center,exp){
 const eps=2**(-exp),rows=[];
 for(const f of directions)for(let mask=0;mask<8;mask++){
  const xyz=f.map((x,j)=>center[j]+(mask>>j&1?-1:1)*x*eps);
  const d2=xyz.reduce((s,x,j)=>s+(x-center[j])**2,0);
  const local=xyz.map(math6).join(" "),world=xyz.map(math6).join(" ");
  const row={local,world,distance:six(Math.sqrt(d2)),kind:"artifact",
     points:1,total:1,simTime:2,id:41,closest:"target"};
  rows.push({key:sourceKey(xyz),row,d2});
 }
 return rows;
}
let families=0,pairs=0;
for(let n=100;n<=999;n+=17)for(let exp=17;exp<=19;exp++){
 const rows=cls([n,n+20,n+50],exp);
 if(new Set(rows.map(r=>r.key)).size!==48||
    new Set(rows.map(r=>JSON.stringify(r.row))).size!==1||
    rows.some(r=>r.d2!==14*2**(-2*exp)))throw Error(JSON.stringify({n,exp}));
 for(let i=0;i<48;i++)for(let j=0;j<48;j++) {
  if((i===j)!==(rows[i].key===rows[j].key))throw Error("identity");
  pairs++;
 }
 families++;
}
const sample=cls([100,100,100],19);
const projection = (t)=>({event:t>=2,scoreFile:t>=4?1:0});
if(JSON.stringify(projection(2))!==JSON.stringify(projection(3)))throw Error("prefix");
console.log({families,queries:pairs,exampleVisible:sample[0].row,
          left:sample[0].key,right:sample[7].key,bits:Math.ceil(Math.log2(48)),
          eventBeforeAggregatePair:[projection(2),projection(3)]});
