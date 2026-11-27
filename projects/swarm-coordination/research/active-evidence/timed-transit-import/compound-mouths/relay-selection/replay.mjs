import fs from "node:fs";
import {createHash} from "node:crypto";
const checksum=b=>createHash("sha1").update("blob "+b.length+"\0").update(b).digest("hex");
function check(source) {
 const input=source["world.sdf"], raw=source["world.dot"];
 const poses=new Map([...input.matchAll(/<include>([\s\S]*?)<\/include>/g)].flatMap(m=>{
  const t=m[1],id=t.match(/<name>tile_(\d+)<\/name>/)?.[1]??(/<name>staging_area<\/name>/.test(t)?"0":null);
  return id===null?[]:[[+id,t.match(/<pose>([^<]+)<\/pose>/)[1].trim().split(/\s+/).map(Number).slice(0,3)]];
 }));
 const N=poses.size, inf=Infinity;
 if(N!==158||[...poses].some(([i,p])=>i<0||i>=N||p.length!==3||p.some(x=>!Number.isFinite(x))))throw Error("tile schema");
 const dist=Array.from({length:N},(_,i)=>Array.from({length:N},(_,j)=>i===j?0:inf));
 const g=Array.from({length:N},()=>[]);
 for(const [,a0,b0,l0] of raw.matchAll(/(\d+)\s*--\s*(\d+)\s+\[label=(\d+)\]/g)){
  const [a,b,l]=[+a0,+b0,+l0];dist[a][b]=dist[b][a]=l;
  g[a].push([b,l]);g[b].push([a,l]);
 }
 for(let k=0;k<N;k++)for(let i=0;i<N;i++)for(let j=0;j<N;j++)dist[i][j]=Math.min(dist[i][j],dist[i][k]+dist[k][j]);
 function shortest(a,b,omit=[],weighted=true){
  const d=Array(N).fill(inf),used=Array(N).fill(false);d[a]=0;
  while(true){
   let s=-1;for(let i=0;i<N;i++)if(!used[i]&&d[i]<(s===-1?inf:d[s]))s=i;
   if(s===-1)return null;if(s===b)return d[s];used[s]=true;
   for(const [t,c] of g[s]){
    if(omit.some(([x,y])=>(s===x&&t===y)||(s===y&&t===x)))continue;
    d[t]=Math.min(d[t],d[s]+(weighted?c:1));
   }
  }
 }
 const ids=[18,39,16,13,42];
 for(const a of ids)for(let b=0;b<N;b++)if(shortest(a,b)!==dist[a][b])throw Error("Dijkstra comparison");
 const squared=(a,b)=>poses.get(a).reduce((s,x,k)=>s+(x-poses.get(b)[k])**2,0);
 const choice=(a,b,k)=>{
  const dc=dist[a][b],d=squared(a,b);
  const rc=k===null||k===a||k===b?inf:Math.max(dist[a][k],dist[k][b]);
  return rc<dc?[rc,Math.max(squared(a,k),squared(k,b)),k]:[dc,d,null];
 };
 const viable=([c,r],m)=>c<=10&&r<=m;
 const mask=(k,m)=>{
  const a=choice(18,39,k),b=choice(16,39,k);
  return [viable(a,m),viable(b,m)];
 };
 const scenarios=[null,13,42].map(k=>[k,choice(18,39,k),choice(16,39,k)]);
 for(let m=1;m<=6400;m++){
  const a=mask(null,m), b=mask(13,m);
  if((a[0]&&!a[1]&&!b[0]&&b[1])!==(m>=5000&&m<5625))throw Error("range");
 }
 const viableForB=[...poses.keys()].map(k=>[k,...mask(k,5184)]).filter(x=>x[2]);
 if(JSON.stringify(viableForB)!=="[[13,false,true],[42,true,true]]")throw Error("site sweep");
 const deploymentTravel=[[],[[13,42]],[[13,42],[2,3]]].map(omit=>[omit,shortest(13,42,omit,false)]);
 const prep=source["level.cc"];
 const geom=source["detector.cc"];
 const factory=source["factory.cc"];
 if(!prep.includes("boxShape.SetSize({2, 2, 2});")||
    !prep.includes("if (!this->runner->entityCompMgr.ChildrenByComponents(modelEntity,")||
    !geom.includes("region.Intersects(performerVolume)")||
    !factory.includes("msgs::StringMsg performerReq;")||
    !factory.includes("/level/set_performer")||
    !source["launch.ign"].includes("<is_performer>true</is_performer>")||
    !source["launch.ign"].includes("<max_range>500.0</max_range>")||
    !source["launch.ign"].includes("<comms_cost_max>10</comms_cost_max>"))throw Error("registration/config source");
 const m=input.match(/<model name="performer_detector_rockfall_4">([\s\S]*?)<\/model>/)[1]
              .replace(/<!--[\s\S]*?-->/g,"");
 if(!/key: "state"\s+value: "1"/.test(m))throw Error("trigger direction");
 const pos=m.match(/<pose>([^<]+)<\/pose>/)[1].trim().split(/\s+/).map(Number);
 const size=m.match(/<size>([^<]+)<\/size>/)[1].trim().split(/\s+/).map(Number);
 if(pos.slice(3).some(x=>x!==0))throw Error("axis alignment");
 const clean=x=>Number(x.toFixed(6));
 const expanded=size.map((s,k)=>[clean(pos[k]-.5*s-1),clean(pos[k]+.5*s+1)]);
 const inBox=v=>v.every((x,i)=>expanded[i][0]<=x&&x<=expanded[i][1]);
 const samples=[[100,62.5,0],[100.000033,62.5,0],[100,62.5,-1]];
 const initialScan=samples.map(p=>inBox(p));
 if(JSON.stringify(initialScan)!=="[true,true,false]")throw Error("trigger");
 const update=(already,center,paused=false,hasPerformer=true)=>{
  if(paused||!hasPerformer)return [already,null];
  const now=inBox(center);
  return [now,now===already?null:Number(now)];
 };
 const stationary=[
  update(false,samples[0],false,false),
  update(false,samples[0],true,true),
  update(false,samples[0]),
  update(true,samples[0]),
  update(true,samples[2])
 ];
 const law=s=>{const [c,r,k]=s;return 40+10*(1.5+.2*c)*Math.log10(.55*(Math.sqrt(r)+(k===null?0:2)));};
 const defaultOld=[choice(115,128,null),choice(115,128,126)];
 return {sites:N,rangeQueries:6400,scenarios,viableForB,deploymentTravel,expanded,initialScan,stationary,
         defaultOld,defaultMeanLossIncrease:clean(law(defaultOld[1])-law(defaultOld[0]))};
}
const root=new URL("./SOURCE.tsv",import.meta.url), source={};
for(const line of fs.readFileSync(root,"utf8").trimEnd().split("\n")){
 const [name,,,,sha]=line.split("\t");
 const b=fs.readFileSync(new URL(name,root));
 if(checksum(b)!==sha)throw Error("source mismatch: "+name);
 source[name]=b.toString("utf8");
}
if(source["launch-link.txt"]!=="competition.ign")throw Error("wrong launch symlink");
process.stdout.write(JSON.stringify(check(source),null,2)+"\n");
