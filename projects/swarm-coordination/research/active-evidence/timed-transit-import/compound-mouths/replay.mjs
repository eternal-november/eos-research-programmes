import fs from "node:fs";
import {createHash} from "node:crypto";
const hash=b=>createHash("sha1").update("blob "+b.length+"\0").update(b).digest("hex");
function compare(s,d,h) {
const section=h.split("ConnectionHelper::connectionPoints")[1].split("};")[0];
const points=new Map([...section.matchAll(/\{"([^"]+)",\s*\{((?:\s*\{[^}]*\}\s*,?)+)\}\}/g)].map(m=>[m[1].toLowerCase(),[...m[2].matchAll(/\{([^}]*)\}/g)].map(p=>p[1].split(",").map(Number))]));
const section2=h.split("ConnectionHelper::connectionTypes")[1].split("};")[0];
const tiles=new Map([...section2.matchAll(/\{"([^"]+)",\s*subt::ConnectionHelper::([A-Z_]+)\}/g)].map(m=>[m[1],m[2]]));
const contents=(str,key)=>str.match(new RegExp("<"+key+">([\\s\\S]*?)</"+key+">"))?.[1];
const values=s=>s.trim().split(/\s+/).map(Number);
const wp=(p,v)=>{
const [x,y,z,r,b,c]=p, [vx,vy,vz]=v;
const ly=Math.cos(r)*vy-Math.sin(r)*vz,lz=Math.sin(r)*vy+Math.cos(r)*vz;
const mx=Math.cos(b)*vx+Math.sin(b)*lz,mz=-Math.sin(b)*vx+Math.cos(b)*lz;
return [x+Math.cos(c)*mx-Math.sin(c)*ly,y+Math.sin(c)*mx+Math.cos(c)*ly,z+mz];
};
const vertex=[...s.matchAll(/<include>([\s\S]*?)<\/include>/g)].map(m=>{
 const t=m[1],name=contents(t,"name"),type=contents(t,"uri")?.split(/\/openrobotics\/models\//i)[1];
 const local=points.get(type?.toLowerCase());
 return !local?null:{name,type,id:name==="staging_area"?0:Number(name.split("_").at(-1)),p:values(contents(t,"pose")),kind:tiles.get(type),local};
}).filter(Boolean);
const caps=vertex.filter(v=>v.name.startsWith("cave_cap_"));vertex.splice(0,vertex.length,...vertex.filter(v=>!v.name.startsWith("cave_cap_"))); 
if(vertex.length!==158||new Set(vertex.map(v=>v.id)).size!==158||vertex.some(v=>v.p.length!==6||!v.kind)) throw Error(JSON.stringify(vertex.filter(v=>!v.kind)));
for(const v of vertex)v.ports=v.local.map(u=>wp(v.p,u));
const eco=new Map([...d.matchAll(/(\d+)\s*--\s*(\d+)\s+\[label=(\d+)\]/g)].map(m=>[m[1]+"/"+m[2],+m[3]]));
const out=new Map();
let eps=Infinity,multi=[],checks=0,maxMatch=0;
for(let i=0;i<vertex.length;i++)for(let j=i+1;j<vertex.length;j++){
 const l=vertex[i],r=vertex[j],key=[l.id,r.id].sort((a,b)=>a-b).join("/");
 const matches=[];
 for(let a=0;a<l.ports.length;a++)for(let b=0;b<r.ports.length;b++){
  const u=l.ports[a],v=r.ports[b];const err=Math.max(...u.map((x,k)=>Math.abs(x-v[k])));
  checks++;eps=Math.min(eps,Math.abs(err-1.5));
  if(err<=1.5){maxMatch=Math.max(maxMatch,err);matches.push({a,b,u,v,err})}
 }
 if(!matches.length)continue;
 if(matches.length!==1)multi.push(key);
 const cost=l.id===0||r.id===0||(l.kind==="STRAIGHT"&&r.kind==="STRAIGHT")?1:
  l.kind==="STRAIGHT"||r.kind==="STRAIGHT"?3:6;
 out.set(key,{cost,matches});
}
const diff=[...new Set([...out.keys(),...eco.keys()])].filter(k=>out.get(k)?.cost!==eco.get(k)).map(k=>[k,out.get(k)?.cost,eco.get(k)]);
const rocks=[...s.matchAll(/<model name="performer_detector_rockfall_(\d+)">([\s\S]*?)<\/model>/g)].map(m=>{
 const clean=m[2].replace(/<!--[\s\S]*?-->/g,""); const pose=values(contents(clean,"pose")),size=values(contents(clean,"size"));
 if(pose.slice(3).some(x=>x!==0))throw Error("not axis-aligned");
 return {id:+m[1],pose,size}
});
const dist=(p,q)=>Math.hypot(...p.map((x,i)=>x-q[i]));
const c2=(center,size,p)=>Math.hypot(...p.map((x,i)=>Math.max(0,Math.abs(x-center[i])-size[i]/2)));
const rockStats=rocks.map(o=>{
 const rr=[...out].map(([k,e])=>({k,min:Math.min(...e.matches.flatMap(m=>[c2(o.pose,o.size,m.u),c2(o.pose,o.size,m.v)]))})).sort((a,b)=>a.min-b.min);
 const touch=rr.filter(x=>x.min===0).map(x=>x.k);
 return {id:o.id,touch,nearest:rr.slice(0,3),gateMin:rr.find(x=>x.k==="2/3").min};
});
const graph=(excluded=[])=>{
 const neighbors=new Map(vertex.map(v=>[v.id,[]]));
 for(const key of out.keys()) if(!excluded.includes(key)){
  const [a,b]=key.split("/").map(Number);neighbors.get(a).push(b);neighbors.get(b).push(a);
 }
 return neighbors;
};
const walk=(g,s,t)=>{
 const paths=[[s]],seen=new Set([s]);
 for(const p of paths){
  const u=p.at(-1);
  if(t!==undefined&&u===t)return p;
  for(const v of g.get(u).slice().sort((a,b)=>a-b))if(!seen.has(v)){seen.add(v);paths.push([...p,v]);}
 }
 return t===undefined?[...seen].sort((a,b)=>a-b):null;
};
const arms=[[],["2/3"],["13/42"],["2/3","13/42"]].map(excluded=>{
 const g=graph(excluded);
 return {excluded,reportPath:walk(g,3,39),egressPath:walk(g,3,0),
   region:excluded.length===2?walk(g,3):undefined};
});
// Equality and a second walk from the published labeled edge list.
const costTo=(a,b,excluded=[])=>{
 const distances=new Map([[a,0]]),done=new Set();
 while(true){
  const next=[...distances].filter(([v])=>!done.has(v)).sort((x,y)=>x[1]-y[1])[0];
  if(!next)return null;
  const [v,dist]=next;if(v===b)return dist;done.add(v);
  for(const [key,cost] of eco){
   if(excluded.includes(key))continue;
   const [x,y]=key.split("/").map(Number);
   const u=v===x?y:v===y?x:null;
   if(u!==null&&dist+cost<(distances.get(u)??Infinity))distances.set(u,dist+cost);
  }
 }
};
const radioCosts=[[3,39],[3,0],[42,13]].map(([a,b])=>({a,b,
  nominal:costTo(a,b), ifEditedForEachArm:arms.map(x=>costTo(a,b,x.excluded))
}));
if(arms.some(x=>Boolean(x.reportPath)!==(costTo(3,39,x.excluded)!==null)||
  Boolean(x.egressPath)!==(costTo(3,0,x.excluded)!==null)))throw Error("graph replay disagrees");
const capMouths=caps.map(cap=>{
 const close=[];
 for(const t of vertex) for(const [j,p] of t.ports.entries())
  for(const q of cap.local.map(x=>wp(cap.p,x))){
   const err=Math.max(...p.map((v,k)=>Math.abs(v-q[k])));
   if(err<=1.5)close.push([t.id,j,err]);
  }
 return [cap.name,close];
});
const gate=out.get("2/3"),detour=out.get("13/42");
const rb=rocks.find(x=>x.id===4);
const keyMouths=[gate,detour].map(e=>e.matches.map(({u,v})=>[u,v].map(p=>{
 const deficit=p.map((x,i)=>Math.max(0,Math.abs(x-rb.pose[i])-rb.size[i]/2));
 return {point:p,halfExtentMinimum:deficit};
})));
return {arms,radioCosts,capMouths,keyMouths,caps:caps.length,tileCount:vertex.length,edgeCount:out.size,publishedEdges:eco.size,checks,eps,maxMatch,multi,diff,gate:out.get("2/3"),rockStats};
}

const roots=new URL("./SOURCE.tsv",import.meta.url);
const src={};
for(const line of fs.readFileSync(roots,"utf8").trimEnd().split("\n")){
 const [name,, , ,expected]=line.split("\t");
 const blob=fs.readFileSync(new URL(name,roots));
 const sha=hash(blob);
 if(sha!==expected)throw Error("source mismatch: "+name+" "+sha);
 src[name]=blob.toString("utf8");
}

const r=compare(src["world.sdf"],src["world.dot"],src["connections.cc"]);
if(r.diff.length||r.multi.length||r.edgeCount!==163||r.checks!==56750||
   r.capMouths.length!==12||r.capMouths.some(x=>x[1].length)||
   r.arms.slice(0,3).some(a=>!a.egressPath||!a.reportPath)||
   r.arms[3].egressPath||r.arms[3].reportPath||r.arms[3].region.length!==78||
   JSON.stringify(r.radioCosts[0].ifEditedForEachArm)!=="[12,25,12,null]"||
   !r.rockStats[3].nearest[0]||r.rockStats[3].nearest[0].k!=="13/42")
 throw Error("changed source results");
process.stdout.write(JSON.stringify(r,(_k,v)=>typeof v==="number"?Number(v.toFixed(6)):v,2)+"\n");
