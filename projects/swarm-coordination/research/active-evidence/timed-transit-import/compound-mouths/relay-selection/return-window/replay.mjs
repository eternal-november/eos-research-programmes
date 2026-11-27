import fs from "node:fs";
import {createHash} from "node:crypto";
const checksum=b=>createHash("sha1").update("blob "+b.length+"\0").update(b).digest("hex");
function schedules(s,d){
 const poses=new Map([...s.matchAll(/<include>([\s\S]*?)<\/include>/g)].flatMap(m=>{
 const a=m[1], i=a.match(/<name>tile_(\d+)<\/name>/)?.[1]??(/<name>staging_area<\/name>/.test(a)?"0":null);
 return i===null?[]:[[+i,a.match(/<pose>([^<]+)<\/pose>/)[1].trim().split(/\s+/).map(Number).slice(0,3)]]}));
 const N=poses.size,edges=[];
 for(const [,a,b,w] of d.matchAll(/(\d+)\s*--\s*(\d+)\s+\[label=(\d+)\]/g))edges.push([+a,+b,+w]);
 const dist=(cut=[],weighted=false)=>{
 const p=Array.from({length:N},(_,i)=>Array.from({length:N},(_,j)=>i===j?0:Infinity));
 for(const [a,b,w] of edges)if(!cut.some(([u,v])=>u===a&&v===b))p[a][b]=p[b][a]=weighted?w:1;
 for(let k=0;k<N;k++)for(let i=0;i<N;i++)for(let j=0;j<N;j++)p[i][j]=Math.min(p[i][j],p[i][k]+p[k][j]);
 return p;
 };
 const radio=dist([],true);
 const sq=(a,b)=>poses.get(a).reduce((s,x,k)=>s+(x-poses.get(b)[k])**2,0);
 const pass=(a,b,l,range=72)=>{
 const v=l===null||l===a||l===b?Infinity:Math.max(radio[a][l],radio[l][b]);
 const c=radio[a][b];
 return v<c?v<=10&&Math.max(sq(a,l),sq(l,b))<=range**2:c<=10&&sq(a,b)<=range**2;
 };

 
 const cuts=[[],[[2,3]],[[13,42]],[[2,3],[13,42]]];
 const installations=[13,42];
 const H=12;
 return cuts.map(c=>{
  const p=dist(c);
  const aGroups=["none","near","original","all"];
  function allPlans(group,fixed=false) {
   const caps=group==="none"?[]:group==="near"?[13]:group==="original"?[13,42]:[...poses.keys()];
   const deployments=[[null,Infinity],...caps.flatMap(t=>Array.from({length:H},(_,i)=>i+1)
      .filter(k=>p[13][t]+1<=k).map(k=>[t,k]))];
   function trajectory(start,t,l) {
    let d=Infinity, place=null;
    for(const v of fixed?[start]:poses.keys()){
       if(fixed&&t<0)throw Error();
       if(p[start][v]>t||!pass(v,39,l))continue;
       if(p[v][0]<d){d=p[v][0];place=v;}
    }
    return place===null?null:{v:place,egress:t+1+d};
   }
   // Independent per-duty lists. Key includes b/a dispatch because the receiver is
   // a unit-capacity resource; common motion conflicts are intentionally absent.
   const plans=[], arr=new Map();
   const at=(i,start,t,l)=>{
     const key=[i,t,l].join("/");
     if(!arr.has(key))arr.set(key,trajectory(start,t,l));
     return arr.get(key);
   };
   for(const [r,k] of deployments){
    const pa=Array.from({length:H},(_,t)=>at(0,18,t,t<k?null:r));
    const pb=Array.from({length:H},(_,t)=>at(1,16,t,t<k?null:r));
    for(let a=0;a<H;a++)if(pa[a])for(let b=0;b<H;b++)if(pb[b]&&a!==b){
     const e=Math.max(pa[a].egress,pb[b].egress,r===null?p[13][0]:k+p[r][0]);
     if(e>H)continue;
     plans.push({r,k,a,b,e,aPos:pa[a].v,bPos:pb[b].v});
    }
   }
   const table={};
   for(let a=1;a<=4;a++)for(let b=1;b<=6;b++)for(let e=8;e<=12;e++){
    const x=plans.find(z=>z.a+1<=a&&z.b+1<=b&&z.e<=e);
    table[[a,b,e].join("/")]=x??null;
   }
   return table;
  }
  const tabs=aGroups.map(g=>allPlans(g));

  const fixed=allPlans("near",true);
  const nbr=Array.from({length:N},(_,u)=>[u]);
  for(const [a,b] of edges)if(!c.some(([x,y])=>a===x&&b===y)){nbr[a].push(b);nbr[b].push(a);}
  const live=(start,relay,k,locked=false)=>{
    // Layered position sets for no receipt and for each admissible send slot.
    let f=new Set([start]), back=Array.from({length:H},()=>new Set());
    const e=Array(H).fill(Infinity);
    for(let t=0;t<H;t++){
      const nf=new Set(), nback=Array.from({length:H},()=>new Set());
      for(const x of f){
        for(const y of (locked?[x]:nbr[x]))nf.add(y);
        if(pass(x,39,t<k?null:relay))nback[t].add(x);
      }
      for(let a=0;a<t;a++)for(const x of back[a])for(const y of nbr[x])nback[a].add(y);
      for(let a=0;a<=t;a++)if(nback[a].has(0)&&e[a]===Infinity)e[a]=t+1;
      f=nf;back=nback;
    }
    return e;
  };
  let envelopeChecks=0;
  const indep=(group,locked,table)=>{
    const candidates=group==="none"?[]:group==="near"?[13]:group==="original"?installations:[...poses.keys()];
    const seen=new Set([13]), d=new Map([[13,0]]), fifo=[13];
    for(const x of fifo)for(const y of nbr[x])if(!seen.has(y)){seen.add(y);d.set(y,d.get(x)+1);fifo.push(y);}
    const dExit=new Map([[0,0]]), exitQueue=[0];
    for(const x of exitQueue)for(const y of nbr[x])if(!dExit.has(y)){dExit.set(y,dExit.get(x)+1);exitQueue.push(y);}
    const deployments=[[null,Infinity],...candidates.flatMap(x=>Array.from({length:H},(_,i)=>i+1)
      .filter(k=>d.has(x)&&d.get(x)+1<=k).map(k=>[x,k]))];
    const plans=[];
    for(const [r,k] of deployments){
      const a=live(18,r,k,locked), b=live(16,r,k,locked);
      for(let i=0;i<H;i++)if(a[i]<=H)for(let j=0;j<H;j++)if(i!==j&&b[j]<=H)
         plans.push([i+1,j+1,Math.max(a[i],b[j],(r===null?0:k)+(dExit.get(r??13)??Infinity))]);
    }
    for(const [key,s] of Object.entries(table)){
      const [a,b,e]=key.split("/").map(Number);
      if(Boolean(s)!==plans.some(([i,j,k])=>i<=a&&j<=b&&k<=e))throw Error("explicit time expansion: "+group+"/"+key);
      envelopeChecks++;
    }
  };
  for(const [i,g] of aGroups.entries())indep(g,false,tabs[i]);
  indep("near",true,fixed);
  return {cut:c, tabs, fixed,envelopeChecks,
    totals:[...tabs,fixed].map(t=>Object.values(t).filter(Boolean).length)};
 });
}
function firstMoves(s,d){
 const poses=new Map([...s.matchAll(/<include>([\s\S]*?)<\/include>/g)].flatMap(m=>{
 const a=m[1], i=a.match(/<name>tile_(\d+)<\/name>/)?.[1]??(/<name>staging_area<\/name>/.test(a)?"0":null);
 return i===null?[]:[[+i,a.match(/<pose>([^<]+)<\/pose>/)[1].trim().split(/\s+/).map(Number).slice(0,3)]]}));
 const N=poses.size,edges=[];
 for(const [,a,b,w] of d.matchAll(/(\d+)\s*--\s*(\d+)\s+\[label=(\d+)\]/g))edges.push([+a,+b,+w]);
 const dist=(cut=[],weighted=false)=>{
 const p=Array.from({length:N},(_,i)=>Array.from({length:N},(_,j)=>i===j?0:Infinity));
 for(const [a,b,w] of edges)if(!cut.some(([u,v])=>u===a&&v===b))p[a][b]=p[b][a]=weighted?w:1;
 for(let k=0;k<N;k++)for(let i=0;i<N;i++)for(let j=0;j<N;j++)p[i][j]=Math.min(p[i][j],p[i][k]+p[k][j]);
 return p;
 };
 const radio=dist([],true);
 const sq=(a,b)=>poses.get(a).reduce((s,x,k)=>s+(x-poses.get(b)[k])**2,0);
 const pass=(a,b,l,range=72)=>{
 const v=l===null||l===a||l===b?Infinity:Math.max(radio[a][l],radio[l][b]);
 const c=radio[a][b];
 return v<c?v<=10&&Math.max(sq(a,l),sq(l,b))<=range**2:c<=10&&sq(a,b)<=range**2;
 };

 const base=dist([]);
 const nr=(v)=>[v,...edges.flatMap(([a,b])=>a===v?[b]:b===v?[a]:[])].sort((a,b)=>a-b);
 const exactFirst=(v,r,p,h)=>nr(v).filter(x=>p[v][x]<=1&&pass(x,39,r)&&p[x][0]<=h-2);
 const out=[[],[[2,3]],[[13,42]],[[2,3],[13,42]]].map(c=>{
  const p=dist(c);
  const viaA=nr(18).filter(x=>p[18][x]<=1&&pass(x,39,13)&&p[x][0]<=6);
  return {cut:c,actions:[null,13,42].map(r=>exactFirst(16,r,p,9)),viaA,
   lowerPaths:[15,6,42,2].map(i=>[i,...[18,16,0].map(j=>Number.isFinite(p[j][i])?p[j][i]:null)])};
 });
 return {out,neighbors:[nr(18),nr(16)],baseFinite:[base[18][0],base[16][0]]};
}

function run(s,d){
 const raw=schedules(s,d), fm=firstMoves(s,d);
 const matrix=raw.map(x=>({cut:x.cut,totals:x.totals,
   examples:["1/2/9","1/2/10","1/5/9"].map(k=>[k,...x.tabs.map(t=>t[k]),x.fixed[k]]), checks:x.envelopeChecks}));
 if(JSON.stringify(matrix.map(x=>x.totals))!=="[[80,80,80,80,60],[80,80,80,80,60],[56,80,80,80,60],[0,0,0,0,0]]")
  throw Error("envelope");
 const open=fm.out[0].actions,closed=fm.out[2].actions;
 const moves=fm.neighbors[1],table=[];
 for(const u of moves)for(const v of moves)for(const o of [false,true])for(const c of [false,true])
  if(open[+o].includes(u)&&closed[+c].includes(v))table.push([u,v,o,c]);
 const blind=table.filter(([u,v])=>u===v),timely=table.filter(([,,o,c])=>!o&&c);
 if(JSON.stringify(blind)!=="[[6,6,true,true]]"||JSON.stringify(timely)!=="[[42,6,false,true]]")
  throw Error("causality");
 return {matrix,firstMove:fm,blind,timely,choicesTested:moves.length**2*4};
}
const root=new URL("./SOURCE.tsv",import.meta.url),src={};
for(const row of fs.readFileSync(root,"utf8").trimEnd().split("\n")){
 const [name,,,,sha]=row.split("\t");
 const b=fs.readFileSync(new URL(name,root));
 if(checksum(b)!==sha)throw Error("source mismatch "+name);
 src[name]=b.toString("utf8");
}
process.stdout.write(JSON.stringify(run(src["world.sdf"],src["world.dot"]),null,2)+"\n");
