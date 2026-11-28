// Model only: post-partition read-only audit and independent inspection.
// Imports the frozen common checker. Plant actions are intentionally discrete.
const fs = require("node:fs"), vm=require("node:vm"), cp=require("node:child_process");
function boot(filename) {
  const hash=cp.execFileSync("git",["hash-object",filename],{encoding:"utf8"}).trim();
  if(hash!=="6b2881248f3f09b6bfe2a45161500d486773728c")throw Error("wrong frozen model blob");
  const demand=fs.readFileSync(filename,"utf8");
  // The assembly reuses the unchanged functions; its landmarks are validated.
  const i=demand.indexOf("function synthesize("),j=demand.indexOf("const assert =");
  if(i<0||j<=i)throw Error("core marker");
  const head=demand.slice(i,j);
  return vm.runInNewContext(head+"\n({synthesize,direct});",{});
}
function main(core) {
  const check=(x)=>{if(!x)throw Error("check failed");};
  const indices=(b)=>[0,1,2].filter(d=>b&(1<<d));
  const count=b=>indices(b).length;
  const records=["a017c1e0","d6018a05"]; // exact bytes, same effect journal prefix
  const actions=[0,1,2,3,4,5]; // dock = floor(a/2), lane = a%2
  const bases=["fork","cycle","forced","revealed","hidden-fork"];
  const supports={fork:[[3,5],[6,6]],cycle:[[3,3],[5,5],[6,6]],
    forced:[[1,1],[2,2],[4,4]],revealed:[[3,3],[5,5]],"hidden-fork":[[1,2],[4,4]]};
  const results={};let counted=0;
  for(const type of bases)for(const reach of [0,3,7])for(const cap of [4,5,6])for(const fresh of [false,true]) {
    // Both report-binding histories and both physical lane histories, after source loss.
    // Each pair of masks is bundled into the same observation cell when hidden.
    const worlds=supports[type].flatMap((m,g)=>m.flatMap((b,k)=>[0,1].flatMap((q)=>[0,1].map(l=>({id:[g,k,q,l].join("/"),g,b,q,l})))));
    const plans=Array.from({length:8},(_,b)=>({id:b,b,shared:false})).concat(
          Array.from({length:8},(_,b)=>({id:b+8,b,shared:true})));
    const required=(_,p)=>p.inspection&&p.audit&&p.independent;
    function execute(w,p,policy) {
      counted++;
      const support=p.b|(p.shared?reach:0);
      // Early qualified staging survives the mandatory late donor outage.
      const dockReceipt=indices(support).map(i=>[i,records[w.q]]);
      // Selector sees neither the key binding nor the complete reachable-dock set.
      const view=[w.g,fresh?w.l:null];
      const action=policy(view);
      const dock=Math.floor(action/2), lane=action%2;
      const canUse = action!==null&&(w.b&(1<<dock))&&(support&(1<<dock));
      let charged=4+(fresh?1:0);
      if(p.shared&&(reach&(1<<dock))&&!(p.b&(1<<dock))) charged+=1;
      const inspection=Boolean(canUse&&lane===w.l&&charged<=cap);
      // Return succeeds only with the exact retained historical row, not a redo.
      const stored=dockReceipt.find(([endpoint])=>endpoint===dock)?.[1];
      const returned=inspection&&stored ? String(lane)+stored : null;
      const audit=returned!==null&&returned.slice(1)===records[w.q]&&
        1+returned.slice(1).length/2<=5;
      // Separate fixed capacity: this checks only the declared disjoint-channel model.
      const independent=new Uint8Array([9,1,4,6]).length<=4;
      return {view,inspection,audit,independent};
    }
    const got=core.synthesize(worlds,plans,actions,execute,required);
    // Equivalent factored direct: earliest use after stop, with complete keyed
    // scoped staging and exact per-dock budget. No reuse of checker internals.
    const masks=supports[type].map(([a,b])=>a&b);
    const expected=plans.filter(p=>fresh&&masks.every(m=>indices(m).some(i=>
      ((p.b&(1<<i))||(p.shared&&(reach&(1<<i))&&cap>=6))&&cap>=5))).map(p=>p.id);
    check(JSON.stringify(got.map(x=>x.plan.id))===JSON.stringify(expected));
    for(const p of got)for(const w of worlds)check(required(w,execute(w,p.plan,p.decide)));
    const local=got.filter(p=>!p.plan.shared);
    const best=(ps,value)=>ps.length?Math.min(...ps.map(x=>value(x.plan))):null;
    const bestLocal=best(local,p=>count(p.b));
    const bestOverall=best(got,p=>count(p.b)+Number(p.shared));
    results[[type,reach,cap,+fresh].join("/")]=[masks,bestLocal,bestOverall,
      got.filter(p=>count(p.plan.b)+Number(p.plan.shared)===bestOverall).map(p=>p.plan.id)];
  }
  function optimum(k,i,j,h) {return results[[k,i,j,h].join("/")].slice(1,3);}
  const tests={hiddenIndistinction:optimum("hidden-fork",7,6,1),cycle:optimum("cycle",0,5,1),
    forced:optimum("forced",7,5,1),forcedWithSharedRead:optimum("forced",7,6,1),
    staleRead:optimum("forced",7,6,0),fork:optimum("fork",0,5,1)};
  check(JSON.stringify(tests)===JSON.stringify({hiddenIndistinction:[null,null],cycle:[2,2],
    forced:[3,3],forcedWithSharedRead:[3,1],staleRead:[null,null],fork:[2,2]}));
  return {configurations:Object.keys(results).length,executionPairs:counted,tests,results};
}
if(typeof require!=="undefined"&&require.main===module)
  console.log(JSON.stringify(main(boot(process.argv[2]))));
