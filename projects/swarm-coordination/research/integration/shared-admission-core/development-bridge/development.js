"use strict";
const report = (()=>{
"use strict";
// Source adapter contract: execute(world, plan, continuation) emits the
// reached receiver-local view before invoking continuation. The local
// selection cannot see world, transition state, or its evaluator.
function synthesize(worlds, plans, actions, execute, required) {
  const viable = [];
  for (const plan of plans) {
    const cells = new Map(), causes = [];
    for (const w of worlds) {
      const boundary = execute(w, plan, () => null);
      if (boundary.view === null) { causes.push(w.id); continue; }
      const key = JSON.stringify(boundary.view);
      if (!cells.has(key)) cells.set(key, new Map(actions.map(a => [a, null])));
      for (const [act, exclusion] of cells.get(key)) {
        if (exclusion !== null) continue;
        const replay = execute(w, plan, view => {
          if (JSON.stringify(view) !== key) throw Error("non-repeatable boundary");
          return act;
        });
        if (!required(w, replay)) cells.get(key).set(act, w.id);
      }
    }
    if (causes.length || [...cells.values()].some(a => [...a.values()].every(x => x !== null))) continue;
    const chosen = new Map([...cells].map(([key, a]) => [key,[...a].find(([, exclusion])=>exclusion===null)[0]]));
    viable.push({plan, decide: view => chosen.get(JSON.stringify(view)) ?? null});
  }
  return viable;
}

// Baseline: global enumeration of typed local functions, deliberately
// not calling intersection code. Used only on the small finite harness.
function direct(worlds, plans, actions, execute, required) {
  const out = [];
  for (const plan of plans) {
    const keys = [...new Set(worlds.map(w => {
      const v = execute(w, plan, () => null).view;
      return v === null ? null : JSON.stringify(v);
    }))];
    if (keys.includes(null)) continue;
    const table = new Map();
    const search = i => {
      if (i === keys.length) return worlds.every(w =>
        required(w, execute(w, plan, v => table.get(JSON.stringify(v)))));
      for (const a of actions) {
        table.set(keys[i], a);
        if (search(i+1)) return true;
      }
      return false;
    };
    if (search(0)) out.push(plan.id);
  }
  return out;
}

const assert = (b, m) => { if (!b) throw Error(m); };
const raw = [[1,0,2,1],[2,1,2,2]];
const domains = [
  {name:"visit", visit:true, audit:false, menu:["move0","move1","move2"]},
  {name:"audit", visit:false, audit:true, menu:["read0","read1"]},
  {name:"joint", visit:true, audit:true,
   menu:[0,1,2].flatMap(m=>[0,1].map(a=>"move"+m+"/read"+a))},
];

function operation(cap, visit, audit) {
  return (w, p, decide) => {
    // One fixture clock, one queue. A failed arrival cannot refund sender
    // charge. Receiver policy sees callbacks only, not the occupancy world.
    const charges = [], debits = [];
    const ledger = {wire:0, rx:0, evidence:0, other:false, unrelatedMove:false};
    const inbox = {occupancy:null, audit:null};
    let view=null, movement=null, output=null, returned=false;
    function send(t,n,sender,receiver,dst,deliver) {
      const tx=debits.filter(c=>c[0]>=t-1 && c[1]===sender).reduce((n,c)=>n+c[2],0);
      if(tx+n>dst) return false;
      debits.push([t,sender,n]); ledger.wire+=n;
      const used=charges.filter(c=>c[0]>=t-1 && c[1]===receiver)
        .reduce((s,c)=>s+c[2],0);
      if (used+n>dst) return false;
      charges.push([t,receiver,n]); ledger.rx+=n; deliver(); return true;
    }
    if (p.encoding!=="none" && p.stage==="early") proof(0);
    const plant={independentCell:0, visited:null};
    plant.independentCell++;
    ledger.unrelatedMove=(plant.independentCell===1);
    // This unrelated report is a separate outgoing duty. It is not
    // aligned with the user's owed operation, and never gets canceled.
    send(2,4,3,w.busy,32,()=>{ledger.other=true;});
    if (visit && p.probe!=="none" && (p.dock===1 || w.nearProbe)) {
      ledger.evidence++;
      const bit = p.probe==="fresh" && w.block===0 ? 1:0;
      send(2,1,4,p.dock,32,()=>{inbox.occupancy=bit;});
    }
    if (p.encoding!=="none" && p.stage==="late" && !w.outage) proof(2);
    function proof(t) {
      ledger.evidence++;
      const bytes=p.encoding==="ordinal"?1:4;
      // Ordinal is a reference into a receiver-local, preloaded two-row
      // basis. The authored old receipt key does not move when the role changes.
      const record=p.encoding==="ordinal" ?
        {scope:w.stale ? "old":"current", row:w.assoc} :
        {scope:"current",raw:raw[w.assoc]};
      send(t,bytes,4,p.dock,32,()=>{inbox.audit=record;});
    }
    const result = () => ({view, movement, output, returned, ledger});
    if (!send(2,4,2,p.dock,cap,()=>{})) return result();
    // Exact audit capacity is local: a grant alone is not a data source.
    // The outcome of the probe is information only, not movement authority.
    view=[p.dock,inbox.occupancy,w.grant,inbox.audit];
    const cmd=decide(JSON.parse(JSON.stringify(view)));
    if (cmd===null) return result();
    const parts=cmd.split("/");
    // Validate both primitive guards before the combined local commit.
    // The modeled interpreter is serialized, not transactional hardware.
    const m=visit ? Number(parts[0].slice(4)) : null;
    if (visit && (m===w.block || ![0,1,2].includes(m))) return result();
    let row=null;
    if (audit) {
      const a=Number(parts.at(-1).slice(4)), record=inbox.audit;
      if (!w.grant || !record || record.scope!=="current") return result();
      const declared=record.row ?? raw.findIndex(r=>JSON.stringify(r)===JSON.stringify(record.raw));
      if (a!==declared) return result();
      row=raw[a];
    }
    if (visit) { plant.visited=m; movement=plant.visited; }
    if (audit) output=row;
    // Actual payload length under declared codec, no compressed audit
    // content at the return interface. The joint frame prepends one
    // selected move byte to the exact four-byte audit result.
    const reply=visit && audit?[movement,...output]:
      audit?output:Array(4).fill(movement);
    if (send(2,reply.length,p.dock,2,cap,()=>{})) returned=true;
    return result();
  };
}

function supports(d, regime) {
  const worlds=[];
  for (const block of (d.visit?[0,1,2]:[-1]))
    for (const assoc of (d.audit?[0,1]:[-1]))
      for (const outage of (d.audit && !regime.noOutage?[false,true]:[false]))
        worlds.push({id:worlds.length,block,assoc,outage,busy:regime.busy,
                     nearProbe:regime.nearProbe,grant:regime.grant,stale:regime.stale});
  return worlds;
}
function obligations(d) {
  const equal=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
  return (w, r) => r.ledger.other && r.ledger.unrelatedMove && r.returned &&
    (!d.visit || (r.movement!==null && r.movement!==w.block)) &&
    (!d.audit || equal(r.output,raw[w.assoc]));
}
function options(d,noEarly=false) {
  const plans=[];
  for (const dock of [0,1])
    for (const probe of (d.visit?["none","stale","fresh"]:["none"]))
      for (const enc of (d.audit?["none","ordinal","full"]:["none"]))
        for (const stage of (enc==="none"?["none"]:noEarly?["late"]:["late","early"]))
          plans.push({dock,probe,encoding:enc,stage,id:[dock,probe,enc,stage].join("/")});
  return plans;
}

const report={};
for (const d of domains) {
  const results={};
  for (const [k,patch] of [
      ["empty-budget",{cap:4,busy:3}],
      ["one-more",{cap:5,busy:3}],
      ["near-occupied",{cap:5,busy:0}],
      ["near-no-probe",{cap:5,busy:1,nearProbe:false}],
      ["missing-grant",{cap:5,busy:3,grant:false}],
      ["bad-ordinal",{cap:5,busy:3,stale:true}],
      ["no-early",{cap:9,busy:3,noEarly:true}],
      ["late-only-pair",{cap:5,busy:3,noEarly:true,noOutage:true}],
      ["late-only-joint-fit",{cap:6,busy:3,noEarly:true,noOutage:true}]
    ]) {
    const regime={cap:5,busy:3,grant:true,stale:false,nearProbe:true,...patch};
    const worlds=supports(d,regime), plans=options(d,regime.noEarly);
    const run=operation(regime.cap,d.visit,d.audit), required=obligations(d);
    const result=synthesize(worlds,plans,d.menu,run,required);
    const alternative=direct(worlds,plans,d.menu,run,required);
    assert(JSON.stringify(result.map(x=>x.plan.id))===JSON.stringify(alternative),"baseline");
    const budgets=result.map(x=>{
      const replays=worlds.map(w=>run(w,x.plan,x.decide));
      assert(replays.every((r,i)=>required(worlds[i],r)),"rerun");
      return [x.plan.id,Math.max(...replays.map(r=>r.ledger.wire))];
    });
    for (const w of worlds) {
      const refused=run(w,{dock:0,stage:"none",encoding:"none",probe:"none"},()=>null);
      assert(refused.movement===null&&refused.output===null&&refused.ledger.other,"refusal");
    }
    results[k]={worlds:worlds.length,plans:plans.length,budgets};
  }
  report[d.name]=results;
}
assert(report.visit["empty-budget"].budgets.length===0,"no early probe workaround");
assert(report.audit["empty-budget"].budgets.length===4,"expired debit is not deleted data");
assert(report.joint["one-more"].budgets.length===4,"combined");
assert(report.joint["near-occupied"].budgets.every(([p])=>p.startsWith("1/")),"shadow dock");
assert(report.joint["near-no-probe"].budgets.length===0,"joint disjunction is not two separate capacities");
assert(report.joint["missing-grant"].budgets.length===0,"retired cannot read");
assert(report.joint["bad-ordinal"].budgets.every(([p])=>p.includes("/full/")),"basis-qualified provenance");
assert(report.joint["no-early"].budgets.length===0,"shared outage");
assert(report.visit["late-only-pair"].budgets.length===2 &&
       report.audit["late-only-pair"].budgets.length===2 &&
       report.joint["late-only-pair"].budgets.length===0,"local admission does not compose");
assert(report.joint["late-only-joint-fit"].budgets.length===2,"joint fit at exactly six");
return report;

})();
console.log(JSON.stringify(report));
