// Node.js: node handoff_reuse.js
// Times 1..4; null means no ready notification. Deadline is end of tick 2.
const D=2, E=[1,2], times=[null,1,2,3,4];
const assert=(v,msg)=>{if(!v)throw Error(msg);};
const range=(vals,n)=>n===0?[[]]:vals.flatMap(x=>range(vals,n-1).map(xs=>[x,...xs]));
// Direct argument: reuse the same receiver proof on actual timed runs.
// Each branch has one job. Only the first well-typed receipt settles it.
function directRun(kind, sourceReady, lag, busy) {
  let ready=false, settled=null, maintenance=0, uses=0;
  for(let t=1;t<=4;t++){
    if(t===sourceReady)ready=true;
    if(t===busy){maintenance++;continue;}
    if(ready && t>=sourceReady+lag && settled===null){
      settled={kind,t}; uses++;
    }
  }
  assert(maintenance===1 && uses<=1,"capacity or at most one");
  return settled;
}
const directProof = records => records.every(r=>r!==null && r.t<=D);
function direct(source) {
  return ["old","fresh"].map(k=>directProof(E.map((b,i)=>directRun(k,source[k][i],source.lag[i],b))));
}
// Context route: compose source readiness and the unchanged gate on the
// same maintenance epoch. Infinity is the raw no-service outcome.
const rdy = (a,l)=>a===null?Infinity:a+l;
const gate = (r,b)=>r+(r===b?1:0);
const retained = (source,kind)=>E.map((b,i)=>({b,t:gate(rdy(source[kind][i],source.lag[i]),b)}));
const contract = rows=>rows.every(({t})=>t<=D);
const contextual = source=>["old","fresh"].map(k=>contract(retained(source,k)));
// Exact symbolic deadline criterion: either ready strictly before the
// deadline, or ready on the deadline with a nonbusy deadline slot.
const exact = s=>["old","fresh"].map(k=>E.every((b,i)=>{
  const r=rdy(s[k][i],s.lag[i]);
  return r<D || (r===D && b!==D);
}));
const iso=(x,y)=>JSON.stringify(x)===JSON.stringify(y);
let variants=0,branchTraces=0; const classes={};
for(const [o1,o2,f1,f2] of range(times,4)) for(const lag of range([0,1,2],2)){
  const s={old:[o1,o2],fresh:[f1,f2],lag};
  const a=direct(s), b=contextual(s), c=exact(s);
  assert(iso(a,b)&&iso(b,c),"proof comparison");
  // Also compare the raw through-tick-4 rows, not just the two Booleans.
  for(const k of ["old","fresh"]) for(const [i,e] of E.entries()){
    const t=gate(rdy(s[k][i],lag[i]),e);
    assert((directRun(k,s[k][i],lag[i],e)?.t??null)===(t<=4?t:null),"raw row");
    branchTraces++;
  }
  const key=a.map(Number).join("");
  classes[key]=(classes[key]??0)+1; variants++;
}
const baseline={old:[1,1],fresh:[2,1],lag:[0,0]};
const harmless={old:[2,1],fresh:[2,1],lag:[0,0]};
const stopFresh={...baseline,fresh:[null,null]};
const delayFresh={...baseline,fresh:[1,2]};
const deliveryHold={...baseline,lag:[0,1]};
assert(iso(contextual(baseline),[true,true]),"baseline");
assert(iso(contextual(harmless),[true,true]),"harmless disclosure change");
assert(iso(contextual(stopFresh),[true,false]),"old carries but new does not");
assert(iso(contextual(delayFresh),[true,false]),"same marginals different joint");
assert(iso(contextual(deliveryHold),[false,false]),"joint delivery change");
assert(iso([...delayFresh.fresh].sort(),[...baseline.fresh].sort()),"same source marginal");
console.log(JSON.stringify({variants,branchTraces,classes,examples:
  [baseline,harmless,stopFresh,delayFresh,deliveryHold].map(contextual)}));
