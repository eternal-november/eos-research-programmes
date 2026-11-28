"use strict";
const fs=require("fs"),crypto=require("crypto");
const pin=process.argv[2];
const input=JSON.parse(fs.readFileSync(0,"utf8"));
const source=fs.readFileSync(pin,"utf8");
const blob=crypto.createHash("sha1").update("blob "+Buffer.byteLength(source)+"\0").update(source).digest("hex");
if(blob!==process.argv[3])throw Error("model core version");
const i=source.indexOf("function synthesize("),j=source.indexOf("const assert =");
if(i<0||j<=i)throw Error("model boundaries");
const {synthesize,direct}=Function(source.slice(i,j)+";return {synthesize,direct}")();
const worlds=input.worlds.map((_,id)=>({id}));
const plans=input.plans.map((p,id)=>({id,p}));
function execute(w,p,k){
   const obs=input.worlds[w.id][p.id];
   const view=obs.view;
   if(view===null)return {view,ok:false};
   return {view,ok:obs.winners.includes(k(view))};
}
const required=(_w,r)=>r.ok;
const results=synthesize(worlds,plans,input.actions,execute,required);
const comparator=direct(worlds,plans,input.actions,execute,required);
if(JSON.stringify(results.map(p=>p.plan.id))!==JSON.stringify(comparator))throw Error("differential");
console.log(JSON.stringify(results.map(({plan,decide})=>{
  const views=Array.from(new Map(worlds.map(w=>{
     const v=input.worlds[w.id][plan.id].view;
     return [JSON.stringify(v),[v,decide(v)]];
  })).values());
  return [plan.id,views];
})));
