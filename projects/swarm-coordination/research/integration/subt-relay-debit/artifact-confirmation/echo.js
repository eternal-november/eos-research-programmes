// Translation of the SELECTED callbacks; "draft repair" switches control
// no other middleware. All report bodies are legitimate observed values.
function forwards(from,data,detachElse) {
 const legs=[];
 if(from==="Scout")legs.push(["Base",data]);
 if(!detachElse||from==="Base")legs.push(["Scout",data]);
 return legs;
}
function inspect(kind,key,v,typed) {
 if(!typed)return false; // flag cleared by the bound tutorial callback
 return !(v.kind==="accepted-score" && v.key===key && v.certifies && v.from==="Relay");
}
function tryLegs({S,C,U,direct,returnPath,correct,typed}) {
 let debit=U, gotBase=false, gotScout=false,pending=true;
 const data={kind:"artifact",key:"r",from:"Relay",bytes:S};
 for(const [dest,p] of forwards("Scout",data,correct)){
  if(debit+p.bytes>C)continue;
  debit+=p.bytes;
  if(dest==="Base"&&direct)gotBase=true;
  if(dest==="Scout"&&returnPath){gotScout=true;pending=inspect(p.kind,"r",p,typed);}
 }
 return {debit,gotBase,gotScout,pending};
}
let cases=0;
for(let S=1;S<=20;S++)for(let C=0;C<=45;C++)for(let U=0;U<=C;U++)
for(const direct of [false,true])for(const returnPath of [false,true]){
 const bad=tryLegs({S,C,U,direct,returnPath,correct:false,typed:false});
 if(bad.gotBase!==(C-U>=S&&direct)||bad.gotScout!==(C-U>=2*S&&returnPath)||
    (!bad.pending&&!bad.gotBase)!==(C-U>=2*S&&returnPath&&!direct))throw Error("bad");
 for(const [correct,typed] of [[true,false],[false,true],[true,true]]){
  let good=tryLegs({S,C,U,direct,returnPath,correct,typed});
  if(!good.pending||good.gotBase!==bad.gotBase)throw Error("guard");
 }
 cases++;
}
const closure={kind:"accepted-score",key:"r",from:"Relay",certifies:false};
const stale={kind:"accepted-score",key:"old",from:"Relay",certifies:true};
const matching={...closure,certifies:true};
const controls=[inspect("", "r",closure,true),inspect("", "r",stale,true),inspect("", "r",matching,true)];
if(JSON.stringify(controls)!=="[true,true,false]")throw Error("controls");
console.log({cases,controls});
