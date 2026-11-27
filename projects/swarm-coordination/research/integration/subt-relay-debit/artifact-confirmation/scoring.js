const artifactScore=(st, report)=>{
 let effect=0,status="scored",delta=0,dup=false;
 if(st.finished)status="scoring finished";
 else if(st.record.size>=st.cap){status="report limit exceeded";st.finished=true;}
 else if(st.record.has(report)) {delta=st.record.get(report);dup=true;}
 else {
   delta=st.freshScore(report);
   st.record.set(report,delta);
   st.total+=delta;
   if(st.total>=st.max)st.finished=true;
   else if(st.record.size>=st.cap){status="report limit reached";st.finished=true;}
   effect=delta;
 }
 return {visible:{report, id:st.record.size,status,delta},effect,dup};
};
const create=(cap,max,F=()=>1)=>({cap,max,total:0,record:new Map,finished:false,freshScore:F});
let qualified=[];
let amount=0;
for(let cap=2;cap<=32;cap++)for(let max=2;max<=36;max++){
 const one=create(cap,max), two=create(cap,max);
 const observedFirst=artifactScore(one,"r");
 artifactScore(two,"x");
 for(let q=1;q<Math.min(cap,max)-1;q++){artifactScore(one,"s"+q);artifactScore(two,"s"+q);}
 if(one.finished||two.finished)throw Error();
 let ran=artifactScore(one,"r");
 if(ran.effect!==0||!ran.dup||one.total!==two.total||ran.visible.id!==Math.min(cap,max)-1)throw Error();
 artifactScore(one,"last");artifactScore(two,"last");
 const a=artifactScore(one,"r"),b=artifactScore(two,"r");
 if(!one.record.has("r")||two.record.has("r")||!one.finished||!two.finished||
    JSON.stringify(a.visible)!==JSON.stringify(b.visible)||one.total!==two.total)throw Error();
 if(cap===3&&max===5)qualified=[observedFirst.visible,ran.visible,a.visible];
 ++amount;
}
function drain(xs,swap){
 let queue=[],detached=[],transmitted=[];
 for (const step of xs) {
  if(step==="take"){
   detached=queue.slice();
   if(swap)queue=[];
  } else if(step==="emit"){
   transmitted.push(...detached);
  } else if(step==="clear"){
   if(!swap)queue=[];
  } else queue.push(step);
 }
 return {transmitted,remaining:queue};
}
let orders=0;
for(let n=0;n<=6;n++){
 for(let i=0;i<=n;i++)for(let j=i;j<=n;j++)for(let k=j;k<=n;k++){
   const xs=[];for(let q=0;q<=n;q++){
     if(q===i)xs.push("take");
     if(q===j)xs.push("emit");
     if(q===k)xs.push("clear");
     if(q<n)xs.push(q);
   }
   const D=drain(xs,false),S=drain(xs,true);
   if(n-D.transmitted.length-D.remaining.length!==k-i)throw Error();
   if(S.transmitted.length+S.remaining.length!==n||
      new Set([...S.transmitted,...S.remaining]).size!==n)throw Error();
   orders++;
 }
}
console.log({artifactPairs:amount,queueOrders:orders,qualified});
