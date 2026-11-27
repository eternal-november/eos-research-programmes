function ex(e,f,request,erased,acked,attempt) {
 const expiry=request+5;
 let t=1,location=1,report=null,localAck=false,physicalDeposits=0;
 // Dequeueing a request may leave a debit even when Gate receives nothing.
 const knownExit=erased?null:e;
 if(knownExit===null){t++;return [t+1,t+5,1,false];}
 if(attempt==="qualified"){
   location=-f;
   t+=Math.abs(location-1);
   if(location===1)t=Math.max(t,expiry);
 } else if(attempt==="silence")t=4;
 else throw Error();
 if(location!==f && (location!==1||t>=expiry)){
   report=t+1;physicalDeposits=1;localAck=acked;
 }
 t++;
 let egress=t+Math.abs(location-e)+1;
 if(!localAck&&report===null){report=egress+4;physicalDeposits++;}
 return [egress,report,physicalDeposits,localAck];
}
const results=[];
for(const e of [-1,1])for(const f of [-1,1])for(const q of [-1,0]){
 const [escape,report,n,ack]=ex(e,f,q,false,true,"qualified");
 if(report!==(f===1?4:q+6)||escape!==report+(e===-f?1:3)||n!==1||!ack)throw Error();
 results.push({e,f,q,report,escape});
}
const controls=[
 ex(-1,-1,0,false,true,"silence"),
 ex(-1,-1,-1,false,false,"silence"),
 ex( 1,-1,0,true,false,"qualified")
];
if(JSON.stringify(controls)!==JSON.stringify([[8,12,1,false],[8,5,1,false],[3,7,1,false]]))throw Error();
console.log({results,controls});
