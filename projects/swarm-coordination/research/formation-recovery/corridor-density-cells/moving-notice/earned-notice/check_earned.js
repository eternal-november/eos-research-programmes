function env(H,t) {
 if(t<=H/2)return [t*t,2*t];
 return [H*H/2-(H-t)**2,2*(H-t)];
}
// State is expressed in 9x position and velocity until branch combination.
function centre9(t,choice) {
 if(t<=.75)return [8*t*t,16*t];
 if(t<=1.5)return [9-8*(1.5-t)**2,16*(1.5-t)];
 if(t<=2||choice==="negative"){
   const [x,v]=env(1.5,t-1.5);return [9-9*x,-9*v];
 }
 if(t<=2.5){const q=t-2;return [27/4-9*q+9*q*q,-9+18*q];}
 return [9/2,0];
}
function centre45(t,selected){
 const a=centre9(t,"negative"),b=centre9(t,"positive");
 if(selected===null)return a.map((z,j)=>4*z+b[j]);
 return (selected==="negative"?a:b).map(z=>5*z);
}
let checks=0,qualified=0,short=0;
for(const window of [[33.75,45],[33.75,44.75]]){
 let within=0;
 for(let i=128;i<=256;i++){
   const x=centre45(i/128,null)[0];
   if(window[0]<=x&&x<=window[1])within++;
 }
 qualified+=within===129;
 short+=within;
}
if(qualified!==1||short>=258)throw Error("acquisition");
function outcome(hidden,valid,erased){return valid&&!erased?hidden:null;}
for(const hit of [true,false])for(const erased of [true,false]){
 let lc=outcome("positive",hit,erased),rc=outcome("negative",hit,erased);
 let last = null;
 for(let i=0;i<=384;i++){
  const t=i/128,L=centre45(t,lc),R=centre45(t,rc),[u,v]=env(3,t);
  for(const [j,s] of [L,R].entries()){
   const [x,w]=s;
   if(Math.abs(x)>45*u||Math.abs(w)>45*v)throw Error("gap or speed");
   if(last&&Math.abs(w-last[j][1])>90/128)throw Error("accel");
   if((i===0||i===384)&&w!==0)throw Error("stop");
  }
  if(i<=256&&(L[0]!==R[0]||L[1]!==R[1]))throw Error("receipt oracle");
  if(i===384){
    const blind=45*4.5, need=45*(37/8);
    if(lc!==null&&(blind+L[0]<need||blind-R[0]<need))throw Error("served");
    if(lc===null&&(L[0]!==0||R[0]!==0))throw Error("fallback");
  }
  last=[L,R];checks++;
 }
}
if(centre45(1,null)[0]!==35||centre45(1.5,null)[0]!==45||centre45(2,null)[0]!==33.75)throw Error("dwell extrema");
if(!(Math.sqrt(3/2)+1+Math.sqrt(7/4)>3))throw Error("stationary lower");
console.log({checks,validDwellWindows:qualified,blind:4.5,qualified:37/8,
  dwellPositions:[35/45,1,3/4],stopToDwellLower:Math.sqrt(3/2)+1+Math.sqrt(7/4)});
