const a=2;
function profile(H,v,t) {
 t=Math.min(H,Math.max(0,t));
 const b=Math.min(H/2,v/a),p=H-b,vl=a*b;
 const pos=t<=b?a*t*t/2:t<=p?a*b*b/2+vl*(t-b):
  a*b*b/2+vl*(p-b)+a*((H-p)**2-(H-t)**2)/2;
 const vel=Math.min(a*t,a*(H-t),v);
 return [pos,vel];
}
const analytic=(H,v)=>H<=2*v/a?a*H*H/4:v*(H-v/a);
let cases=0,checks=0;
for(const v of [1,2,4,8])for(let k=1;k<=16;k++)for(let c=0;c<=k;c++)
 for(const scale of [0,.25,.5,.75,1]){
 const T=k/2,cut=c/2,H=T-cut;
 const D=scale*(analytic(T,v)+analytic(H,v));
 let A=0,B=0,prevF=0,prevG=0;
 for(let j=0;j<=k*4;j++){
   const t=j/8;
   const [f,vf]=profile(T,v,t),[g,vg]=profile(H,v,t-cut);
   if(j){A+=(vf+prevF)/16;B+=(vg+prevG)/16;}
   if(f!==A||g!==B||g<0||g>f||scale*(f+g)>D||scale*(f-g)>D||
      vf<vg||vf>v||vg>v||Math.abs(vf-prevF)>.25||Math.abs(vg-prevG)>.25)throw Error();
   prevF=vf;prevG=vg;checks++;
 }
 if(scale*(A+B)!==D||prevF!==0||prevG!==0)throw Error();
 cases++;
}
const T=2,t=1,v=8;
const moving=analytic(T,v)+analytic(T-t,v),rest=analytic(t,v)+2*analytic(T-t,v);
if(moving!==2.5||rest!==1.5||analytic(T,v)!==2)throw Error();

const fifths={moving:analytic(6,16)+analytic(4,16),rest:analytic(2,16)+2*analytic(4,16),blind:analytic(6,16)};
if(fifths.moving!==26||fifths.rest!==18||fifths.blind!==18)throw Error("scaled fifths");
console.log({cases,checks,moving,rest,blind:analytic(T,v),latest:"2 - sqrt(1/2)",scaledFifths:fifths});
