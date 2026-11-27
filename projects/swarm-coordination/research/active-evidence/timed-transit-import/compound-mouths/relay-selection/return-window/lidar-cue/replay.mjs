import fs from "node:fs";
import {createHash} from "node:crypto";
const checksum=b=>createHash("sha1").update("blob "+b.length+"\0").update(b).digest("hex");
function rays(s,robot,more,src){
 const extract=(x,k)=>x.match(new RegExp("<"+k+"(?: [^>]*)?>([^<]+)</"+k+">"))[1].trim();
 const sensor=(x,n)=>{
  const b=x.match(new RegExp('<sensor name="'+n+'"[^>]*>([\\s\\S]*?)</sensor>'))[1];
  const ax=k=>{const z=b.match(new RegExp("<"+k+">([\\s\\S]*?)</"+k+">"))[1];
   return ["samples","resolution","min_angle","max_angle"].map(x=>Number(extract(z,x)));
  };
  const [min,max]=["min","max"].map(k=>Number(extract(b.match(/<range>([\s\S]*?)<\/range>/)[1],k)));
  return {h:ax("horizontal"),v:ax("vertical"),p:extract(b,"pose").split(/\s+/).map(Number),min,max,hz:+extract(b,"update_rate")};
 };
 const tile=n=>s.match(new RegExp("<name>tile_"+n+"</name>\\s*<pose>([^<]+)</pose>"))[1].trim().split(/\s+/).slice(0,3).map(Number);
 const read=sensor(robot,"front_laser"),dense=sensor(more,"front_laser");
 const [midX,midY,midZ]=[(tile(13)[0]+tile(42)[0])/2,(tile(13)[1]+tile(42)[1])/2,0];
 const lo=[midX-.5,midY-.05,midZ+.2],hi=[midX+.5,midY+.05,midZ+.7];
 const count=(data,id,yaw=0,zBias=0)=>{
  const [dx,dy,dz,r,p,sy]=data.p;
  if(r||p||sy||data.h[1]!==1||data.v[1]!==1)throw Error("unsupported SDF");
  const pos=tile(id);
  pos[0]+=Math.cos(yaw)*dx-Math.sin(yaw)*dy;
  pos[1]+=Math.sin(yaw)*dx+Math.cos(yaw)*dy;
  pos[2]+=dz+zBias;
  const [n,,a,b]=data.h,[m,,c,d]=data.v;
  let hits=0,maxHitDist=0,minHitDist=Infinity,rings=new Set(),heights=[];
  for(let j=0;j<m;j++){
   const v=c+j*(d-c)/(m-1);
   heights.push(pos[2]+Math.tan(v)*(pos[1]-midY));
   for(let i=0;i<n;i++){
    const h=yaw+a+i*(b-a)/(n-1);
    const dir=[Math.cos(v)*Math.cos(h),Math.cos(v)*Math.sin(h),Math.sin(v)];
    let l=data.min, u=data.max;
    for(let k=0;k<3;k++){
     if(Math.abs(dir[k])<1e-12){if(pos[k]<lo[k]||pos[k]>hi[k]){u=-1;break}continue}
     const a=(lo[k]-pos[k])/dir[k],b=(hi[k]-pos[k])/dir[k];
     l=Math.max(l,Math.min(a,b));u=Math.min(u,Math.max(a,b));
    }
    if(l<=u){hits++;rings.add(j);minHitDist=Math.min(l,minHitDist);maxHitDist=Math.max(l,maxHitDist)}
   }
  }
  const clean=x=>Number(x.toFixed(6));
  return {id,hits,rings:[...rings],dist:hits?[clean(minHitDist),clean(maxHitDist)]:null,
          innerHeights:heights.slice(m/2-1,m/2+1).map(clean)};
 };
 const far=count(read,16),near=count(read,42),denseFar=count(dense,16);
 if(far.hits!==0||!near.hits||!denseFar.hits||read.hz!==10||read.max!==100)throw Error("geometry");
 const analytic=(read.v[3]-read.v[2])/(read.v[0]-1)/2;
 const minDist=37.5-.05-Math.hypot(read.p[0],read.p[1]);
 const low=read.p[2]+.05-Math.tan(analytic)*minDist;
 const high=read.p[2]-.05+Math.tan(analytic)*minDist;
 if(!(low<lo[2]&&high>hi[2]))throw Error("strip");
 let poseGrid=0;
 for(let y=0;y<60;y++)for(let z=-5;z<=5;z++){
  if(count(read,16,y*Math.PI/30,z/100).hits)throw Error("pose perturbation");
  poseGrid++;
 }
 const math=(p,ph)=>p-ph%p;
 let phaseCases=0;
 for(const p of [25,50,100,200])for(const lag of [0,1,7,20,50])for(let budget=0;budget<=250;budget++){
  const holds=Array.from({length:p},(_,phase)=>math(p,phase)+lag<=budget).every(Boolean);
  if(holds!==(p+lag<=budget))throw Error("phase");
  phaseCases++;
 }
 if(!src.launch.includes('front_laser/scan/points@sensor_msgs/PointCloud2')||
    src.launch.includes('set_rate_relay')||!src.spawner.includes('costar_husky_sensor_config_1 vehicle_topics.launch')||
    !src.gpu.includes('this->dataPtr->pointPub.HasConnections()')||
    !src.render.includes('(vmax-vmin) / static_cast<double>(this->dataPtr->h2nd-1)'))throw Error("pinned source interface");
 return {tiles:[tile(16),tile(42),tile(13)],slab:[lo,hi],far,near,denseFar,poseGrid,phaseCases,strip:[low,high].map(x=>Number(x.toFixed(6)))};
}
const root=new URL("./SOURCE.tsv",import.meta.url),src={};
for(const row of fs.readFileSync(root,"utf8").trimEnd().split("\n")){
 const [name,,,,sha]=row.split("\t");
 const b=fs.readFileSync(new URL(name,root));
 if(checksum(b)!==sha)throw Error("source mismatch "+name);
 src[name]=b.toString("utf8");
}
process.stdout.write(JSON.stringify(rays(src["world.sdf"],src["costar.sdf"],src["marble.sdf"],src),null,2)+"\n");
