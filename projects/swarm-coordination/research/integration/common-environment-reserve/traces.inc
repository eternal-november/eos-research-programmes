
int main(){
 WindEffectsPrivate wind;
 EntityComponentManager e;
 e.bodies[1].pose.val.p.x=1;
 e.bodies[2].pose.val.p.x=1;
 double maximum=0,max1=0,max2=0;
 for(int i=-32;i<=32;i++){
   e.common.val.x=double(i)/16;
   e.applied.clear();
   wind.ApplyWindForce({},e);
   auto f1=e.applied.at(1).x, f2=e.applied.at(2).x;
   assert(f1==e.common.val.x&&f2==e.common.val.x);
   double a=std::max(0.0,f1),b=std::max(0.0,-f2);
   maximum=std::max(maximum,a+b);
   max1=std::max(max1,a);max2=std::max(max2,b);
 }
 assert(maximum==2&&max1+max2==4);
 // Separate declared observation histories; these are not stock reports.
 e.common.val.x=2;
 const auto fresh_at_old_cut=e.common.val.x;
 e.common.val.x=-2;
 const auto fresh_at_new_cut=e.common.val.x;
 e.applied.clear();wind.ApplyWindForce({},e);
 assert(fresh_at_old_cut==2&&fresh_at_new_cut==-2);
 assert(e.applied.at(1).x==-2&&e.applied.at(2).x==-2);
 assert(std::max(0.0,fresh_at_old_cut)+std::max(0.0,-fresh_at_new_cut)==4);
 assert(std::max(0.0,e.applied.at(1).x)+std::max(0.0,-e.applied.at(2).x)==2);
 e.common.val.x=0;
 e.bodies[1].velocity.val.x=-1;
 e.bodies[2].velocity.val.x=1;
 e.bodies[2].pose.val.p.x=2;
 e.applied.clear();wind.ApplyWindForce({},e);
 assert(e.applied.at(1).x==1&&e.applied.at(2).x==-2);
 e.bodies[1].enabled.val=false;
 e.bodies[2].pose.val.p.x=99;
 e.applied.clear();wind.ApplyWindForce({},e);
 assert(!e.applied.contains(1)&&e.applied.at(2).x==0);
 e.applied.clear();e.source=false;wind.ApplyWindForce({},e);
 assert(e.applied.empty());
 std::cout<<"65 matched common wind cases: exact joint opposing reserve 2, sum of separate maxima 4\n"
          <<"mixed authored report ages can suggest opposite simultaneous demands at one real cut\n"
          <<"same wind at two eligible links can yield opposite forces with different local state\n"
          <<"disabled link, undefined scale, and absent source follow separate selected paths\n";
}
