#define main prior_subt_test
#include "subt/replay.cpp"
#undef main
static bool action(World& w, char a, char last, bool early)
{
 if(early)
 {
  if(a=='w')return false;
  assert(a=='p');
  return w.send("P","Base",3,0);
 }
 if(a=='s')return false;
 if(a=='a')
 {
  if(last=='G')return false;
  return w.send("P","Base",3,1);
 }
 assert(a=='b');
 if(w.carried_copy.empty())return false;
 return w.send("Q","Base",(unsigned)w.carried_copy.size(),1);
}
int main(int argc,char** argv)
{
 const bool runtime=argc==3;
 const char prefix=runtime?argv[1][0]:'?';
 const char on_miss=runtime?argv[2][0]:'?';
 // Independent reconstruction from the chosen prefix and a native cycle.
 for(char h:{'G','F','Z'})for(char early:{'w','p'})for(char late:{'s','a','b'})
 {
  if(runtime && (h=='Z' || early!=prefix || late!=on_miss))continue;
  World w(5);
  if(h=='F')
  {
   (void)w.send("P","Q",3,-2);
   assert(w.carried_copy==std::string(3,'a'));
  }
  // An expired early copy on P uses no P capacity at t=0. It remains in Q's
  // receiving/custody state at the application layer even after rate expiry.
  w.path_available=h=='G';
  const bool early_done=action(w,early,h,true);
  unsigned debit=0;
  // A no-op does not call attempt_send and lazily prunes no timestamps.
  // Recover the logical observed live burden rather than the raw counter.
  for(const auto& [stamp,size]:w.state("P").bytes_sent)
   if(-1<=stamp && stamp<=0)debit+=size;
  if(h!='G')w.recover();
  else w.path_available=false;
  const char actual_next=(runtime && early_done)?'s':late;
  const bool final_done=early_done||action(w,actual_next,h,false);
  assert(w.recv==unsigned(final_done));
  std::cout<<h<<early<<actual_next<<" "<<early_done<<" "<<final_done<<" "<<debit<<" "<<!w.carried_copy.empty()<<"\n";
 }
}
