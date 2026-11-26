using namespace nav2_collision_monitor;
int main() {
  auto take=[](int p0,int p1,int b0,int b1,bool shift,bool independent,int stamp) {
    TF tf{p0,p1,b0,b1};
    Scan sc;sc.tf_manager_=&tf;sc.base_shift_correction_=shift;
    sc.global_frame_id_=independent?"motion_reference":"map";
    sc.data_->header.stamp={stamp};
    // A fixed wall at x=4; local measurement at the chosen acquisition instant.
    sc.data_->ranges={float(4-(stamp?p1:p0))};
    std::vector<Point> data;
    assert(sc.getSourceData({1},data)&&data.size()==1&&tf.called);
    return data.front().x;
  };
  assert(take(0,1,8,8,true,false,0)==3);
  double crossed=take(0,1,8,6,true,false,0);
  assert(crossed==5);
  assert(take(0,1,8,6,true,true,0)==3);
  assert(take(0,1,8,6,true,false,1)==3);
  double skipped=take(0,1,8,6,false,false,0);
  assert(skipped==4);
  std::cout<<"cross-generation map pair "<<crossed<<"; true current range 3\n"
      <<"stable motion reference and fresh scan 3; uncorrected delayed scan "<<skipped<<"\n";
  int checked=0;
  for(int p0=-2;p0<=0;p0++)for(int p1=0;p1<=2;p1++)
    for(int b0=-2;b0<=2;b0++)for(int b1=-2;b1<=2;b1++){
      assert(take(p0,p1,b0,b1,true,false,0)==4-p1+b0-b1);
      assert(take(p0,p1,b0,b1,true,true,0)==4-p1);
      assert(take(p0,p1,b0,b1,true,false,1)==4-p1);
      assert(take(p0,p1,b0,b1,false,false,0)==4-p0);
      ++checked;
    }
  std::cout<<"matched declared transforms "<<checked<<"\n";
}
