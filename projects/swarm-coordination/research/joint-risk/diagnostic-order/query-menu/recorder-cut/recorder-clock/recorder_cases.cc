#define main unused_original_main
#include "replay.cpp"
#undef main
#include <sstream>
int main() {
  RecorderImpl r;
  const auto a=r.create_subscription("A","fixture",rclcpp::QoS{});
  const auto b=r.create_subscription("B","fixture",rclcpp::QoS{});
  // Use a deterministic delivery order independent of camera acquisition.
  std::string label,topic,stamp;
  unsigned idx,flag,serial=0;
  while(std::cin>>label>>topic>>idx>>stamp>>flag) {
    assert((topic=="A"||topic=="B") && flag<2);
    std::ostringstream out;
    out<<label<<','<<idx<<','<<stamp<<','<<flag;
    const long tx=1000+(serial++)*10;
    const auto sub=topic=="A"?a:b;
    sub->callback(std::make_shared<const rclcpp::SerializedMessage>(
        rclcpp::SerializedMessage{out.str()}),rclcpp::MessageInfo{{tx,tx+3,serial}});
  }
  for(auto& [t,p,rx,tx,k]:r.writer_->rows)
    std::cout<<t<<' '<<p<<' '<<rx<<' '<<tx<<' '<<k<<'\n';
}
