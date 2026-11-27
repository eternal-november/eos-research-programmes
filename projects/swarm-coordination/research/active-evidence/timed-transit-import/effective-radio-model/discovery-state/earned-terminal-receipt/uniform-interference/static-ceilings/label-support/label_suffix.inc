   static const std::array<std::string,5> keys{"IR:0/run7","IR:1/run7","IR:2/run7","IR:3/run7","IR:4/run7"};
   const std::string b="IER:1/run7";
   std::set<char> used_tags;
   std::set<std::string> used_keys;
   std::array<int,5> arrivals{};
   int bDone=0, drops=0, issued=0;
   char current_tag='?';
   w.app.callbacks["Base:7"]=[&](auto sender,auto,auto,auto body){
      if(sender=="R"&&body==b){++bDone;return;}
      auto where=std::find(keys.begin(),keys.end(),body);
      assert((sender=="P"||sender=="Q")&&where!=keys.end());
      ++arrivals[where-keys.begin()];used_keys.insert(body);used_tags.insert(current_tag);
   };
   auto dispatch=[&](double t,const std::string& from,const std::string& dst,const std::string& payload){
      now=t;w.b.incomingMsgs.push_back({from,dst,payload});w.b.DispatchMessages();
   };
   dispatch(4.0,"Side","Sink","W");
   double time=4.125;
   for(char letter:timeline){
     if(letter=='|'){
       if(mode=="clear")used_tags.clear();
       continue;
     }
     assert(time<5.0);
     if(letter=='B'){dispatch(time,"R","Base",b);time+=.125;continue;}
     assert(letter>='0'&&letter<='4');
     auto id=letter-'0';
     current_tag=tags.at(id);
     bool suppress=false;
     if(mode=="qualified")suppress=used_keys.count(keys[id]);
     else if(mode!="blind")suppress=used_tags.count(current_tag);
     if(suppress)++drops;
     else dispatch(time,(++issued)%2?"P":"Q","Base",keys[id]);
     time+=.125;
   }
   for(int c:arrivals)std::cout<<c<<' ';
   std::cout<<bDone<<' '<<drops<<' '<<w.state("Base").bytes_received_this_epoch<<' '<<independent<<std::endl;
  }
 }
}
