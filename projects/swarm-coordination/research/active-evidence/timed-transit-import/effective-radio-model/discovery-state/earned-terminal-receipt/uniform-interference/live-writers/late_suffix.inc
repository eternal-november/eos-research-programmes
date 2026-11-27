   const std::string key="IR:3/run7", other="IER:1/run7";
   std::set<std::string> exact{"IR:3/prior"};
   size_t receivedA=0,receivedB=0;
   w.app.callbacks["Base:7"]=[&](auto sender,auto,auto,auto payload){
     if((sender=="P"||sender=="Q") && payload==key){++receivedA;exact.insert(payload);}
     if(sender=="R"&&payload==other)++receivedB;
   };
   auto dispatch=[&](double t,const std::string& from,const std::string& dst,const std::string& payload){
     now=t;w.b.incomingMsgs.push_back({from,dst,payload});w.b.DispatchMessages();
   };
   unsigned skippedP=0,skippedQ=0;
   bool readAtEstimate=false;
   auto primary=[&](double at){
     if((guard=="all-inline"&&exact.count(key))||(guard=="all-stale"&&readAtEstimate)){++skippedP;return;}
     dispatch(at,"P","Base",key);
   };
   if(position=="prefix")primary(4.0);
   dispatch(4.125,"Side","Sink","W");
   readAtEstimate=exact.count(key);
   if(position=="gap")primary(4.5);
   const bool skipQ=((guard=="Q-snapshot"||guard=="all-stale")&&readAtEstimate)||
                    ((guard=="Q-inline"||guard=="all-inline")&&exact.count(key));
   if(skipQ)++skippedQ;
   else dispatch(4.625,"Q","Base",key);
   if(position=="second")primary(4.75);
   dispatch(5.0,"R","Base",other);
   const auto Bdue=receivedB;
   if(position=="after")primary(5.125);
   std::cout<<receivedA<<' '<<Bdue<<' '<<readAtEstimate<<' '
            <<skippedP<<' '<<skippedQ<<' '
            <<w.state("P").bytes_sent_this_epoch<<' '<<w.state("Q").bytes_sent_this_epoch<<' '
            <<w.state("Base").bytes_received_this_epoch<<' '<<independent<<std::endl;
  }
 }
}
