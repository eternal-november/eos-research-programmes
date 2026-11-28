#include "cut_contract.h"
#include <iostream>
#include <stdexcept>
#include <string>
int main(int argc,char**argv){
    if(argc!=6)return 2;
    std::string act=argv[1];
    if(act!="inspect" && act!="effect")return 2;
    auto bit=[&](int i){const std::string s=argv[i];if(s!="0"&&s!="1")throw std::logic_error("not a bit");return s=="1";};
    auto p=cut::Profile{act=="inspect"?cut::Act::inspect:cut::Act::effect,bit(2),bit(3),bit(4),bit(5)};
    std::cout<<static_cast<unsigned>(cut::check(p))<<"\n";
}
