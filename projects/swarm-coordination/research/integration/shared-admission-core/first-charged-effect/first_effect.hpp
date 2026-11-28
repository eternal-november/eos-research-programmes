#pragma once
#include <cstddef>
#include <optional>

// Run in one serialized source loop. Inspect must be read-only, and no
// actor may change a checked premise before the first committed effect.
// Commit is called at most once, not retried after a charged failure.
template<class Inspect, class Commit>
bool dispatch_one(std::size_t n, Inspect inspect, Commit commit){
  for(std::size_t k=0;k<n;++k)
    if(inspect(k)){commit(k);return true;}
  return false;
}

template<class Inspect>
std::optional<std::size_t> propose(std::size_t n, Inspect inspect){
  std::optional<std::size_t> choice;
  dispatch_one(n,inspect,[&](std::size_t k){choice=k;});
  return choice;
}
