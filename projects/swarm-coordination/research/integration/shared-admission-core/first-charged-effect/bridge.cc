#include "first_effect.hpp"
extern "C" bool dispatch(std::size_t n,bool(*inspect)(std::size_t),void(*commit)(std::size_t)){
  return dispatch_one(n,inspect,commit);
}
