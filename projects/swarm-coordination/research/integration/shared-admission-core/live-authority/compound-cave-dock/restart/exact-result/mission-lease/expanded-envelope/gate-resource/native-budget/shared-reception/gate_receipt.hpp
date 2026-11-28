#pragma once

// Endpoint policy for a fixed role. A negative scope is an ordinary report.
// Caller supplies the verified read / hold; this does not discover either.
inline int qualification(bool source_qualified, int source_epoch){
  return source_qualified ? source_epoch : -1;
}
inline bool may_use(int scope, int live_epoch, bool entitled, bool held_through_use){
  return scope >= 0 && scope == live_epoch && entitled && held_through_use;
}
