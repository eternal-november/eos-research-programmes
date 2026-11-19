import Lean.Util.FoldConsts
import ContextualComposition.JoinedChartFrames
open Lean Elab Command ContextualComposition.GrothendieckStep
private partial def breadth (env : Environment) (front : List (Name × List Name)) (seen : NameSet) (goal : Name) : Option (List Name) := Id.run do
  if front.isEmpty then return none
  let mut nex := []
  let mut s := seen
  for (n,p) in front do
    if n == goal then return some ((n::p).reverse)
    if !s.contains n && (`ContextualComposition).isPrefixOf n then
      s := s.insert n
      if let some c := env.find? n then
        for k in c.getUsedConstantsAsSet.toList do
          if !s.contains k && (`ContextualComposition).isPrefixOf k then nex := (k,n::p)::nex
  return breadth env nex s goal
run_cmd do
  let env ← getEnv
  for a in [``JoinedBinary.joined,``JoinedBinary.vertical,``JoinedTarget.joinedPrefix,``JoinedTarget.joinedSuffix,``JoinedTarget.comparison,``JoinedChartFrames.joinFirst,``JoinedChartFrames.joinLast,``JoinedChartFrames.byCharts] do
    for b in [``MovingCell.cell,``JoinedTarget.square] do
      logInfo m!"{a} to {b}: {breadth env [(a,[])] {} b}"
