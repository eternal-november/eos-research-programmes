import Lean.Util.FoldConsts
import ContextualComposition.JoinedChartFrames
open Lean Elab Command ContextualComposition.GrothendieckStep
private partial def walkNative (env : Environment) (todo : List Name) (seen : NameSet) : NameSet := Id.run do
  match todo with
  | [] => return seen
  | n :: tail =>
    if seen.contains n || !( `ContextualComposition.GrothendieckStep).isPrefixOf n then return walkNative env tail seen
    let seen := seen.insert n
    match env.find? n with
    | none => return walkNative env tail seen
    | some ci => return walkNative env (ci.getUsedConstantsAsSet.toList ++ tail) seen
run_cmd do
  let env ← getEnv
  let target := walkNative env [``JoinedTarget.comparison] {}
  for n in [``JoinedBinary.joined,``JoinedBinary.readJoined,``MovingCoordinates.recover,``MovingCell.right,``TaggedTripleFaces.ordinary,``SuffixCell.foldIsoCell] do
    unless target.contains n do throwError "Expected native construction dependency missing: {n}"
  for n in [``TaggedTripleFaces.first,``TaggedTripleFaces.last,``TaggedTripleFaces.sourceCorner,``JoinedBinary.compatible,
    ``JoinedTarget.square,``JoinedChartFrames.byCharts,``JoinedChartFrames.targetTest] do
    if target.contains n then throwError "Forbidden dependency in construction of target: {n}"
  for f in [``JoinedChartFrames.joinFirst,``JoinedChartFrames.joinLast] do
    let frame := walkNative env [f] {}
    for n in [``JoinedTarget.comparison,``TaggedTripleFaces.first,``TaggedTripleFaces.last,``TaggedTripleFaces.sourceCorner,``JoinedTarget.square] do
      if frame.contains n then throwError "Corner frame {f} depends on comparison being tested: {n}"
