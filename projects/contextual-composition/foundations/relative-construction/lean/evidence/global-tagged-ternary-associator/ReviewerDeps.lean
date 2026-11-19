import Lean.Util.FoldConsts
import ContextualComposition.JoinedChartFrames
open Lean Elab Command ContextualComposition.GrothendieckStep
private partial def collect (env : Environment) (todo : List Name) (done : NameSet) : NameSet := Id.run do
  match todo with
  | [] => return done
  | n :: ns =>
    if done.contains n || !( `ContextualComposition).isPrefixOf n then return collect env ns done
    let seen := done.insert n
    match env.find? n with
    | none => return collect env ns seen
    | some c => return collect env (c.getUsedConstantsAsSet.toList ++ ns) seen
run_cmd do
  let e ← getEnv
  for n in [``JoinedBinary.joined,``JoinedTarget.comparison,``JoinedChartFrames.joinFirst,``JoinedChartFrames.joinLast] do
    let d := collect e [n] {}
    for k in [``TaggedTripleFaces.first,``TaggedTripleFaces.last,``TaggedTripleFaces.sourceCorner,
      ``JoinedBinary.compatible,``JoinedTarget.square,``JoinedChartFrames.targetTest,``JoinedChartFrames.byCharts] do
      if d.contains k then throwError "Construction {n} depends on {k}."
  let q := collect e [``JoinedChartFrames.byCharts] {}
  for k in [``JoinedTarget.square] do
    if q.contains k then throwError "Chart proof uses direct proof via {k}."
  for k in [``TaggedSquareRecognition.onCharts,``TaggedFixedSquare.fixed,``JoinedChartFrames.targetTest] do
    unless q.contains k do throwError "Expected prior chart dependency missing: {k}."

  for n in [``JoinedBinary.joined,``JoinedTarget.joinedPrefix] do
    if (collect e [n] {}).contains ``MovingCell.cell then throwError "Binary normalization or prefix uses historical binary cell"
  for n in [``JoinedTarget.comparison,``JoinedTarget.joinedSuffix,``JoinedChartFrames.joinLast] do
    unless (collect e [n] {}).contains ``ProjectedCharts.rightOver do throwError "Historical over-base proof no longer present"
  unless (collect e [``ProjectedCharts.rightOver] {}).contains ``MovingCell.cell do throwError "Historical proof dependency changed"
