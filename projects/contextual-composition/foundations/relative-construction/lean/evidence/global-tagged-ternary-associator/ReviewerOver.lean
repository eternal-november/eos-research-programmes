import Lean.Util.FoldConsts
import ContextualComposition.JoinedChartFrames
namespace ContextualComposition.GrothendieckStep.ReviewerOver
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativePacked MovingCoordinates MovingCell ProjectedCharts TaggedTripleFaces WholeEvaluator
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
theorem nativeRightOver : rightTotal S Y ⋙ proj S Y = base S Y :=
  (projected (proj S Y) (JoinedBinary.joined S Y) (JoinedBinary.projectedJoined S Y)).trans (binaryOver S Y)
theorem nativeVertical : SuffixCell.vertical (base S Y) (proj S Y) (nativeRightOver S Y) (binaryOver S Y) (JoinedBinary.joined S Y).hom :=
  fun x => (JoinedBinary.projectedJoined S Y x).choose_spec
noncomputable def nativeSuffix := isoWhiskerLeft (regrouping S Y) (isoWhiskerRight
  (SuffixCell.foldIsoCell Y (ChartRealization.twice S Y) (U S).dest (pairSpan S).source (pairSpan S).dest
    (nativeRightOver S Y) (binaryOver S Y) (JoinedBinary.joined S Y) (nativeVertical S Y)) (outer S Y))
noncomputable def nativeComparison := JoinedTarget.joinedPrefix S Y ≪≫ eqToIso (ordinary S Y) ≪≫ (nativeSuffix S Y).symm
example : nativeComparison S Y = JoinedTarget.comparison S Y := rfl
end ContextualComposition.GrothendieckStep.ReviewerOver
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
  let ds := collect e [``ReviewerOver.nativeComparison] {}
  for k in [``MovingCell.cell,``JoinedBinary.compatible,``JoinedTarget.comparison,``JoinedTarget.square] do
    if ds.contains k then throwError "Proof-independent native construction depends on {k}."
