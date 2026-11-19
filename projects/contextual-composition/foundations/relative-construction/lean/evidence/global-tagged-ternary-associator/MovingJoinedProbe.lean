import ContextualComposition.JoinedChartFrames
import ContextualComposition.TripleFaceBase
import ContextualComposition.TaggedTripleCover
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativePacked NativeCleavage
namespace MovingTripleProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
inductive B | pt
instance : Category B where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev b := B.pt
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of B)
  extend _ := 𝟭 _
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
abbrev Y := P.grades
def no : b ⟶ b := fun _ => false
def yes : b ⟶ b := fun _ => true
open SpanApex TaggedTripleFaces
def letter : (power S 1).apex := pair P.grades (𝟭 B) b b
def atom (a d : b ⟶ b) : letter ⟶ letter := arrow a d
def xp : (fixed S (1,1)).apex := ⟨letter,letter,rfl⟩
def bp (a m d : b ⟶ b) : xp ⟶ xp := ⟨⟨atom a m,atom m d,rfl⟩⟩
def xt : (TripleBoundary.L (power S 1) (power S 1) (power S 1)).apex := ⟨xp,letter,rfl⟩
def bt (a m d e : b ⟶ b) : xt ⟶ xt := ⟨⟨bp a m d,atom d e,rfl⟩⟩
def x : TripleTrace.input S Y 1 1 1 := pair Y _ xt b
def f (a : b ⟶ b) : x ⟶ x := arrow (bt a no yes no) (𝟙 b)
abbrev J := TaggedTripleCover.incl S Y 1 1 1
abbrev e (a : b ⟶ b) := J.map (f a)
theorem observe {C : Type*} [Category* C] {F G : C ⥤ B} (h : F = G) {x y : C} (f : x ⟶ y) :
    (F.map f : Bool → Bool) = (G.map f : Bool → Bool) := by subst G; rfl
theorem seen (a : b ⟶ b) : ((outerBase S Y).map (e a) : Bool → Bool) = a :=
  observe (Lift.over (TaggedTripleCover.spanTag S 1 1 1) Y) (f a)
theorem retained {F : input S Y ⥤ Total (three S Y) (𝟭 B)} (h : F ⋙ gradeProjection = outerBase S Y) (a : b ⟶ b) :
    (gradeProjection.map (F.map (e a)) : Bool → Bool) = a := (observe h (e a)).trans (seen a)
example := retained (firstBase S Y _ (ProjectedCharts.leftOver S (WholeEvaluator.one S Y)))
example := retained (firstBase S Y _ (ProjectedCharts.rightOver S (WholeEvaluator.one S Y)))
example := retained (lastBase S Y _ (ProjectedCharts.leftOver S Y))
example := retained (lastBase S Y _ (ProjectedCharts.rightOver S Y))
theorem notIso (a : b ⟶ b) (h : a false = a true) : ¬ IsIso a := by
  intro ha; have k := IsIso.hom_inv_id a
  have p := congrFun k false; have q := congrFun k true
  change (inv a) (a false) = false at p
  change (inv a) (a true) = true at q
  rw [h,q] at p; cases p
example : ¬ IsIso no ∧ ¬ IsIso yes := ⟨notIso no rfl,notIso yes rfl⟩
example : no ≠ yes := fun h => Bool.noConfusion (congrFun h false)
def flip : b ⟶ b := Bool.not
def spin (a : b ⟶ b) : x ⟶ x := arrow (bt a (𝟙 b) (𝟙 b) (𝟙 b)) (𝟙 b)
theorem spinComp (a a' : b ⟶ b) : spin a ≫ spin a' = spin (a ≫ a') := rfl
theorem spinId : spin (𝟙 b) = 𝟙 x := rfl
def turn : x ≅ x where
  hom := spin flip
  inv := spin flip
  hom_inv_id := by rw [spinComp,show flip ≫ flip = 𝟙 b by funext z; cases z <;> rfl,spinId]
  inv_hom_id := by rw [spinComp,show flip ≫ flip = 𝟙 b by funext z; cases z <;> rfl,spinId]
noncomputable abbrev F := lastRight S Y
noncomputable abbrev xg := J.obj x
noncomputable def twist := F.mapIso (J.mapIso turn)
theorem twistSeen : (gradeProjection.map twist.hom : Bool → Bool) = flip :=
  (observe (lastBase S Y _ (ProjectedCharts.rightOver S Y)) (J.map (spin flip))).trans
    (observe (Lift.over (TaggedTripleCover.spanTag S 1 1 1) Y) (spin flip))
theorem twistDiff : twist.hom ≠ 𝟙 _ := by
  intro h
  have e := congrArg gradeProjection.map h
  rw [Functor.map_id] at e
  have d : flip = id := twistSeen.symm.trans e
  exact Bool.noConfusion (congrFun d false)
noncomputable def wrong := (JoinedTarget.comparison S Y).app xg ≪≫ twist
theorem altered : wrong.hom ≠ (JoinedTarget.comparison S Y).hom.app xg := by
  intro j
  apply twistDiff
  apply (cancel_epi ((JoinedTarget.comparison S Y).hom.app xg)).mp
  simpa [wrong] using j
example : (firstRight S Y).map (e no) ≫ (JoinedTarget.comparison S Y).hom.app xg =
    (JoinedTarget.comparison S Y).hom.app xg ≫ (lastRight S Y).map (e no) :=
  (JoinedTarget.comparison S Y).hom.naturality (e no)
example : (firstRight S Y).map (e yes) ≫ (JoinedTarget.comparison S Y).hom.app xg =
    (JoinedTarget.comparison S Y).hom.app xg ≫ (lastRight S Y).map (e yes) :=
  (JoinedTarget.comparison S Y).hom.naturality (e yes)
theorem failsNativeTest : wrong.hom ≫ (JoinedChartFrames.joinLast S Y 1 1 1).hom.app x ≠
    (JoinedChartFrames.joinFirst S Y 1 1 1).hom.app x ≫ (TaggedFixedSquare.ft S Y 1 1 1).app x := by
  intro h
  apply altered
  apply (cancel_mono ((JoinedChartFrames.joinLast S Y 1 1 1).hom.app x)).mp
  exact h.trans (NatTrans.congr_app (JoinedChartFrames.targetTest S Y 1 1 1) x).symm
end MovingTripleProbe
