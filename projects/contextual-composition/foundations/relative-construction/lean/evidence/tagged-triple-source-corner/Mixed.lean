import ContextualComposition.TripleFaceBase
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
def mixed (a i j d p : b ⟶ b) : x ⟶ x := arrow (bt a i j d) p
example : mixed no no yes no yes ≠ mixed no no yes no no := by
  intro h
  have bad := congrArg (fun g : x ⟶ x => (payloadMap g : Bool → Bool) false) h
  exact Bool.noConfusion bad
example (a i j d p : b ⟶ b) : ((outerBase S Y).map (J.map (mixed a i j d p)) : Bool → Bool) = a :=
  observe (Lift.over (TaggedTripleCover.spanTag S 1 1 1) Y) (mixed a i j d p)
-- Actual source comparison is natural for these arrows, with independently
-- varied matched internal maps and a simultaneous nonidentity payload map.
example (a i j d p : b ⟶ b) := (sourceCorner S Y).hom.naturality (J.map (mixed a i j d p))
example : ¬ IsIso (J.map (mixed no yes no yes yes)) := by
  intro h
  have hi : IsIso ((outerBase S Y).map (J.map (mixed no yes no yes yes))) := inferInstance
  have q : ((outerBase S Y).map (J.map (mixed no yes no yes yes)) : Bool → Bool) = no :=
    observe (Lift.over (TaggedTripleCover.spanTag S 1 1 1) Y) (mixed no yes no yes yes)
  exact notIso no rfl (q ▸ hi)
end MovingTripleProbe
