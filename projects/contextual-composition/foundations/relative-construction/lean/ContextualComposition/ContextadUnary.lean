module
public import ContextualComposition.ContextadVertical
public import ContextualComposition.NativeTrace
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadUnary
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage SpanApex NativeBlocks BlockEvaluation TelescopeSquares WordTrace
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
theorem totalHEq {B K : Type*} [Category* B] [Category* K] {Y : Bᵒᵖ ⥤ Cat.{v,u}} {e : K ⥤ B}
    {x y x' y' : Total Y e} (l : x = x') (r : y = y') (f : x ⟶ y) (g : x' ⟶ y')
    (k : HEq (gradeMap f) (gradeMap g)) (p : HEq (payloadMap f) (payloadMap g)) : HEq f g := by
  subst x'; subst y'; exact heq_of_eq ((homEquiv _ _).injective (Sigma.ext (eq_of_heq k) p))
theorem castHEq {C : Type*} [Category* C] {x a b : C} (h : a=b) (f : x ⟶ a) :
    HEq (Equiv.cast (congrArg (fun d => x ⟶ d) h) f) f := by subst b; rfl
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (A : B) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev L := PackedFree.pow S Y 1
abbrev atomHead {x y : P.grades.obj (op A)} (g : x ⟶ y) := payloadMap ((ContextadChart.one (P := P) A).map g)
include S in
theorem leg {x y : P.grades.obj (op A)} (g : x ⟶ y) :
    next (𝟙 A) (atomHead A g) = (P.extend A).map g :=
  eq_of_heq (Edge.hom_heq (congrArg (fun W => Edge.map W ⟨x,y,g⟩) (ContextadChart.oneEnd S A)))
variable (z : Edge (Total Y (P.extend A)))
abbrev adjusted := (payloadMap z.hom) ≫ eqToHom (congrArg (fun a : (P.extend A).obj (grade _ _ z.src) ⟶ (P.extend A).obj (grade _ _ z.dst) => (Y.map a.op).toFunctor.obj (payload _ _ z.dst)) (leg S A (gradeMap z.hom)).symm)
abbrev explicit := cell (L S Y) (𝟙 A) z.src z.dst
    (squareEquiv Y S (𝟙 A) (.cons (grade _ _ z.src) (.nil _)) (.cons (grade _ _ z.dst) (.nil _))
      (payload _ _ z.src) (payload _ _ z.dst) ⟨⟨atomHead A (gradeMap z.hom),PUnit.unit⟩,adjusted S A Y z⟩)
theorem explicit_incl : explicit S A Y z = Edge.map (FibreValue.incl (L S Y) A) z := by
  refine Edge.eq_of (a := explicit S A Y z) (b := Edge.map (FibreValue.incl (L S Y) A) z) rfl rfl ?_
  refine totalHEq rfl rfl _ _ HEq.rfl ?_
  refine HEq.trans ?_ (FibreValue.embed_payload (L S Y) z.hom).symm
  apply totalHEq rfl (Functor.congr_obj (congrArg Cat.Hom.toFunctor ((L S Y).map_id (op A))) z.dst)
  · exact FibreValue.embed_payload P.grades (gradeMap z.hom)
  · refine (castHEq (tailTarget Y S (n := 0) (𝟙 A) (atomHead A (gradeMap z.hom)) (payload _ _ z.dst)) (adjusted S A Y z)).trans ?_
    have t {C : Type u} [Category.{max u v} C] {x b c : C} (f : x ⟶ b) (h : b=c) : HEq (f ≫ eqToHom h) f := by subst c; simp
    exact t _ _
theorem read_incl : read S Y 1 (Edge.map (FibreValue.incl (L S Y) A) z) =
    ([Edge.map (ContextadChart.one (P := P) A) (Edge.map gradeProjection z)], Edge.map (NativeTrace.leaf Y (P.extend A)) z) := by
  rw [← explicit_incl]
  have t := one_atom S Y (𝟙 A) (atomHead A (gradeMap z.hom)) (payload _ _ z.src) (payload _ _ z.dst) (adjusted S A Y z)
  change ([(WordTrace.one S Y (explicit S A Y z)).1], (WordTrace.one S Y (explicit S A Y z)).2) = _
  change WordTrace.one S Y (explicit S A Y z) = _ at t
  rw [t]
  apply Prod.ext
  · rfl
  · refine Edge.eq_of (b := Edge.map (NativeTrace.leaf Y (P.extend A)) z) rfl rfl ?_
    refine totalHEq rfl rfl _ _ (heq_of_eq (leg S A (gradeMap z.hom))) ?_
    have aux {C : Type u} [Category.{max u v} C] {x b c : C} (f : x ⟶ b) (h : b=c) : HEq (f ≫ eqToHom h) f := by subst c; simp
    exact aux _ _
theorem recognition : ContextadVertical.insertOne (S := S) A Y ⋙ global S Y 1 = FibreValue.incl (L S Y) A := by
  apply Edge.functor_ext
  intro z
  apply read_injective S Y 1
  apply (NativeTrace.read_global S Y 1 (Edge.map (ContextadVertical.insertOne (S := S) A Y) z)).trans
  rw [read_incl]
  apply Prod.ext
  · exact congrArg (fun F => [Edge.map F z]) (SpanPayload.total_projection Y _ _ (ContextadChart.oneEnd S A))
  · exact congrArg (fun F => Edge.map F z) (NativeTrace.leaf_total Y _ _ (ContextadChart.oneEnd S A))
end ContextualComposition.GrothendieckStep.ContextadUnary
