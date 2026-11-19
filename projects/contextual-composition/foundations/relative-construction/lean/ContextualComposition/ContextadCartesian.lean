module
public import ContextualComposition.ContextadTensorLift
public import ContextualComposition.BlockEvaluation
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadCartesian
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage ContextadUnit
universe b w u v
set_option backward.isDefEq.respectTransparency false
variable {B K L E : Type*} [Category* B] [Category* K] [Category* L] [Category* E]
variable (Y : Bᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ B) (d : L ⥤ B)
theorem verticalPayload {i : K} {x y : Y.obj (op (e.obj i))} (f : x ⟶ y) :
    HEq (payloadMap ((atGrade Y e i).map f)) f := by
  change HEq ((eqToHom _ ≫ f.op).unop) _
  rw [unop_comp]
  have aux {a c z : Y.obj (op (e.obj i))} (g : a ⟶ c) (h : op z = op c) :
      HEq (g ≫ (eqToHom h).unop) g := by cases unop_injective h; simp
  exact aux _ _
theorem vertical_cart {p : K ⥤ E} {x y : K} (f : x ⟶ y) [IsIso f] : Cartesian p f :=
  Change.ofStrong _ (inferInstance : p.IsStronglyCartesian (p.map f) f)
theorem factorTotal {x y : Total Y e} (f : x ⟶ y) :
    (atGrade Y e (grade _ _ x)).map (payloadMap f) ≫ pullLift Y e y (gradeMap f) = f := by
  apply (homEquiv _ _).injective
  refine Sigma.ext (Category.id_comp _) ?_
  exact (payload_post Y e y _ _).trans (verticalPayload Y e (payloadMap f))
theorem cart_of_payload {x y : Total Y e} (f : x ⟶ y) [IsIso (payloadMap f)] :
    Cartesian gradeProjection f := by
  rw [← factorTotal Y e f]
  exact pasteCart (vertical_cart _) (cartesianLift Y e y _)
variable (k : K ⥤ L) (δ : k ⋙ d ⟶ e)
theorem restrictLift {z : Total Y e} {x : K} (a : x ⟶ grade _ _ z) :
    Cartesian gradeProjection ((restrict Y e d k δ).map (pullLift Y e z a)) := by
  have : IsIso (payloadMap ((restrict Y e d k δ).map (pullLift Y e z a))) := by
    rw [restrict_payload]
    change IsIso ((Y.map _).toFunctor.map (𝟙 _) ≫ eqToHom _)
    infer_instance
  exact cart_of_payload _ _ _
variable {p : K ⥤ E} {q : L ⥤ E} (over : k ⋙ q = p)
abbrev weighted := restrict Y e d k δ
include over in
theorem weightedOver : weighted Y e d k δ ⋙ (gradeProjection ⋙ q) = gradeProjection ⋙ p :=
  congrArg (gradeProjection (Y := Y) (e := e) ⋙ ·) over
theorem weightedLift {z : Total Y e} {x : K} (a : x ⟶ grade _ _ z) (h : Cartesian q (k.map a)) :
    Cartesian (gradeProjection ⋙ q) ((weighted Y e d k δ).map (pullLift Y e z a)) :=
  composite (restrictLift Y e d k δ a) h
theorem presOfChoice {C D X : Type*} [Category* C] [Category* D] [Category* X]
    (F : C ⥤ D) (p : C ⥤ X) (q : D ⥤ X) (c : Cleavage p)
    (hc : ∀ (A : X) (y : C) (a : A ⟶ p.obj y), Cartesian q (F.map (c A y a).lift))
    {x y : C} (f : x ⟶ y) (h : Cartesian p f) : Cartesian q (F.map f) := by
  let z := c (p.obj x) y (p.map f)
  have : p.IsStronglyCartesian (p.map f) f := strong h
  have : p.IsStronglyCartesian (p.map f) z.lift := chosenStrong z
  let i := IsCartesian.domainUniqueUpToIso p (p.map f) z.lift f
  have k : i.hom ≫ z.lift = f := IsCartesian.fac p (p.map f) z.lift f
  rw [← k,F.map_comp]
  exact pasteCart (vertical_cart _) (hc _ _ _)
theorem weightedCartesian {p : K ⥤ B} {q : L ⥤ B} (c : Cleavage p)
    (h : ∀ {x y : K} (a : x ⟶ y), Cartesian p a → Cartesian q (k.map a))
    {x y : Total Y e} (f : x ⟶ y) (hf : Cartesian (gradeProjection ⋙ p) f) :
    Cartesian (gradeProjection ⋙ q) ((weighted Y e d k δ).map f) :=
  presOfChoice _ _ _ (extendChoice Y e p c)
    (fun _ z a => weightedLift Y e d k δ (c _ (grade _ _ z) a).lift (h _ (c _ _ a).cart)) f hf
end ContextualComposition.GrothendieckStep.ContextadCartesian
