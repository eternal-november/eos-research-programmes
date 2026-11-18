module
public import ContextualComposition.PayloadLift
/-! Payload naturality for the actual positive evaluation functor, from global morphisms to values. The two-base-direction mixed equation is not asserted here. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.EvalPayload
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage TelescopeSquares SpanApex
universe b w k j u v
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K] {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
theorem pairAligned (e : K ⥤ B) {p q : K} {x x' : Y.obj (op (e.obj p))}
    {y y' : Y.obj (op (e.obj q))} (hx : x = x') (hy : y = y')
    {f : pair Y e p x ⟶ pair Y e q y} {g : pair Y e p x' ⟶ pair Y e q y'}
    (hg : gradeMap f = gradeMap g) (hp : Aligned (payloadMap f) (payloadMap g)) : Aligned f g := by
  subst x'; subst y'
  have aux {k j : p ⟶ q} (h : k = j)
      {m : x ⟶ (Y.map (e.map k).op).toFunctor.obj y} {l : x ⟶ (Y.map (e.map j).op).toFunctor.obj y}
      (hm : Aligned m l) : HEq m l := by subst j; exact heq_of_eq hm.eq
  have he := (homEquiv _ _).injective (Sigma.ext hg (aux hg hp))
  rw [he]; exact Aligned.refl _

variable {P : Endpoints.{b,w,u,v} B} (S : P.Split)
theorem rawMap {n : Nat} {x y : Evaluation.W S Y n} (f : x ⟶ y) :
    Evaluation.raw S Z ((ChainPayload.fibreMap T (chainDest S n)).map f) = ChainPayload.onSquare T (Evaluation.raw S Y f) :=
  Sigma.ext rfl (heq_of_eq (PayloadLift.mapPayload T (chainDest S n) f))
theorem alignedMap {n : Nat} {x y : Evaluation.W S Y n} (f : x ⟶ y) :
    Aligned ((Evaluation.functor S Z n).map ((ChainPayload.fibreMap T (chainDest S n)).map f))
      ((ChainPayload.fibreMap (ChainPayload.layerMap T S (n+1)) (𝟭 B)).map ((Evaluation.functor S Y n).map f)) := by
  apply pairAligned (𝟭 B) (ChainPayload.realized T S _ _) (ChainPayload.realized T S _ _) rfl
  change Aligned (squareEquiv Z S _ _ _ _ _ (Evaluation.raw S Z _)) _
  rw [rawMap]
  exact (ChainPayload.compared_square T S _ _ _ _ (Evaluation.raw S Y f)).trans
    (ChainPayload.fibreMap_payload (ChainPayload.layerMap T S (n+1)) (𝟭 B) ((Evaluation.functor S Y n).map f)).symm
theorem conjugate {C : Type*} [Category* C] {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'} (h : Aligned f g)
    (s : x = x') (t : y' = y) : f = eqToHom s ≫ g ≫ eqToHom t := by
  subst x'; subst y'; simpa using h.eq
theorem totalSquare (n : Nat) :
    ChainPayload.fibreMap T (chainDest S n) ⋙ Evaluation.functor S Z n =
      Evaluation.functor S Y n ⋙ ChainPayload.fibreMap (ChainPayload.layerMap T S (n+1)) (𝟭 B) := by
  fapply Functor.ext
  · intro x; exact congrArg (pair _ _ _) (ChainPayload.realized T S _ _)
  · intro x y f; exact conjugate (alignedMap T S f) _ _
theorem pasteEq {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
    (p : A ⥤ B) (q : B ⥤ C) (r : A ⥤ D) (s : B ⥤ E) (t : C ⥤ F) (v : D ⥤ E) (w : E ⥤ F)
    (h : r ⋙ v = p ⋙ s) (k : s ⋙ w = q ⋙ t) : r ⋙ (v ⋙ w) = (p ⋙ q) ⋙ t := by
  rw [← Functor.assoc,h,Functor.assoc,k]; rfl
theorem nativeSquare (n : Nat) :
    ChainPayload.fibreMap T (positivePowers P S n).dest ⋙ Evaluation.nativeFunctor S Z n =
      Evaluation.nativeFunctor S Y n ⋙ ChainPayload.fibreMap (ChainPayload.layerMap T S (n+1)) (𝟭 B) := by
  exact pasteEq (SpanPayload.Power.global S n Y) (Evaluation.functor S Y n) (ChainPayload.fibreMap T _) (ChainPayload.fibreMap T _)
    (ChainPayload.fibreMap (ChainPayload.layerMap T S (n+1)) _) (SpanPayload.Power.global S n Z) (Evaluation.functor S Z n)
    (SpanPayload.Power.global_natural S n Y T).symm (totalSquare T S n)
theorem cancelEmbedding {C D E : Type*} [Category* C] [Category* D] [Category* E] (I : D ⥤ E)
    [I.Faithful] (inj : Function.Injective I.obj) (F G : C ⥤ D) (h : F ⋙ I = G ⋙ I) : F = G := by
  fapply Functor.ext
  · intro x; exact inj (Functor.congr_obj h x)
  · intro x y f
    apply I.map_injective
    simp only [Functor.map_comp,eqToHom_map]
    exact Functor.congr_hom h f
theorem cancelInclusion {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {p : D ⥤ E} {A : E} (F G : C ⥤ p.Fiber A)
    (h : F ⋙ Functor.Fiber.fiberInclusion = G ⋙ Functor.Fiber.fiberInclusion) : F = G :=
  cancelEmbedding (Functor.Fiber.fiberInclusion (p := p) (S := A)) (fun _ _ e => Subtype.ext e) F G h
theorem fibrePaste {B C D E : Type*} [Category* B] [Category* C] [Category* D] [Category* E]
    {p : C ⥤ B} {q : D ⥤ B} {r : E ⥤ B} (A : B) (F : C ⥤ D) (G : D ⥤ E)
    (h : F ⋙ q = p) (k : G ⋙ r = q) :
    (SpanPayload.fibreFunctor F q h A ⋙ SpanPayload.fibreFunctor G r k A) ⋙ Functor.Fiber.fiberInclusion =
      Functor.Fiber.fiberInclusion ⋙ (F ⋙ G) :=
by
  rw [Functor.assoc,SpanPayload.fibre_diagram,← Functor.assoc,SpanPayload.fibre_diagram]; rfl
open SpanPayload.Power
def strictEval (G : Bᵒᵖ ⥤ Cat.{v,u}) (n : Nat) (A : B) :=
  SpanPayload.fibreFunctor (Evaluation.nativeFunctor S G n) gradeProjection (Evaluation.native_over S G n) A
theorem strictSquare (n : Nat) (A : B) :
    PayloadLift.action T (positivePowers P S n).dest (positivePowers P S n).source A ⋙ strictEval S Z n A =
      strictEval S Y n A ⋙ PayloadLift.action (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) A := by
  apply cancelInclusion
  let I := Functor.Fiber.fiberInclusion (p := gradeProjection (Y := Y) (e := (positivePowers P S n).dest) ⋙ (positivePowers P S n).source) (S := A)
  exact (fibrePaste A _ _ (PayloadLift.over T _ _) (Evaluation.native_over S Z n)).trans
    ((congrArg (I ⋙ ·) (nativeSquare T S n)).trans
      (fibrePaste A _ _ (Evaluation.native_over S Y n) (PayloadLift.over (ChainPayload.layerMap T S (n+1)) _ _)).symm)
theorem intoSquare (e p : K ⥤ B) (A : B) :
    ChainPayload.fibreMap T (FibreTotal.endpoint e p A) ⋙ FibreTotal.into Z e p A =
      FibreTotal.into Y e p A ⋙ PayloadLift.action T e p A := by
  apply cancelInclusion
  exact (SpanPayload.total_payload_natural _ _ rfl T).symm
theorem onFibreSquare (n : Nat) (A : B) :
    ChainPayload.fibreMap T (nativeEndpoint S n A) ⋙ Evaluation.onFibre S Z n A =
      Evaluation.onFibre S Y n A ⋙ PayloadLift.action (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) A :=
  pasteEq (FibreTotal.into Y _ _ A) (strictEval S Y n A) (ChainPayload.fibreMap T _) (PayloadLift.action T _ _ A)
    (PayloadLift.action (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) A)
    (FibreTotal.into Z _ _ A) (strictEval S Z n A) (intoSquare T _ _ A) (strictSquare T S n A)
theorem inclMapEq {C : Type*} [Category* C] {F G : C ⥤ Cat.{v,u}} (t : F ⟶ G) (c : C) :
    Grothendieck.ι F c ⋙ Grothendieck.map t = (t.app c).toFunctor ⋙ Grothendieck.ι G c := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    have h := (Grothendieck.ιCompMap t c).hom.naturality f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
    change _ = 𝟙 _ ≫ ((t.app c).toFunctor ⋙ Grothendieck.ι G c).map f ≫ 𝟙 _
    exact (Category.comp_id _).symm.trans (h.trans (congrArg (𝟙 _ ≫ ·) (Category.comp_id _).symm))
open FibreValue
theorem embedSquare (A : B) :
    embed Y A ⋙ PayloadLift.action T (𝟭 B) (𝟭 B) A = (T.app (op A)).toFunctor ⋙ embed Z A := by
  apply cancelInclusion
  exact congrArg Functor.rightOp (inclMapEq (ChainPayload.cell T (𝟭 B)) (op A))
theorem valueSquare (A : B) :
    PayloadLift.action T (𝟭 B) (𝟭 B) A ⋙ value Z A = value Y A ⋙ (T.app (op A)).toFunctor := by
  let H := PayloadLift.action T (𝟭 B) (𝟭 B) A
  let t := (T.app (op A)).toFunctor
  calc
    H ⋙ value Z A = (value Y A ⋙ embed Y A) ⋙ (H ⋙ value Z A) := by rw [value_embed]; rfl
    _ = value Y A ⋙ ((t ⋙ embed Z A) ⋙ value Z A) :=
      congrArg (fun k => value Y A ⋙ k ⋙ value Z A) (embedSquare T A)
    _ = (value Y A ⋙ t) ⋙ (embed Z A ⋙ value Z A) := rfl
    _ = _ := by rw [embed_value]; rfl
theorem evalSquare (n : Nat) (A : B) :
    ChainPayload.fibreMap T (nativeEndpoint S n A) ⋙ eval S Z n A =
      eval S Y n A ⋙ ((ChainPayload.layerMap T S (n+1)).app (op A)).toFunctor :=
  pasteEq (Evaluation.onFibre S Y n A) (value _ A) (ChainPayload.fibreMap T _)
    (PayloadLift.action (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) A) _ (Evaluation.onFibre S Z n A) (value _ A)
    (onFibreSquare T S n A) (valueSquare (ChainPayload.layerMap T S (n+1)) A)
end ContextualComposition.GrothendieckStep.EvalPayload
