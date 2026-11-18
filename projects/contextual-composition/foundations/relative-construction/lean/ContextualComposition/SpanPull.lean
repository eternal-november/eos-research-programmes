module
public import ContextualComposition.SumChange
@[expose] public section
namespace ContextualComposition.GrothendieckStep.SpanPull
open CategoryTheory CategoryTheory.Functor Opposite CoproductSpan NativeCleavage
universe i k j b w u v
variable {I : Type i} {B : Type b} [Category.{w} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (C : ∀ t, Cleavage (p t)) (Y : Bᵒᵖ ⥤ Cat.{v,u})
theorem tagCartesian {t : I} {x y : K t} (f : x ⟶ y) (hf : Cartesian (p t) f) :
    Cartesian (Sigma.desc p) ((Sigma.incl t).map f) := by
  rintro ⟨s,z⟩ g a ha
  change Sigma.SigmaHom (C := K) ⟨s,z⟩ ⟨t,y⟩ at g
  cases g with | mk g =>
    obtain ⟨l,hl,ul⟩ := hf _ g a ha
    refine ⟨Sigma.SigmaHom.mk l,⟨hl.1,congrArg Sigma.SigmaHom.mk hl.2⟩,?_⟩
    rintro ⟨m⟩ hm
    exact congrArg Sigma.SigmaHom.mk (ul m ⟨hm.1,(Sigma.incl t).map_injective hm.2⟩)
def choice : Cleavage (Sigma.desc p) := fun A ⟨t,y⟩ a =>
  let L := C t A y a
  ⟨⟨t,L.obj⟩,L.source,Sigma.SigmaHom.mk L.lift,L.over,tagCartesian p _ L.cart⟩
def weightedChoice := extendChoice Y (Sigma.desc d) (Sigma.desc p) (choice p C)
def partChoice (t : I) := extendChoice Y (d t) (p t) (C t)
abbrev totalTag (t : I) := Distribute.tag Y d t
abbrev proj := FibreTotal.projection Y (Sigma.desc d) (Sigma.desc p)
abbrev partProj (t : I) := FibreTotal.projection Y (d t) (p t)
def strictTag (A : B) (t : I) := SpanPayload.fibreFunctor (totalTag d Y t) (proj p d Y) rfl A
theorem lift_tag {A D : B} (a : A ⟶ D) (t : I) (x : (partProj p d Y t).Fiber D) :
    (totalTag d Y t).map (Reindex.lift (partChoice p d C Y t) a x) =
      Reindex.lift (weightedChoice p d C Y) a ((strictTag p d Y D t).obj x) := rfl
theorem map_tag {A D : B} (a : A ⟶ D) (t : I) {x y : (partProj p d Y t).Fiber D} (f : x ⟶ y) :
    (strictTag p d Y A t).map (Reindex.map (partChoice p d C Y t) a f) =
      Reindex.map (weightedChoice p d C Y) a ((strictTag p d Y D t).map f) := by
  refine Reindex.cancel (weightedChoice p d C Y) a (z := (strictTag p d Y D t).obj y) _ _ ?_
  refine Eq.trans ?_ (Reindex.map_fac (weightedChoice p d C Y) a ((strictTag p d Y D t).map f)).symm
  exact ((totalTag d Y t).map_comp _ _).symm.trans ((congrArg ((totalTag d Y t).map) (Reindex.map_fac (partChoice p d C Y t) a f)).trans ((totalTag d Y t).map_comp _ _))
theorem strictSquare {A D : B} (a : A ⟶ D) (t : I) :
    Reindex.functor (partChoice p d C Y t) a ⋙ strictTag p d Y A t =
      strictTag p d Y D t ⋙ Reindex.functor (weightedChoice p d C Y) a := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    exact (map_tag p d C Y a t f).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm)
noncomputable def wholePull {A D : B} (a : A ⟶ D) :
    Total Y (wholeLeg p d D) ⥤ Total Y (wholeLeg p d A) :=
  FibreTotal.into Y _ _ D ⋙ Reindex.functor (weightedChoice p d C Y) a ⋙ FibreTotal.out Y _ _ A
noncomputable def componentPull {A D : B} (a : A ⟶ D) (t : I) :
    Total Y (leg p d D t) ⥤ Total Y (leg p d A t) :=
  FibreTotal.into Y _ _ D ⋙ Reindex.functor (partChoice p d C Y t) a ⋙ FibreTotal.out Y _ _ A
def presentedTag (A : B) (t : I) : Total Y (leg p d A t) ⥤ Total Y (wholeLeg p d A) :=
  FibreTotal.into Y _ _ A ⋙ strictTag p d Y A t ⋙ FibreTotal.out Y _ _ A
theorem presentedSquare {A D : B} (a : A ⟶ D) (t : I) :
    componentPull p d C Y a t ⋙ presentedTag p d Y A t = presentedTag p d Y D t ⋙ wholePull p d C Y a :=
  congrArg (fun F => FibreTotal.into Y (d t) (p t) D ⋙ F ⋙ FibreTotal.out Y (Sigma.desc d) (Sigma.desc p) A)
    (strictSquare p d C Y a t)
theorem compareTag (A : B) (t : I) :
    Sigma.incl t ⋙ compare p d A Y = presentedTag p d Y A t := by
  exact (SpanPayload.total_comp Y (Sigma.incl t) _ rfl (pack p A) _ (over p d A))
noncomputable def forward {A D : B} (a : A ⟶ D) :
    compare p d D Y ⋙ wholePull p d C Y a ≅
      ZeroPower.Sum.map (componentPull p d C Y a) ⋙ compare p d A Y :=
  Sigma.natIso fun t => eqToIso <|
    (congrArg (· ⋙ wholePull p d C Y a) (compareTag p d Y D t)).trans
      ((presentedSquare p d C Y a t).symm.trans
        (congrArg (componentPull p d C Y a t ⋙ ·) (compareTag p d Y A t).symm))

namespace All
open CoproductSpan.All
variable {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (X : Bᵒᵖ ⥤ Cat.{w,b})
def parts : (n : Nat) → Cleavage (src R n)
  | 0 => baseChoice
  | n+1 => powerChoice R n
noncomputable def pull {A D : B} (a : A ⟶ D) := wholePull (src R) (dst R) (parts R) X a
theorem pull_eq_leaf {A D : B} (a : A ⟶ D) :
    componentPull (src R) (dst R) (parts R) X a = SumChange.leafPull R X a := by
  funext n; cases n <;> rfl
noncomputable def comparison {A D : B} (a : A ⟶ D) :
    compare (src R) (dst R) D X ⋙ pull R X a ≅
      ZeroPower.Sum.map (SumChange.leafPull R X a) ⋙ compare (src R) (dst R) A X :=
  forward (src R) (dst R) (parts R) X a ≪≫
    eqToIso (congrArg (fun F => ZeroPower.Sum.map F ⋙ compare (src R) (dst R) A X) (pull_eq_leaf R X a))
noncomputable def evaluationBase {A D : B} (a : A ⟶ D) :
    pull R X a ⋙ (evaluation R X A).functor ≅ (evaluation R X D).functor ⋙ Iterates.packedMap Q R X a.op :=
  (SpanPayload.pasteIso
    (SumChange.inverseSquare (compare (src R) (dst R) D X).asEquivalence
      (compare (src R) (dst R) A X).asEquivalence (comparison R X a))
    (SumChange.taggedBase R X a).symm).symm
end All
end ContextualComposition.GrothendieckStep.SpanPull
