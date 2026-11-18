module
public import ContextualComposition.MixedMates
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
/-! Identity and composition of the existing single-span evaluation comparison
in the ordinary payload direction. Its inverse-equivalence operand is a mate,
not an equality transport. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.PayloadLaws
open CategoryTheory CategoryTheory.Functor Opposite CoproductSpan SumChange FibreValue
open ForwardMixed (IsTransport)
universe i k j b w v u
/-- The weighted total category varies strictly functorially in the presheaf
at a fixed endpoint functor. Morphisms act on payloads, not on grades. -/
def weightedAction {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K] (e : K ⥤ B) :
    (Bᵒᵖ ⥤ Cat.{v,u}) ⥤ Cat where
  obj Y := Cat.of (Total Y e)
  map T := (ChainPayload.fibreMap T e).toCatHom
  map_id _ := congrArg Functor.toCatHom (ChainPayload.fibreMap_id e)
  map_comp T U := congrArg Functor.toCatHom (ChainPayload.fibreMap_comp T U e)
section Sum
variable {I : Type i} {C D E : I → Type*} [∀ n, Category* (C n)] [∀ n, Category* (D n)] [∀ n, Category* (E n)]
theorem sumId : ZeroPower.Sum.map (fun n => 𝟭 (C n)) = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]; exact (Category.comp_id _).symm
theorem sumComp (F : ∀ n, C n ⥤ D n) (G : ∀ n, D n ⥤ E n) :
    ZeroPower.Sum.map (fun n => F n ⋙ G n) = ZeroPower.Sum.map F ⋙ ZeroPower.Sum.map G := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]; exact (Category.comp_id _).symm
end Sum
section Transport
variable {C D : Type*} [Category* C] [Category* D]
theorem uniq {x y : C} {f g : x ⟶ y} (hf : IsTransport f) (hg : IsTransport g) : f = g := by
  obtain ⟨e,rfl⟩ := hf; obtain ⟨j,rfl⟩ := hg; rfl
theorem unit {U : C ⥤ C} {V : D ⥤ D} {F : C ⥤ D} (s : U ⋙ F ≅ F ⋙ V) (e : U = 𝟭 _) (d : V = 𝟭 _)
    (h : ∀ x, IsTransport (s.hom.app x)) : Paste.UnitLaw s (eqToHom e) (eqToHom d) := fun x =>
  uniq ((h x).comp (ForwardMixed.IsTransport.app d _)) ((ForwardMixed.IsTransport.app e x).map F)
variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category* A₁] [Category* A₂] [Category* A₃]
  [Category* B₁] [Category* B₂] [Category* B₃]
theorem comp {U : A₂ ⥤ A₁} {V : A₃ ⥤ A₂} {W : A₃ ⥤ A₁} {U' : B₂ ⥤ B₁} {V' : B₃ ⥤ B₂} {W' : B₃ ⥤ B₁}
    {F : A₁ ⥤ B₁} {G : A₂ ⥤ B₂} {H : A₃ ⥤ B₃}
    (s : W ⋙ F ≅ H ⋙ W') (i : U ⋙ F ≅ G ⋙ U') (j : V ⋙ G ≅ H ⋙ V')
    (e : W = V ⋙ U) (d : W' = V' ⋙ U')
    (hs : ∀ x, IsTransport (s.hom.app x)) (hi : ∀ x, IsTransport (i.hom.app x)) (hj : ∀ x, IsTransport (j.hom.app x)) :
    Paste.CompLaw s i j (eqToHom e) (eqToHom d) := fun x =>
  uniq ((hs x).comp (ForwardMixed.IsTransport.app d _))
    (((ForwardMixed.IsTransport.app e x).map F).comp ((hi _).comp ((hj x).map U')))
end Transport
open Bicategory
/-- Consume ordinary componentwise unit/composition diagrams without
suppressing the identities, compositors or structural arrows of Cat. -/
def ofDiagrams {I : Type i} [Category.{k} I] (F G : I ⥤ Cat.{v,u}) (E : ∀ a, F.obj a ⥤ G.obj a)
    (c : ∀ {a b} (f : a ⟶ b), (F.map f).toFunctor ⋙ E b ≅ E a ⋙ (G.map f).toFunctor)
    (one : ∀ a, Paste.UnitLaw (c (𝟙 a)) (eqToHom (congrArg Cat.Hom.toFunctor (F.map_id a)))
        (eqToHom (congrArg Cat.Hom.toFunctor (G.map_id a))))
    (two : ∀ {a b d} (f : a ⟶ b) (g : b ⟶ d), Paste.CompLaw (c (f ≫ g)) (c g) (c f)
        (eqToHom (congrArg Cat.Hom.toFunctor (F.map_comp f g)))
        (eqToHom (congrArg Cat.Hom.toFunctor (G.map_comp f g)))) :
    Pseudofunctor.StrongTrans F.toPseudofunctor' G.toPseudofunctor' where
  app a := (E a.as).toCatHom
  naturality f := Cat.Hom.isoMk (c f.as)
  naturality_naturality {a b f g} h := by
    obtain rfl := LocallyDiscrete.eq_of_hom h
    obtain rfl := Subsingleton.elim h (𝟙 f)
    rw [PrelaxFunctor.map₂_id,PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change (E b.as).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    exact ((congrArg (· ≫ (c f.as).hom.app x) ((E b.as).map_id _)).trans (Category.id_comp _)).trans (Category.comp_id _).symm
  naturality_id a := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change (c _).hom.app x ≫ (eqToHom (G.map_id a.as)).toNatTrans.app _ =
      (E a.as).map ((eqToHom (F.map_id a.as)).toNatTrans.app x) ≫ 𝟙 _ ≫ 𝟙 _
    rw [Cat.Hom₂.eqToHom_toNatTrans,Cat.Hom₂.eqToHom_toNatTrans,Category.id_comp,Category.comp_id]
    exact one a.as x
  naturality_comp {a b d} f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change (c _).hom.app x ≫ (eqToHom (G.map_comp f.as g.as)).toNatTrans.app _ =
      (E d.as).map ((eqToHom (F.map_comp f.as g.as)).toNatTrans.app x) ≫
      𝟙 _ ≫ (c g.as).hom.app _ ≫ 𝟙 _ ≫ (G.map g.as).toFunctor.map ((c f.as).hom.app x) ≫ 𝟙 _
    rw [Cat.Hom₂.eqToHom_toNatTrans,Cat.Hom₂.eqToHom_toNatTrans,Category.id_comp,Category.id_comp,Category.comp_id]
    exact two f.as g.as x
namespace All
open CoproductSpan.All
variable {B : Type b} [Category.{w} B] {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (A : B)
variable {Y Z W : Bᵒᵖ ⥤ Cat.{w,b}} (T : Y ⟶ Z) (U : Z ⟶ W)
abbrev whole := ChainPayload.fibreMap T (wholeLeg (src R) (dst R) A)
abbrev leaves := ZeroPower.Sum.map (leaf R T A)
abbrev iterates := ZeroPower.Sum.map (SumChange.target R T A)
theorem leafId : leaves R A (𝟙 Y) = 𝟭 _ :=
  (congrArg ZeroPower.Sum.map (funext (fun n => ChainPayload.fibreMap_id (Y := Y) (leg (src R) (dst R) A n)))).trans sumId
theorem leafComp : leaves R A (T ≫ U) = leaves R A T ⋙ leaves R A U :=
  (congrArg ZeroPower.Sum.map (funext (fun n => ChainPayload.fibreMap_comp T U (leg (src R) (dst R) A n)))).trans (sumComp _ _)
theorem iterateId : iterates R A (𝟙 Y) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (NatTrans.congr_app (ChainPayload.allIterate_id (Y := Y) R) (op A))
theorem iterateComp : iterates R A (T ≫ U) = iterates R A T ⋙ iterates R A U :=
  congrArg Cat.Hom.toFunctor (NatTrans.congr_app (ChainPayload.allIterate_comp T R U) (op A))
noncomputable abbrev forward := eqToIso (compare_payload (src R) (dst R) A Y T)
theorem forwardTransport (x) : IsTransport ((forward R A T).inv.app x) :=
  ForwardMixed.IsTransport.app (compare_payload (src R) (dst R) A Y T).symm x
theorem taggedTransport (x) : IsTransport ((taggedPayload R T A).inv.app x) := by
  rcases x with ⟨n,x⟩
  exact (ForwardMixed.IsTransport.app (componentPayload R T A n).symm x).map (Sigma.incl n)
/-- Strict payload functors at a fixed base object, before and after the
tagged presentation. These do not strictify the chosen inverse comparison. -/
abbrev wholeAction : (Bᵒᵖ ⥤ Cat.{w,b}) ⥤ Cat := weightedAction (wholeLeg (src R) (dst R) A)
def leafAction : (Bᵒᵖ ⥤ Cat.{w,b}) ⥤ Cat where
  obj Y := Cat.of (Σ n, Total Y (leg (src R) (dst R) A n))
  map T := (leaves R A T).toCatHom
  map_id _ := congrArg Functor.toCatHom (leafId R A)
  map_comp T U := congrArg Functor.toCatHom (leafComp R A T U)
def iterateAction : (Bᵒᵖ ⥤ Cat.{w,b}) ⥤ Cat where
  obj Y := Cat.of (Iterates.Packed Q R Y (op A))
  map T := (iterates R A T).toCatHom
  map_id _ := congrArg Functor.toCatHom (iterateId R A)
  map_comp T U := congrArg Functor.toCatHom (iterateComp R A T U)
theorem wholeId : whole R A (𝟙 Y) = 𝟭 _ := ChainPayload.fibreMap_id _
theorem wholeComp : whole R A (T ≫ U) = whole R A T ⋙ whole R A U := ChainPayload.fibreMap_comp T U _
theorem forwardUnit : Paste.UnitLaw (forward R A (𝟙 Y)).symm (eqToHom (leafId R A)) (eqToHom (wholeId R A)) :=
  unit _ _ _ (forwardTransport R A _)
theorem forwardComp : Paste.CompLaw (forward R A (T ≫ U)).symm (forward R A U).symm (forward R A T).symm
    (eqToHom (leafComp R A T U)) (eqToHom (wholeComp R A T U)) :=
  comp _ _ _ _ _ (forwardTransport R A _) (forwardTransport R A _) (forwardTransport R A _)
theorem taggedUnit : Paste.UnitLaw (taggedPayload R (𝟙 Y) A).symm (eqToHom (leafId R A)) (eqToHom (iterateId R A)) :=
  unit _ _ _ (taggedTransport R A _)
theorem taggedComp : Paste.CompLaw (taggedPayload R (T ≫ U) A).symm (taggedPayload R U A).symm (taggedPayload R T A).symm
    (eqToHom (leafComp R A T U)) (eqToHom (iterateComp R A T U)) :=
  comp _ _ _ _ _ (taggedTransport R A _) (taggedTransport R A _) (taggedTransport R A _)
noncomputable abbrev presentation (Y : Bᵒᵖ ⥤ Cat.{w,b}) := (compare (src R) (dst R) A Y).asEquivalence
theorem inverseUnit : Paste.UnitLaw (inversePayload R (𝟙 Y) A).symm (eqToHom (wholeId R A)) (eqToHom (leafId R A)) :=
  MateLaws.unit (presentation R A Y) (forward R A (𝟙 Y)) _ _ (forwardUnit R A)
theorem inverseComp : Paste.CompLaw (inversePayload R (T ≫ U) A).symm (inversePayload R U A).symm (inversePayload R T A).symm
    (eqToHom (wholeComp R A T U)) (eqToHom (leafComp R A T U)) :=
  MateLaws.comp (presentation R A W) (presentation R A Z) (presentation R A Y)
    (forward R A (T ≫ U)) (forward R A U) (forward R A T) _ _ (forwardComp R A T U)
theorem evaluationUnit : Paste.UnitLaw (evaluationPayload R (𝟙 Y) A).symm (eqToHom (wholeId R A)) (eqToHom (iterateId R A)) :=
  Paste.unitLaw (inversePayload R (𝟙 Y) A).symm (taggedPayload R (𝟙 Y) A).symm _ _ _ (inverseUnit R A) (taggedUnit R A)
theorem evaluationComp : Paste.CompLaw (evaluationPayload R (T ≫ U) A).symm (evaluationPayload R U A).symm (evaluationPayload R T A).symm
    (eqToHom (wholeComp R A T U)) (eqToHom (iterateComp R A T U)) :=
  Paste.compLaw (inversePayload R (T ≫ U) A).symm (inversePayload R U A).symm (inversePayload R T A).symm
    (taggedPayload R (T ≫ U) A).symm (taggedPayload R U A).symm (taggedPayload R T A).symm
    _ _ _ (inverseComp R A T U) (taggedComp R A T U)
/-- The underlying actions preserve identity by functor equality; the
comparison being tested is still the actual evaluationPayload isomorphism. -/
theorem evaluationUnitDiagram :
    (evaluationPayload R (𝟙 Y) A).inv ≫ whiskerLeft (evaluation R Y A).functor (eqToHom (iterateId R A)) =
      whiskerRight (eqToHom (wholeId R A)) (evaluation R Y A).functor :=
  (Paste.unitDiagram_iff _ _ _).mp (evaluationUnit R A)
/-- Payloads change covariantly: apply T first, then U. The inverse
orientation here is the payload face used in the final mixed diagram. -/
theorem evaluationCompDiagram :
    (evaluationPayload R (T ≫ U) A).inv ≫ whiskerLeft (evaluation R Y A).functor (eqToHom (iterateComp R A T U)) =
      whiskerRight (eqToHom (wholeComp R A T U)) (evaluation R W A).functor ≫
      whiskerLeft (whole R A T) (evaluationPayload R U A).inv ≫
      whiskerRight (evaluationPayload R T A).inv (iterates R A U) :=
  (Paste.compDiagram_iff _ _ _ _ _).mp (evaluationComp R A T U)
/-- Fixed-base pseudonaturality for ordinary payload transformations. -/
noncomputable def strong : Pseudofunctor.StrongTrans
    (wholeAction R A).toPseudofunctor' (iterateAction R A).toPseudofunctor' :=
  ofDiagrams (wholeAction R A) (iterateAction R A) (fun Y => (evaluation R Y A).functor)
    (fun T => (evaluationPayload R T A).symm) (fun _ => evaluationUnit R A) (fun T U => evaluationComp R A T U)
theorem strongComponent (Y : Bᵒᵖ ⥤ Cat.{w,b}) : ((strong R A).app ⟨Y⟩).toFunctor.IsEquivalence :=
  (evaluation R Y A).isEquivalence_functor
theorem strongCell : Cat.Hom.toNatIso ((strong R A).naturality ⟨T⟩) = (evaluationPayload R T A).symm := rfl
end All
end ContextualComposition.GrothendieckStep.PayloadLaws
