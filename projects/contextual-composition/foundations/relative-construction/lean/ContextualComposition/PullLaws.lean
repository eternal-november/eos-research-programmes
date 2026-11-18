module
public import ContextualComposition.SpanPull
@[expose] public section
namespace ContextualComposition.GrothendieckStep.PullLaws
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage SpanPull CoproductSpan
universe i k j b w u v
variable {I : Type i} {B : Type b} [Category.{w} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (C : ∀ t, Cleavage (p t)) (Y : Bᵒᵖ ⥤ Cat.{v,u})
theorem unitFac {L : Type*} [Category* L] {q : L ⥤ B} (A : B) (H : Cleavage q) (z : q.Fiber A) :
      ((Route.unitIso H A).hom.app z).val = Reindex.lift H (𝟙 A) z :=
    (Category.comp_id _).symm.trans (Route.compare_fac (Route.ofChoice H (𝟙 A)) (Route.id A) z)
theorem unitTag (A : B) (t : I) (x : (partProj p d Y t).Fiber A) :
    (strictTag p d Y A t).map ((Route.unitIso (partChoice p d C Y t) A).hom.app x) =
    (Route.unitIso (weightedChoice p d C Y) A).hom.app ((strictTag p d Y A t).obj x) := by
  let P := partChoice p d C Y t
  let W := weightedChoice p d C Y
  let T := totalTag d Y t
  exact Subtype.ext ((congrArg T.map (unitFac A P x)).trans (unitFac A W ((strictTag p d Y A t).obj x)).symm)
theorem compTag {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (t : I) (x : (partProj p d Y t).Fiber E) :
    (strictTag p d Y A t).map ((Route.compIso (partChoice p d C Y t) a b).hom.app x) =
    (Route.compIso (weightedChoice p d C Y) a b).hom.app ((strictTag p d Y E t).obj x) := by
  let P := partChoice p d C Y t
  let W := weightedChoice p d C Y
  let T := totalTag d Y t
  let route := Route.comp (Route.ofChoice W a) (Route.ofChoice W b)
  let z := (strictTag p d Y E t).obj x
  refine Route.cancel route (y := z) ?_
  refine Eq.trans ?_ (Route.compare_fac (Route.ofChoice W (a ≫ b)) route z).symm
  let f := ((Route.compIso P a b).hom.app x).val
  let g := Reindex.lift P a (Reindex.object P b x)
  let h := Reindex.lift P b x
  change T.map f ≫ T.map g ≫ T.map h = T.map (Reindex.lift P (a ≫ b) x)
  exact (congrArg (T.map f ≫ ·) (T.map_comp g h).symm).trans
    ((T.map_comp f (g ≫ h)).symm.trans (congrArg T.map (Route.compare_fac (Route.ofChoice P (a ≫ b))
      (Route.comp (Route.ofChoice P a) (Route.ofChoice P b)) x)))
noncomputable def wholeUnit (A : B) : wholePull p d C Y (𝟙 A) ≅ 𝟭 _ :=
  isoWhiskerLeft (FibreTotal.into Y _ _ A) (isoWhiskerRight (Route.unitIso (weightedChoice p d C Y) A) (FibreTotal.out Y _ _ A))
noncomputable def partUnit (A : B) (t : I) : componentPull p d C Y (𝟙 A) t ≅ 𝟭 _ :=
  isoWhiskerLeft (FibreTotal.into Y _ _ A) (isoWhiskerRight (Route.unitIso (partChoice p d C Y t) A) (FibreTotal.out Y _ _ A))
noncomputable def wholeComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    wholePull p d C Y (a ≫ b) ≅ wholePull p d C Y b ⋙ wholePull p d C Y a :=
  isoWhiskerLeft (FibreTotal.into Y _ _ E) (isoWhiskerRight (Route.compIso (weightedChoice p d C Y) a b) (FibreTotal.out Y _ _ A))
noncomputable def partComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (t : I) :
    componentPull p d C Y (a ≫ b) t ≅ componentPull p d C Y b t ⋙ componentPull p d C Y a t :=
  isoWhiskerLeft (FibreTotal.into Y _ _ E) (isoWhiskerRight (Route.compIso (partChoice p d C Y t) a b) (FibreTotal.out Y _ _ A))
theorem presentedUnit (A : B) (t : I) (x : Total Y (leg p d A t)) :
    (presentedTag p d Y A t).map ((partUnit p d C Y A t).hom.app x) =
      (wholeUnit p d C Y A).hom.app ((presentedTag p d Y A t).obj x) :=
  congrArg (FibreTotal.out Y (Sigma.desc d) (Sigma.desc p) A).map (unitTag p d C Y A t ((FibreTotal.into Y _ _ A).obj x))
theorem presentedComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (t : I) (x : Total Y (leg p d E t)) :
    (presentedTag p d Y A t).map ((partComp p d C Y a b t).hom.app x) =
      (wholeComp p d C Y a b).hom.app ((presentedTag p d Y E t).obj x) :=
  congrArg (FibreTotal.out Y (Sigma.desc d) (Sigma.desc p) A).map (compTag p d C Y a b t ((FibreTotal.into Y _ _ E).obj x))
namespace Transport
variable {A B : Type*} [Category* A] [Category* B]
theorem unit {F G : A ⥤ B} (h : F = G) {X : A ⥤ A} {Y : B ⥤ B}
    (s : X ⋙ G = G ⋙ Y) (u : X ⟶ 𝟭 _) (v : Y ⟶ 𝟭 _)
    (law : ∀ x, eqToHom (Functor.congr_obj s x) ≫ v.app (G.obj x) = G.map (u.app x))
    (e : X ⋙ F = F ⋙ Y) (x : A) : eqToHom (Functor.congr_obj e x) ≫ v.app (F.obj x) = F.map (u.app x) := by
  subst G; exact law x
variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*}
  [Category* A₁] [Category* A₂] [Category* A₃] [Category* B₁] [Category* B₂] [Category* B₃]
theorem comp {F F' : A₁ ⥤ B₁} {G G' : A₂ ⥤ B₂} {H H' : A₃ ⥤ B₃}
    (hf : F = F') (hg : G = G') (hh : H = H')
    {X : A₂ ⥤ A₁} {Y : A₃ ⥤ A₂} {W : A₃ ⥤ A₁}
    {U : B₂ ⥤ B₁} {V : B₃ ⥤ B₂} {T : B₃ ⥤ B₁}
    (sd : W ⋙ F' = H' ⋙ T) (sa : X ⋙ F' = G' ⋙ U) (sb : Y ⋙ G' = H' ⋙ V)
    (u : W ⟶ Y ⋙ X) (v : T ⟶ V ⋙ U)
    (law : FibreValue.Paste.CompLaw (eqToIso sd) (eqToIso sa) (eqToIso sb) u v)
    (d : W ⋙ F = H ⋙ T) (a : X ⋙ F = G ⋙ U) (b : Y ⋙ G = H ⋙ V) :
    FibreValue.Paste.CompLaw (eqToIso d) (eqToIso a) (eqToIso b) u v := by subst F'; subst G'; subst H'; exact law
end Transport
noncomputable def taggedUnit (A : B) : ZeroPower.Sum.map (componentPull p d C Y (𝟙 A)) ⟶ 𝟭 _ :=
  Sigma.natTrans fun t => whiskerRight (partUnit p d C Y A t).hom (Sigma.incl (C := fun t => Total Y (leg p d A t)) t)
noncomputable def taggedComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    ZeroPower.Sum.map (componentPull p d C Y (a ≫ b)) ⟶
      ZeroPower.Sum.map (componentPull p d C Y b) ⋙ ZeroPower.Sum.map (componentPull p d C Y a) :=
  Sigma.natTrans fun t => whiskerRight (partComp p d C Y a b t).hom (Sigma.incl (C := fun t => Total Y (leg p d A t)) t)
theorem restrictEq {A D : B} (a : A ⟶ D) (t : I) :
    componentPull p d C Y a t ⋙ (Sigma.incl (C := fun n => Total Y (leg p d A n)) t ⋙ compare p d A Y) =
      (Sigma.incl (C := fun n => Total Y (leg p d D n)) t ⋙ compare p d D Y) ⋙ wholePull p d C Y a :=
  (congrArg (componentPull p d C Y a t ⋙ ·) (compareTag p d Y A t)).trans
    ((presentedSquare p d C Y a t).trans (congrArg (· ⋙ wholePull p d C Y a) (compareTag p d Y D t).symm))
theorem unitSummand (A : B) (t : I) (x : Total Y (leg p d A t)) :
    eqToHom (Functor.congr_obj (restrictEq p d C Y (𝟙 A) t) x) ≫
      (wholeUnit p d C Y A).hom.app ((compare p d A Y).obj ⟨t,x⟩) =
      (Sigma.incl (C := fun n => Total Y (leg p d A n)) t ⋙ compare p d A Y).map ((partUnit p d C Y A t).hom.app x) :=
  Transport.unit (compareTag p d Y A t) (presentedSquare p d C Y (𝟙 A) t) _ _
    (fun z => (Category.id_comp _).trans (presentedUnit p d C Y A t z).symm) (restrictEq p d C Y (𝟙 A) t) x
theorem forwardApp {A D : B} (a : A ⟶ D) (t : I) (x : Total Y (leg p d D t)) :
    (forward p d C Y a).inv.app ⟨t,x⟩ = eqToHom (Functor.congr_obj (restrictEq p d C Y a t) x) :=
  eqToHom_app _ _
theorem forwardUnit (A : B) (x : Σ t, Total Y (leg p d A t)) :
    (forward p d C Y (𝟙 A)).inv.app x ≫ (wholeUnit p d C Y A).hom.app ((compare p d A Y).obj x) =
      (compare p d A Y).map ((taggedUnit p d C Y A).app x) := by
  rcases x with ⟨t,x⟩
  exact (congrArg (· ≫ (wholeUnit p d C Y A).hom.app _) (forwardApp p d C Y (𝟙 A) t x)).trans (unitSummand p d C Y A t x)
theorem presentedLaw {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (t : I) :
    FibreValue.Paste.CompLaw (F := presentedTag p d Y A t) (G := presentedTag p d Y D t) (H := presentedTag p d Y E t)
      (eqToIso (presentedSquare p d C Y (a ≫ b) t)) (eqToIso (presentedSquare p d C Y a t)) (eqToIso (presentedSquare p d C Y b t))
      (partComp p d C Y a b t).hom (wholeComp p d C Y a b).hom := by
  intro x
  simp only [eqToIso.hom, eqToHom_app]
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _ ≫ (wholePull p d C Y a).map (𝟙 _)
  rw [Functor.map_id, Category.id_comp]
  exact (Category.id_comp _).trans ((presentedComp p d C Y a b t x).symm.trans (Category.comp_id _).symm)
abbrev tag (A : B) (t : I) := Sigma.incl (C := fun t => Total Y (leg p d A t)) t ⋙ compare p d A Y
theorem compSummand {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (t : I) :
    FibreValue.Paste.CompLaw (F := tag p d Y A t) (G := tag p d Y D t) (H := tag p d Y E t)
      (eqToIso (restrictEq p d C Y (a ≫ b) t)) (eqToIso (restrictEq p d C Y a t)) (eqToIso (restrictEq p d C Y b t))
      (partComp p d C Y a b t).hom (wholeComp p d C Y a b).hom :=
  Transport.comp (compareTag p d Y A t) (compareTag p d Y D t) (compareTag p d Y E t)
    (presentedSquare p d C Y (a ≫ b) t) (presentedSquare p d C Y a t) (presentedSquare p d C Y b t)
    (partComp p d C Y a b t).hom (wholeComp p d C Y a b).hom (presentedLaw p d C Y a b t)
    (restrictEq p d C Y (a ≫ b) t) (restrictEq p d C Y a t) (restrictEq p d C Y b t)
theorem forwardComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (x : Σ t, Total Y (leg p d E t)) :
    (forward p d C Y (a ≫ b)).inv.app x ≫ (wholeComp p d C Y a b).hom.app ((compare p d E Y).obj x) =
      (compare p d A Y).map ((taggedComp p d C Y a b).app x) ≫
        (forward p d C Y a).inv.app ((ZeroPower.Sum.map (componentPull p d C Y b)).obj x) ≫
        (wholePull p d C Y a).map ((forward p d C Y b).inv.app x) := by
  rcases x with ⟨t,x⟩
  have h := compSummand p d C Y a b t x
  simp only [eqToIso.hom,eqToHom_app] at h
  let v := (wholeComp p d C Y a b).hom.app ((compare p d E Y).obj ⟨t,x⟩)
  let u := (compare p d A Y).map ((taggedComp p d C Y a b).app ⟨t,x⟩)
  refine (congrArg (· ≫ v) (forwardApp p d C Y (a ≫ b) t x)).trans (h.trans ?_)
  apply congrArg (u ≫ ·)
  exact congrArg₂ (· ≫ ·) (forwardApp p d C Y a t ((componentPull p d C Y b t).obj x)).symm
    (congrArg (wholePull p d C Y a).map (forwardApp p d C Y b t x).symm)
end ContextualComposition.GrothendieckStep.PullLaws
