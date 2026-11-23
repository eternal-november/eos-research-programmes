module
public import ContextualComposition.RelativeTensorMixedEndpointCompatibility

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section BundleJointInterface
section Cat
variable {D : Type*} [Category* D] {F G : LocallyDiscrete D ⥤ᵖ Cat}
variable (μ : ∀ a, F.obj a ⥤ G.obj a)
variable (σ : ∀ {a b} (f : a ⟶ b), (F.map f).toFunctor ⋙ μ b ≅ μ a ⋙ (G.map f).toFunctor)

def strongCatFromEndpointLaws
    (un : ∀ a, RespectsEndpointIdentity (σ (𝟙 a)) (F.mapId a).hom.toNatTrans (G.mapId a).hom.toNatTrans)
    (cp : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c),
      RespectsEndpointComposition (σ f) (σ g) (σ (f ≫ g))
        (F.mapComp f g).hom.toNatTrans (G.mapComp f g).hom.toNatTrans) : F ⟶ G where
  app a := (μ a).toCatHom
  naturality f := Cat.Hom.isoMk (σ f)
  naturality_naturality {a b f g} η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := Subsingleton.elim η (𝟙 f)
    rw [PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    simp
  naturality_id a := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (σ (𝟙 a)).hom.app x ≫ (G.mapId a).hom.toNatTrans.app ((μ a).obj x) =
      (μ a).map ((F.mapId a).hom.toNatTrans.app x) ≫ 𝟙 _ ≫ 𝟙 _
    simpa only [Category.comp_id] using un a x
  naturality_comp {a b c} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (σ (f ≫ g)).hom.app x ≫ (G.mapComp f g).hom.toNatTrans.app ((μ a).obj x) =
      (μ c).map ((F.mapComp f g).hom.toNatTrans.app x) ≫ 𝟙 _ ≫
      (σ g).hom.app ((F.map f).toFunctor.obj x) ≫ 𝟙 _ ≫
      (G.map g).toFunctor.map ((σ f).hom.app x) ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using cp f g x
end Cat

section Curried
variable {D E : Type*} [Category* D] [Bicategory E] {F G : LocallyDiscrete D ⥤ᵖ (E ⥤ᵖ Cat)}
variable (μ : ∀ a, F.obj a ⟶ G.obj a)
variable (σ : ∀ {a b} (f : a ⟶ b), F.map f ≫ μ b ≅ μ a ≫ G.map f)

def strongCurriedFromEndpointLaws
    (un : ∀ a d, RespectsEndpointIdentity (Cat.Hom.toNatIso ((Middle.evaluate d).map₂Iso (σ (𝟙 a))))
      ((F.mapId a).hom.as.app d).toNatTrans ((G.mapId a).hom.as.app d).toNatTrans)
    (cp : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c) d,
      RespectsEndpointComposition (Cat.Hom.toNatIso ((Middle.evaluate d).map₂Iso (σ f)))
        (Cat.Hom.toNatIso ((Middle.evaluate d).map₂Iso (σ g)))
        (Cat.Hom.toNatIso ((Middle.evaluate d).map₂Iso (σ (f ≫ g))))
        ((F.mapComp f g).hom.as.app d).toNatTrans ((G.mapComp f g).hom.as.app d).toNatTrans) :
    F ⟶ G where
  app := μ
  naturality f := σ f
  naturality_naturality {a b f g} η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := Subsingleton.elim η (𝟙 f)
    rw [PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    simp
  naturality_id a := by
    apply Pseudofunctor.StrongTrans.homCategory.ext; intro d
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change ((σ (𝟙 a)).hom.as.app d).toNatTrans.app x ≫
      ((G.mapId a).hom.as.app d).toNatTrans.app (((μ a).app d).toFunctor.obj x) =
      ((μ a).app d).toFunctor.map (((F.mapId a).hom.as.app d).toNatTrans.app x) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    exact un a d x
  naturality_comp {a b c} f g := by
    apply Pseudofunctor.StrongTrans.homCategory.ext; intro d
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change ((σ (f ≫ g)).hom.as.app d).toNatTrans.app x ≫
      ((G.mapComp f g).hom.as.app d).toNatTrans.app (((μ a).app d).toFunctor.obj x) =
      ((μ c).app d).toFunctor.map (((F.mapComp f g).hom.as.app d).toNatTrans.app x) ≫ 𝟙 _ ≫
      ((σ g).hom.as.app d).toNatTrans.app (((F.map f).app d).toFunctor.obj x) ≫ 𝟙 _ ≫
      ((G.map g).app d).toFunctor.map (((σ f).hom.as.app d).toNatTrans.app x) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact cp f g d x
end Curried

section Modification
variable {D : Type*} [Category* D] {F F' G G' : LocallyDiscrete D ⥤ᵖ Cat}
variable (V : F ⟶ F') (W : G ⟶ G') (l : F ⟶ G) (r : F' ⟶ G')
variable (o : ∀ a, (V.app a).toFunctor ⋙ (r.app a).toFunctor ≅ (l.app a).toFunctor ⋙ (W.app a).toFunctor)

def ColumnCubeLaw : Prop :=
  ∀ {a b} (f : a ⟶ b),
      JointEndpointSquare (Cat.Hom.toNatIso (V.naturality f)) (Cat.Hom.toNatIso (W.naturality f))
        (Cat.Hom.toNatIso (l.naturality f)) (Cat.Hom.toNatIso (r.naturality f)) (o a) (o b)

/-- A family of natural isomorphisms lifts to an invertible modification
when the mixed six-arrow equation holds. -/
def isoFromJointEndpointLaws (j : ColumnCubeLaw V W l r o) :
    V ≫ r ≅ l ≫ W :=
  Pseudofunctor.StrongTrans.isoMk (fun a => Cat.Hom.isoMk (o a)) (by
    intro a b f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (o b).hom.app ((F.map f).toFunctor.obj x) ≫ (𝟙 _ ≫
        (W.app b).toFunctor.map ((l.naturality f).hom.toNatTrans.app x) ≫ 𝟙 _ ≫
          (W.naturality f).hom.toNatTrans.app ((l.app a).toFunctor.obj x) ≫ 𝟙 _) =
      (𝟙 _ ≫ (r.app b).toFunctor.map ((V.naturality f).hom.toNatTrans.app x) ≫ 𝟙 _ ≫
        (r.naturality f).hom.toNatTrans.app ((V.app a).toFunctor.obj x) ≫ 𝟙 _) ≫
      (G'.map f).toFunctor.map ((o a).hom.app x)
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    exact j f x)
end Modification
end BundleJointInterface

section BundleBoundary
section Boundary
variable {D : Type*} [Category* D] {F F' G G' : LocallyDiscrete D ⥤ᵖ Cat}
variable (V : F ⟶ F') (W : G ⟶ G') (l : F ⟶ G) (r : F' ⟶ G')
variable (L : ∀ a, F.obj a ⥤ G.obj a) (R : ∀ a, F'.obj a ⥤ G'.obj a)
variable (i : ∀ {a b} (f : a ⟶ b), (F.map f).toFunctor ⋙ L b ≅ L a ⋙ (G.map f).toFunctor)
variable (j : ∀ {a b} (f : a ⟶ b), (F'.map f).toFunctor ⋙ R b ≅ R a ⋙ (G'.map f).toFunctor)
variable (o : ∀ a, (V.app a).toFunctor ⋙ R a ≅ L a ⋙ (W.app a).toFunctor)
variable (o' : ∀ a, (V.app a).toFunctor ⋙ (r.app a).toFunctor ≅ (l.app a).toFunctor ⋙ (W.app a).toFunctor)

/-- Six-arrow law stated only in terms of explicitly named raw functors and isos;
in particular its four multiplication faces do not project from a bundled column. -/
def RawColumnCube : Prop :=
  ∀ {a b} (f : a ⟶ b),
    JointEndpointSquare (Cat.Hom.toNatIso (V.naturality f)) (Cat.Hom.toNatIso (W.naturality f))
      (i f) (j f) (o a) (o b)

/-- Transport the raw cube into the bundled consumer, eliminating all dependent
endpoint types generically before the retained quotient is substituted. -/
theorem ColumnCubeLaw.of_raw
    (hL : L = fun a => (l.app a).toFunctor) (hR : R = fun a => (r.app a).toFunctor)
    (hi : ∀ {a b} (f : a ⟶ b), HEq (i f) (Cat.Hom.toNatIso (l.naturality f)))
    (hj : ∀ {a b} (f : a ⟶ b), HEq (j f) (Cat.Hom.toNatIso (r.naturality f)))
    (ho : ∀ a, HEq (o a) (o' a))
    (h : RawColumnCube V W L R i j o) :
    ColumnCubeLaw V W l r o' := by
  subst L; subst R
  intro a b f
  exact (by
    have hh := h f
    change JointEndpointSquare (Cat.Hom.toNatIso (V.naturality f)) (Cat.Hom.toNatIso (W.naturality f)) (i f) (j f) (o a) (o b) at hh
    rw [eq_of_heq (hi f), eq_of_heq (hj f), eq_of_heq (ho a), eq_of_heq (ho b)] at hh
    exact hh)

variable
  (lu : ∀ a, RespectsEndpointIdentity (i (𝟙 a)) (F.mapId a).hom.toNatTrans (G.mapId a).hom.toNatTrans)
  (lc : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), RespectsEndpointComposition (i f) (i g) (i (f ≫ g))
    (F.mapComp f g).hom.toNatTrans (G.mapComp f g).hom.toNatTrans)
  (ru : ∀ a, RespectsEndpointIdentity (j (𝟙 a)) (F'.mapId a).hom.toNatTrans (G'.mapId a).hom.toNatTrans)
  (rc : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c), RespectsEndpointComposition (j f) (j g) (j (f ≫ g))
    (F'.mapComp f g).hom.toNatTrans (G'.mapComp f g).hom.toNatTrans)

theorem ColumnCubeLaw.of_constructedColumns (h : RawColumnCube V W L R i j o) :
    ColumnCubeLaw V W (strongCatFromEndpointLaws L i lu lc) (strongCatFromEndpointLaws R j ru rc) o := by
  intro a b f
  exact @h a b f

end Boundary
end BundleBoundary

section BundleOuterBridge
theorem jointIso_evaluate
    {D : Type*} [Category* D] {F F' G G' : LocallyDiscrete D ⥤ᵖ Cat}
    (V : F ⟶ F') (W : G ⟶ G') (l : F ⟶ G) (r : F' ⟶ G')
    (o : ∀ a, (V.app a).toFunctor ⋙ (r.app a).toFunctor ≅ (l.app a).toFunctor ⋙ (W.app a).toFunctor)
    (j : ColumnCubeLaw V W l r o) (a : LocallyDiscrete D) :
    Cat.Hom.toNatIso ((Middle.evaluate a).map₂Iso (isoFromJointEndpointLaws V W l r o j)) = o a := by
  rfl

section Outer
variable {D E : Type*} [Category* D] [Category* E]
variable {F G : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete E ⥤ᵖ Cat)}
variable (μ : ∀ a, F.obj a ⟶ G.obj a)
variable (o : ∀ {a b} (f : a ⟶ b) (e : LocallyDiscrete E),
  ((F.map f).app e).toFunctor ⋙ ((μ b).app e).toFunctor ≅
    ((μ a).app e).toFunctor ⋙ ((G.map f).app e).toFunctor)
variable (cube : ∀ {a b} (f : a ⟶ b), ColumnCubeLaw (F.map f) (G.map f) (μ a) (μ b) (o f))

def CurriedRawUnit : Prop :=
  ∀ a e, RespectsEndpointIdentity (o (𝟙 a) e)
    ((F.mapId a).hom.as.app e).toNatTrans ((G.mapId a).hom.as.app e).toNatTrans

def CurriedRawComp : Prop :=
  ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c) e,
    RespectsEndpointComposition (o f e) (o g e) (o (f ≫ g) e)
      ((F.mapComp f g).hom.as.app e).toNatTrans ((G.mapComp f g).hom.as.app e).toNatTrans

def strongCurriedFromRawLaws (u : CurriedRawUnit μ o) (c : CurriedRawComp μ o) : F ⟶ G :=
  strongCurriedFromEndpointLaws μ
    (fun f => isoFromJointEndpointLaws (F.map f) (G.map f) (μ _) (μ _) (o f) (cube f))
    (by
      intro a e
      exact u a e)
    (by
      intro a b d f g e
      exact c f g e)

theorem strongCurriedFromRawLaws_app (u : CurriedRawUnit μ o) (c : CurriedRawComp μ o) (a : LocallyDiscrete D) :
    (strongCurriedFromRawLaws μ o cube u c).app a = μ a := rfl

theorem strongCurriedFromRawLaws_eval (u : CurriedRawUnit μ o) (c : CurriedRawComp μ o)
    {a b : LocallyDiscrete D} (f : a ⟶ b) (e : LocallyDiscrete E) :
    Cat.Hom.toNatIso ((Middle.evaluate e).map₂Iso ((strongCurriedFromRawLaws μ o cube u c).naturality f)) =
      o f e := rfl
end Outer
end BundleOuterBridge

section BundleOuterOrdinary
section Ordinary
variable {D E : Type*} [Category* D] [Category* E]
variable {F G : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete E ⥤ᵖ Cat)}
variable (μ : ∀ a : D, F.obj ⟨a⟩ ⟶ G.obj ⟨a⟩)
variable (o : ∀ {a b : D} (f : a ⟶ b) (e : LocallyDiscrete E),
  ((F.map f.toLoc).app e).toFunctor ⋙ ((μ b).app e).toFunctor ≅
    ((μ a).app e).toFunctor ⋙ ((G.map f.toLoc).app e).toFunctor)
variable (cube : ∀ {a b : D} (f : a ⟶ b), ColumnCubeLaw (F.map f.toLoc) (G.map f.toLoc) (μ a) (μ b) (o f))

def OrdinaryRawUnit : Prop :=
  ∀ (a : D) e, RespectsEndpointIdentity (o (𝟙 a) e)
    ((F.mapId ⟨a⟩).hom.as.app e).toNatTrans ((G.mapId ⟨a⟩).hom.as.app e).toNatTrans

def OrdinaryRawComp : Prop :=
  ∀ {a b c : D} (f : a ⟶ b) (g : b ⟶ c) e,
    RespectsEndpointComposition (o f e) (o g e) (o (f ≫ g) e)
      ((F.mapComp f.toLoc g.toLoc).hom.as.app e).toNatTrans ((G.mapComp f.toLoc g.toLoc).hom.as.app e).toNatTrans

def strongCurriedFromOrdinaryRawLaws (u : OrdinaryRawUnit μ o) (c : OrdinaryRawComp μ o) : F ⟶ G :=
  strongCurriedFromRawLaws (fun a => μ a.as)
    (fun f => o f.as) (fun f => @cube _ _ f.as)
    (fun a e => u a.as e) (fun f g e => c f.as g.as e)

theorem strongCurriedFromOrdinaryRawLaws_app (u : OrdinaryRawUnit μ o) (c : OrdinaryRawComp μ o) (a : D) :
    (strongCurriedFromOrdinaryRawLaws μ o cube u c).app ⟨a⟩ = μ a := rfl

theorem strongCurriedFromOrdinaryRawLaws_eval (u : OrdinaryRawUnit μ o) (c : OrdinaryRawComp μ o)
    {a b : D} (f : a ⟶ b) (e : LocallyDiscrete E) :
    Cat.Hom.toNatIso ((Middle.evaluate e).map₂Iso ((strongCurriedFromOrdinaryRawLaws μ o cube u c).naturality f.toLoc)) =
      o f e := rfl
end Ordinary
end BundleOuterOrdinary

end ContextualComposition.RelativeTensor.Iterated
