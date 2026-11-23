module
public import ContextualComposition.EndpointGrothendieck
public import Mathlib.CategoryTheory.Types.Basic

/-! Constantization at the empty interface for a genuinely pseudofunctorial covariant content fibre. The total comparison commutes with the projection to sets. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.EmptyContentTransport
open CategoryTheory CategoryTheory.Bicategory ContextualComposition.Factorization.Endpoint.Indexed
set_option backward.isDefEq.respectTransparency false
universe u w v
abbrev Zero := PEmpty.{u+1}
def initial (B : Type u) : Zero.{u} ⟶ B := TypeCat.ofHom PEmpty.elim
theorem initial_unique (B : Type u) (f g : Zero.{u} ⟶ B) : f = g := by
  apply ConcreteCategory.hom_ext; intro z; exact z.elim

variable (L : LocallyDiscrete (Type u) ⥤ᵖ Cat.{v,w})
abbrev Fibre (B : Type u) := L.obj ⟨B⟩
abbrev action {B D : Type u} (f : B ⟶ D) := (L.map f.toLoc).toFunctor
abbrev E (B : Type u) := action L (initial B)

def comparison {B D : Type u} (f : B ⟶ D) : E L B ⋙ action L f ≅ E L D :=
  (Cat.Hom.toNatIso (L.mapComp (initial B).toLoc f.toLoc)).symm ≪≫
    eqToIso (congrArg (action L) (initial_unique D (initial B ≫ f) (initial D)))

theorem all_equivalences (h : ∀ B, (E L B).IsEquivalence) {B D : Type u} (f : B ⟶ D) :
    (action L f).IsEquivalence := by
  let := h B
  let := h D
  let := Functor.isEquivalence_of_iso (comparison L f).symm
  exact Functor.isEquivalence_of_comp_left (E L B) (action L f)

abbrev Base := Type u × Fibre L Zero
abbrev Total := Pseudofunctor.Grothendieck L
def point (s : Base L) : Total L := ⟨s.1,(E L s.1).obj s.2⟩
abbrev start (Q : Fibre L Zero) := (outInclusion L Zero).obj Q
def κ (s : Base L) : start L s.2 ⟶ point L s := (outputLift L (initial s.1)).app s.2

/-- A total arrow over f is determined by its composite with the chosen lift from the empty fibre. -/
theorem cancel_initial {s t : Base L} (f g : point L s ⟶ point L t) (base : f.base = g.base)
    (after : κ L s ≫ f = κ L s ≫ g) : f = g := by
  obtain ⟨b,k⟩ := f
  obtain ⟨b',k'⟩ := g
  change b = b' at base
  subst b'
  obtain ⟨_,_,uniq⟩ := output_cocartesian L (initial s.1) b s.2 ((E L t.1).obj t.2)
    (κ L s ≫ (⟨b,k⟩ : point L s ⟶ point L t)) rfl
  have eq : k = k' := (uniq k rfl).trans (uniq k' after.symm).symm
  cases eq
  rfl

def send {s t : Base L} (f : s ⟶ t) : point L s ⟶ point L t :=
  ⟨f.1,(comparison L f.1).hom.app s.2 ≫ (E L t.1).map f.2⟩

theorem send_triangle {s t : Base L} (f : s ⟶ t) :
    κ L s ≫ send L f = (outInclusion L Zero).map f.2 ≫ κ L t := by
  dsimp only [κ]
  erw [(outputLift L (initial t.1)).naturality f.2]
  refine Pseudofunctor.Grothendieck.Hom.ext _ _ (initial_unique _ _ _) ?_
  dsimp [send,comparison,outInclusion,outputLift]
  simp [L.mapComp_id_right_hom_app,Strict.rightUnitor_eqToIso,Category.assoc]
  dsimp only [start,outInclusion]
  simp only [Functor.map_id, Category.id_comp]
  let i := Cat.Hom.toNatIso (L.mapComp (initial s.1).toLoc f.1.toLoc)
  change eqToHom _ ≫ i.hom.app s.2 ≫ i.inv.app s.2 ≫ eqToHom _ ≫ (E L t.1).map f.2 = _
  rw [Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc]
  exact Category.id_comp _

def constantize : Base L ⥤ Total L where
  obj := point L
  map := send L
  map_id s := by
    refine cancel_initial L (send L (𝟙 s)) (𝟙 (point L s)) rfl ?_
    rw [send_triangle]
    change (outInclusion L Zero).map (𝟙 s.2) ≫ κ L s = _
    simp
  map_comp {s t k} f g := by
    refine cancel_initial L (send L (f ≫ g)) (send L f ≫ send L g) rfl ?_
    rw [send_triangle, ← Category.assoc, send_triangle, Category.assoc, send_triangle, ← Category.assoc, ← Functor.map_comp]
    rfl

theorem over_base : constantize L ⋙ Pseudofunctor.Grothendieck.forget L = CategoryTheory.Prod.fst _ _ := rfl

def fullyFaithful (h : ∀ B, (E L B).FullyFaithful) : (constantize L).FullyFaithful where
  preimage {X Y} f := ⟨f.base,(h Y.1).preimage ((comparison L f.base).inv.app X.2 ≫ f.fiber)⟩
  map_preimage {X Y} f := by
    refine Pseudofunctor.Grothendieck.Hom.ext
      (send L (⟨f.base,(h Y.1).preimage ((comparison L f.base).inv.app X.2 ≫ f.fiber)⟩ : X ⟶ Y)) f rfl ?_
    change eqToHom _ ≫ (comparison L f.base).hom.app X.2 ≫ (E L Y.1).map _ = _
    simp
  preimage_map {X Y} f := by
    apply Prod.ext
    · rfl
    change (h Y.1).preimage ((comparison L f.1).inv.app X.2 ≫ (comparison L f.1).hom.app X.2 ≫ (E L Y.1).map f.2) = f.2
    simp

end ContextualComposition.EmptyContentTransport
