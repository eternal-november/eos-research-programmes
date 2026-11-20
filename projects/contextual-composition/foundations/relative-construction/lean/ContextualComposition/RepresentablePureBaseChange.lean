module
public import ContextualComposition.RepresentablePureBuilder
public import ContextualComposition.RepresentableStrictFold
public import ContextualComposition.RepresentableKleisliGeneric
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureBaseChange
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {A C D : Type*} [Category* A] [Category* C] [Bicategory D]
variable (G : A ⥤ C) (F : LocallyDiscrete C ⥤ᵖ D)
variable {a b c : A}

theorem comp (f : a ⟶ b) (g : b ⟶ c) :
    ((G.toPseudofunctor.comp F).mapComp f.toLoc g.toLoc).symm =
      (F.mapComp (G.map f).toLoc (G.map g).toLoc).symm ≪≫
        eqToIso (congrArg (fun k => F.map k.toLoc) (G.map_comp f g).symm) := by
  let e : (G.map (f ≫ g)).toLoc = (G.map f ≫ G.map g).toLoc := congrArg _ (G.map_comp f g)
  change (F.map₂Iso (eqToIso e) ≪≫ F.mapComp (G.map f).toLoc (G.map g).toLoc).symm = _
  rw [F.toPrelaxFunctor.map₂Iso_eqToIso]
  rfl

theorem unit (a : A) :
    (G.toPseudofunctor.comp F).mapId ⟨a⟩ =
      eqToIso (congrArg (fun k => F.map k.toLoc) (G.map_id a)) ≪≫ F.mapId ⟨G.obj a⟩ := by
  let e : (G.map (𝟙 a)).toLoc = (𝟙 (G.obj a)).toLoc := congrArg _ (G.map_id a)
  change F.map₂Iso (eqToIso e) ≪≫ F.mapId ⟨G.obj a⟩ = _
  rw [F.toPrelaxFunctor.map₂Iso_eqToIso]

section Assembly
open RepresentableBicategoryAssembly RepresentablePureBuilder
variable {X : Type*} {H : X → X → Type*} [∀ x y, Category (H x y)] {O : Operations H}
variable (L : Laws O) (F₀ : Faces (A := C) O)

theorem buildComp (f : a ⟶ b) (g : b ⟶ c) :
    letI := build O L
    ((G.toPseudofunctor.comp (buildPure L F₀)).mapComp f.toLoc g.toLoc).symm =
      F₀.comp (G.map f) (G.map g) ≪≫ eqToIso (congrArg (fun k => F₀.map k) (G.map_comp f g).symm) := by
  letI : Bicategory X := build O L
  exact comp G (buildPure L F₀) f g
end Assembly

section Strict
variable {Q : Type*} [Bicategory Q] [Bicategory.Strict Q] {x y z w : Q}

theorem foldSuffix (f : x ⟶ y) (g : y ⟶ z) (p : z ⟶ w)
    {k j : x ⟶ w} (i : k ≅ f ≫ (g ≫ p)) (e : (f ≫ g) ≫ p = j) :
    (i ≪≫ (α_ f g p).symm) ≪≫ eqToIso e =
      i ≪≫ eqToIso ((Category.assoc f g p).symm.trans e) := by
  rw [Strict.associator_eqToIso,RepresentableKleisliGeneric.symCast,Iso.trans_assoc,RepresentableStrictFold.castIsoComp]
end Strict

end ContextualComposition.GrothendieckStep.RepresentablePureBaseChange
