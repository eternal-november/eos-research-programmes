module
public import ContextualComposition.ContextualRaggedGrid
public import ContextualComposition.RaggedRigAdapter
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (F : C ⥤ C) [F.LaxBraided]
abbrev gatheringOfLax : Lin (binary (Binary.ofMonoidal (C:=C))) (𝟙_ C) where
  obj := F.obj
  map := F.map
  id := F.map_id
  seq := F.map_comp
  nil := Functor.LaxMonoidal.ε F
  cons := Functor.LaxMonoidal.μ F
theorem gatheringOfLax_natural : LinNatural (gatheringOfLax F) where
  bin p q := Functor.LaxMonoidal.μ_natural F p q
abbrev symmetricCross := cross (Additive.ofBraided (C:=C)) add_middle_involutive
theorem lax_dup :
    (λ_ (𝟙_ C)).inv ≫ (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
      Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) =
      Functor.LaxMonoidal.ε F ≫ F.map (λ_ (𝟙_ C)).inv := by
    let η := Functor.LaxMonoidal.ε F
    let μ := Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C)
    change (λ_ (𝟙_ C)).inv ≫ (η ⊗ₘ η) ≫ μ = η ≫ F.map (λ_ (𝟙_ C)).inv
    have h := Functor.LaxMonoidal.left_unitality_inv F (𝟙_ C)
    change (λ_ (F.obj (𝟙_ C))).inv ≫ η ▷ (F.obj (𝟙_ C)) ≫ μ = F.map (λ_ (𝟙_ C)).inv at h
    rw [← h, ← Category.assoc η, leftUnitor_inv_naturality]
    rw [Category.assoc, ← id_tensorHom, ← tensorHom_id, ← Category.assoc (𝟙 (𝟙_ C) ⊗ₘ η), tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
theorem gatheringOfLax_cross : LinCross (symmetricCross (C:=C)) (gatheringOfLax F) where
  dup := lax_dup F
  merge := by
    let η := Functor.LaxMonoidal.ε F
    let μ := Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C)
    change (λ_ (𝟙_ C)).hom ≫ η = ((η ⊗ₘ η) ≫ μ) ≫ F.map (λ_ (𝟙_ C)).hom
    apply (cancel_epi (λ_ (𝟙_ C)).inv).mp
    rw [Iso.inv_hom_id_assoc]
    have h := congrArg (fun g => g ≫ F.map (λ_ (𝟙_ C)).hom) (lax_dup F)
    simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id] at h ⊢
    exact h.symm
  middle a b c d := by
    simpa only [Binary.ofMonoidal, gatheringOfLax, binary, coeff, symmetricCross, cross,
      Additive.ofBraided, Category.assoc] using tensorμ_comp_μ_tensorHom_μ_comp_μ F a b c d

section Lin
variable (A : Lin (binary (Binary.ofMonoidal (C:=C))) (𝟙_ C))
abbrev linFunctor : C ⥤ C where
  obj := A.obj
  map := A.map
  map_id := A.id
  map_comp := A.seq
/-- The exact forward local diagrams for a chosen gathering for one tensor
context. Unlike a general structural coherence premise, all cells here
are binary or nullary; the original gathering is not replaced. -/
structure AdditiveContextLaws : Prop where
  natural : LinNatural A
  assoc : LinMonoidalForward (H:=additiveStructure (C:=C)) A
  swap : LinSymmetric (H:=additiveStructure (C:=C)) A
  left (x : C) : (λ_ (A.obj x)).hom =
    (A.nil ⊗ₘ 𝟙 (A.obj x)) ≫ A.cons (𝟙_ C) x ≫ A.map (λ_ x).hom
  right (x : C) : (ρ_ (A.obj x)).hom =
    (𝟙 (A.obj x) ⊗ₘ A.nil) ≫ A.cons x (𝟙_ C) ≫ A.map (ρ_ x).hom
abbrev linLax (h : AdditiveContextLaws A) : (linFunctor A).LaxBraided where
  toLaxMonoidal := Functor.LaxMonoidal.ofTensorHom A.nil A.cons h.natural.bin h.assoc.assoc h.left h.right
  braided x y := h.swap.swap x y

theorem actual_context_cross (h : AdditiveContextLaws A) : LinCross (symmetricCross (C:=C)) A := by
  let _ := linLax A h
  exact gatheringOfLax_cross (linFunctor A)
end Lin
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
