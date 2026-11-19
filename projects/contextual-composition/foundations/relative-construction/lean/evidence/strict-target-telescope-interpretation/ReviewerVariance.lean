import ContextualComposition.EndpointInterpretation
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
namespace ReviewerVariance
set_option backward.isDefEq.respectTransparency false
inductive B | pt
instance : Category B where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev b := B.pt
abbrev G := Discrete Unit
abbrev g : G := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of G)
  extend A := (Functor.const _).obj A
  lift f := { app := fun _ => f }
theorem split : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
-- Precomposition acts on Boolean observables. This is a genuine, nonconstant presheaf action.
def Y : Bᵒᵖ ⥤ Cat.{0,0} where
  obj _ := Cat.of (Discrete (Bool → Bool))
  map f := (Discrete.functor (fun z : Bool → Bool => Discrete.mk (z ∘ f.unop))).toCatHom
  map_id _ := by
    apply congrArg Functor.toCatHom
    fapply Functor.ext
    · rintro ⟨x⟩; rfl
    · exact fun _ _ _ => Subsingleton.elim _ _
  map_comp _ _ := by apply congrArg Functor.toCatHom; apply Functor.ext (fun _ => rfl)
def c : b ⟶ b := fun _ => false
def ell (A : B) : (𝟭 G) ⋙ P.extend A ⟶ P.extend A where
  app _ := fun _ => true
theorem noninvertible : ¬ IsIso ((ell b).app g) := by
  intro h
  let f := (ell b).app g
  have h₁ := congrFun (IsIso.hom_inv_id f) false
  have h₂ := congrFun (IsIso.hom_inv_id f) true
  change (inv f) true = false at h₁
  change (inv f) true = true at h₂
  exact Bool.noConfusion (h₁.symm.trans h₂)
def F (A : B) := restrict Y (P.extend A) (P.extend A) (𝟭 G) (ell A)
def x := pair Y (P.extend b) g (Discrete.mk (id : Bool → Bool))
def see (y : Total Y (P.extend b)) := (payload Y _ y).as false
-- F has the correct fibre type and is natural on grade arrows. Grade base change is even strict.
example (f : b ⟶ b) : (P.grades.map f.op).toFunctor ⋙ (𝟭 G) = (𝟭 G) ⋙ (P.grades.map f.op).toFunctor := rfl
-- Still the unverified endpoint square would let in a false transformation.
theorem breaksBase : P.baseRestrict Y c ⋙ F b ≠ F b ⋙ P.baseRestrict Y c := by
  intro h
  have q := congrArg see (Functor.congr_obj h x)
  exact Bool.noConfusion q
theorem cannotLift : ¬ ∃ H : PackedFree.step split ⟶ PackedFree.step split,
    ∀ Z A, (H.app Z).app (op A) = (restrict Z (P.extend A) (P.extend A) (𝟭 G) (ell A)).toCatHom := by
  rintro ⟨H,hh⟩
  apply breaksBase
  have n := (H.app Y).naturality c.op
  rw [hh Y b] at n
  exact congrArg Cat.Hom.toFunctor n
end ReviewerVariance
