module

public import ContextualComposition.CouplingPossibilities
public import ContextualComposition.DependentConeInterchange

/-! The nonempty powerset supplies a separate commutative affine monad with the previously constructed weak-pullback functor. -/

@[expose] public section
namespace ContextualComposition.NonemptyPossibilityMonad

open CategoryTheory CouplingPossibilities CouplingPullbacks
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Type u}

def pure (x : X) : Poss X := ⟨{x},⟨x,rfl⟩⟩
def union (s : Poss (Poss X)) : Poss X :=
  ⟨{x | ∃ t ∈ s.val, x ∈ t.val}, by
    obtain ⟨t,ht⟩ := s.property; obtain ⟨x,hx⟩ := t.property
    exact ⟨x,t,ht,hx⟩⟩

def monad : CategoryTheory.Monad (Type u) where
  toFunctor := possibilities
  η := {
    app := fun _ => TypeCat.ofHom pure
    naturality := by
      intro A B f; apply ConcreteCategory.hom_ext; intro p; apply Subtype.ext
      change {f p} = f '' {p}
      exact Set.image_singleton.symm }
  μ := {
    app := fun _ => TypeCat.ofHom union
    naturality := by
      intro A B f; apply ConcreteCategory.hom_ext; intro p; apply Subtype.ext
      ext b
      change (∃ t ∈ image f '' p.val, b ∈ t.val) ↔ b ∈ f '' (union p).val
      constructor
      · rintro ⟨_,⟨t,ht,rfl⟩,a,ha,rfl⟩
        exact ⟨a,⟨t,ht,ha⟩,rfl⟩
      · rintro ⟨a,⟨t,ht,ha⟩,rfl⟩
        exact ⟨image f t,⟨t,ht,rfl⟩,a,ha,rfl⟩ }
  assoc A := by
    apply ConcreteCategory.hom_ext; intro s; apply Subtype.ext; ext x
    change (∃ t ∈ union '' s.val, x ∈ t.val) ↔ ∃ t ∈ (union s).val, x ∈ t.val
    constructor
    · rintro ⟨_,⟨t,ht,rfl⟩,a,ha,hx⟩; exact ⟨a,⟨t,ht,ha⟩,hx⟩
    · rintro ⟨a,⟨t,ht,ha⟩,hx⟩; exact ⟨union t,⟨t,ht,rfl⟩,a,ha,hx⟩
  left_unit A := by
    apply ConcreteCategory.hom_ext; intro s; apply Subtype.ext; ext x
    change (∃ t ∈ ({s} : Set (Poss A)), x ∈ t.val) ↔ x ∈ s.val
    simp
  right_unit A := by
    apply ConcreteCategory.hom_ext; intro s; apply Subtype.ext; ext x
    change (∃ t ∈ pure '' s.val, x ∈ t.val) ↔ x ∈ s.val
    constructor
    · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩; exact hy
    · intro hx; exact ⟨pure x,⟨x,hx,rfl⟩,rfl⟩

theorem bind_mem (p : Poss X) (k : X → Poss Y) (y : Y) :
    y ∈ (DependentConeInterchange.bind monad p k).val ↔ ∃ x ∈ p.val, y ∈ (k x).val := by
  change (∃ t ∈ k '' p.val, y ∈ t.val) ↔ _
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,hy⟩; exact ⟨x,hx,hy⟩
  · rintro ⟨x,hx,hy⟩; exact ⟨k x,⟨x,hx,rfl⟩,hy⟩

theorem affine : Subsingleton (monad.obj PUnit.{u+1}) where
  allEq p q := by
    apply Subtype.ext; ext x
    obtain ⟨y,hy⟩ := p.property; obtain ⟨z,hz⟩ := q.property
    exact ⟨fun _ => (Subsingleton.elim z x) ▸ hz,fun _ => (Subsingleton.elim y x) ▸ hy⟩

theorem exchange (p : Poss X) (q : Poss Y) (k : X → Y → Poss Z) :
    DependentConeInterchange.bind monad p (fun x => DependentConeInterchange.bind monad q (k x)) =
    DependentConeInterchange.bind monad q (fun y => DependentConeInterchange.bind monad p (fun x => k x y)) := by
  apply Subtype.ext; ext z; simp only [bind_mem]
  constructor <;> rintro ⟨a,ha,b,hb,h⟩ <;> exact ⟨b,hb,a,ha,h⟩

theorem weak : WeakPullbacks monad.toFunctor := CouplingPossibilities.weak

end ContextualComposition.NonemptyPossibilityMonad
