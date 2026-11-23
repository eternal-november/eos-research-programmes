module
public import ContextualComposition.CouplingPullbacks
public import Mathlib.Data.Set.Image

/-! A weakly pullback-preserving functor with distinct full and diagonal bit couplings. Every comparison uses the same raw carriers. -/

@[expose] public section
namespace ContextualComposition.CouplingPossibilities
open CategoryTheory CouplingPullbacks
set_option backward.isDefEq.respectTransparency false

universe u
abbrev Poss (X : Type u) := {s : Set X // s.Nonempty}

def image {X Y : Type u} (f : X → Y) (s : Poss X) : Poss Y :=
  ⟨f '' s.val,s.property.image f⟩

def possibilities : Type u ⥤ Type u where
  obj := Poss
  map f := TypeCat.ofHom (image (fun x => f x))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change id '' s.val = s.val
    exact Set.image_id _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (fun x => g (f x)) '' s.val = (fun y => g y) '' ((fun x => f x) '' s.val)
    exact (Set.image_image (fun y => g y) (fun x => f x) s.val).symm

theorem weak : WeakPullbacks possibilities.{u} := by
  intro X Y S f g w
  obtain ⟨⟨a,b⟩,eq⟩ := w
  have same : f '' a.val = g '' b.val := congrArg Subtype.val eq
  have mate (x : X) (hx : x ∈ a.val) : ∃ y ∈ b.val, g y = f x := by
    change f x ∈ g '' b.val
    rw [← same]
    exact ⟨x,hx,rfl⟩
  have mate' (y : Y) (hy : y ∈ b.val) : ∃ x ∈ a.val, f x = g y := by
    change g y ∈ f '' a.val
    rw [same]
    exact ⟨y,hy,rfl⟩
  let joint : Set (PB f g) := fun p => p.val.1 ∈ a.val ∧ p.val.2 ∈ b.val
  have nonempty : joint.Nonempty := by
    obtain ⟨x,hx⟩ := a.property
    obtain ⟨y,hy,he⟩ := mate x hx
    exact ⟨⟨(x,y),he.symm⟩,hx,hy⟩
  refine ⟨⟨joint,nonempty⟩, Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
  · ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht.1
    · intro hx
      obtain ⟨y,hy,he⟩ := mate x hx
      exact ⟨⟨(x,y),he.symm⟩,⟨hx,hy⟩,rfl⟩
  · ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht.2
    · intro hy
      obtain ⟨x,hx,he⟩ := mate' y hy
      exact ⟨⟨(x,y),he⟩,⟨hx,hy⟩,rfl⟩

def diagonal : Poss (Bool × Bool) := ⟨{p | p.1 = p.2},⟨(false,false),rfl⟩⟩
def full : Poss (Bool × Bool) := ⟨Set.univ,⟨(false,false),trivial⟩⟩

theorem distinct : diagonal ≠ full := by
  intro eq
  have h : (false,true) ∈ diagonal.val := eq ▸ (show (false,true) ∈ full.val from trivial)
  exact Bool.noConfusion h

theorem same_marginals : pairComparison possibilities Bool Bool diagonal =
    pairComparison possibilities Bool Bool full := by
  apply Subtype.ext
  apply Prod.ext
  · rw [pair_left,pair_left]
    apply Subtype.ext
    ext x
    exact ⟨fun _ => ⟨(x,x),trivial,rfl⟩,fun _ => ⟨(x,x),rfl,rfl⟩⟩
  · rw [pair_right,pair_right]
    apply Subtype.ext
    ext x
    exact ⟨fun _ => ⟨(x,x),trivial,rfl⟩,fun _ => ⟨(x,x),rfl,rfl⟩⟩

theorem quadrilateral_failure : ¬ QuadBijective possibilities.{0} := by
  intro h
  exact distinct (((pair_of_quad possibilities weak h) Bool Bool).injective same_marginals)

end ContextualComposition.CouplingPossibilities
