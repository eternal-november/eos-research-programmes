import Mathlib

namespace ReceiptInterfaces

structure Interface (Q V : Type) where
  State : Type
  query : State → Q → Option V

structure Replacement {Q V : Type} (Allowed : Q → Prop)
    (source target : Interface Q V) where
  map : source.State → target.State
  reflect : ∀ s q, Allowed q → target.query (map s) q = source.query s q

def identity {Q V : Type} (Allowed : Q → Prop) (I : Interface Q V) :
    Replacement Allowed I I where
  map := id
  reflect := by intros; rfl

def compose {Q V : Type} {Allowed : Q → Prop} {A B C : Interface Q V}
    (f : Replacement Allowed A B) (g : Replacement Allowed B C) :
    Replacement Allowed A C where
  map := g.map ∘ f.map
  reflect := by
    intro s q h
    exact (g.reflect (f.map s) q h).trans (f.reflect s q h)

def weakening {Q V : Type} {P P' : Q → Prop} {A B : Interface Q V}
    (f : Replacement P A B) (h : ∀ q, P' q → P q) :
    Replacement P' A B where
  map := f.map
  reflect := by
    intro s q hq
    exact f.reflect s q (h q hq)

theorem comp_assoc {Q V : Type} {P : Q → Prop} {A B C D : Interface Q V}
    (f : Replacement P A B) (g : Replacement P B C) (h : Replacement P C D) :
    compose (compose f g) h = compose f (compose g h) := rfl

theorem left_unit {Q V : Type} {P : Q → Prop} {A B : Interface Q V}
    (f : Replacement P A B) : compose (identity P A) f = f := rfl

theorem right_unit {Q V : Type} {P : Q → Prop} {A B : Interface Q V}
    (f : Replacement P A B) : compose f (identity P B) = f := rfl

theorem forgotten_exact_cannot_reflect {Q V : Type} {P : Q → Prop} {A B : Interface Q V}
    (map : A.State → B.State) (s : A.State) (q : Q) (v : V)
    (allowed : P q) (src : A.query s q = some v) (dst : B.query (map s) q = none) :
    ¬ (∀ s q, P q → B.query (map s) q = A.query s q) := by
  intro h
  have obs := h s q allowed
  rw [src, dst] at obs
  contradiction

theorem wire_gain (w n s mask : Nat) (h : s ≤ n) :
    (1 + mask + w * (n-s) < 1 + w * n) ↔ mask < w*s := by
  have hs : n - s + s = n := Nat.sub_add_cancel h
  have e : w * (n-s) + w*s = w*n := by
    rw [← Nat.mul_add, hs]
  omega

end ReceiptInterfaces
