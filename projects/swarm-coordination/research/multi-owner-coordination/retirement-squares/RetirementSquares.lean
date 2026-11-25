import Mathlib

namespace RetirementSquares

def Square {X Y X' Y' : Type}
    (r : X → Y → Prop) (s : X' → Y' → Prop) (f : X → X') (g : Y → Y') : Prop :=
  ∀ x y, r x y → s (f x) (g y)

def thenRel {X Y Z : Type} (r : X → Y → Prop) (q : Y → Z → Prop) :
    X → Z → Prop := fun x z => ∃ y, r x y ∧ q y z

theorem pasteHorizontal {X Y Z X' Y' Z' : Type}
    {r : X → Y → Prop} {q : Y → Z → Prop} {r' : X' → Y' → Prop}
    {q' : Y' → Z' → Prop} {f : X → X'} {g : Y → Y'} {h : Z → Z'}
    (a : Square r r' f g) (b : Square q q' g h) :
    Square (thenRel r q) (thenRel r' q') f h := by
  rintro x z ⟨y,p,s⟩
  exact ⟨g y,a x y p,b y z s⟩

theorem pasteVertical {X Y X' Y' X'' Y'' : Type}
    {r : X → Y → Prop} {r' : X' → Y' → Prop} {r'' : X'' → Y'' → Prop}
    {f : X → X'} {g : Y → Y'} {f' : X' → X''} {g' : Y' → Y''}
    (a : Square r r' f g) (b : Square r' r'' f' g') :
    Square r r'' (f' ∘ f) (g' ∘ g) := by
  intro x y w
  exact b (f x) (g y) (a x y w)

theorem uniformRetire {S S' : Type} (m : S → S')
    (k : S → Bool) (k' : S' → Bool) (h : ∀ s, k' (m s) = k s) (rows : List S) :
    (rows.filter k).map m = (rows.map m).filter k' := by
  induction rows with
  | nil => rfl
  | cons x remaining ih =>
    simp only [List.filter_cons, List.map_cons, h]
    split <;> simp [ih]

theorem singleRetirementCounterexample :
    ∃ (p q : Fin 4 → Nat),
      (p 0 + p 1 + p 2 + p 3 = q 0 + q 1 + q 2 + q 3)
      ∧ (p 0 + p 2 = q 0 + q 2)
      ∧ (p 0 + p 1 = q 0 + q 1)
      ∧ p 0 ≠ q 0 := by
  exact ⟨![1,0,0,1],![0,1,1,0],by decide,by decide,by decide,by decide⟩

#print axioms pasteHorizontal
#print axioms pasteVertical
#print axioms uniformRetire
#print axioms singleRetirementCounterexample
end RetirementSquares
