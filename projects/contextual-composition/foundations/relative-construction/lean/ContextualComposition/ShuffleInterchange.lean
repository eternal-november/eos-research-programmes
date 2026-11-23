module

public import Mathlib.Data.Set.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-! The terminal-base language example of the geometric parallel-crossing report. Sequencing is concatenation and parallel is all order-preserving shuffles. -/

@[expose] public section
namespace ContextualComposition.ShuffleInterchange

open CategoryTheory
universe u
variable {A : Type u}

inductive Weave : List A → List A → List A → Prop
  | nil : Weave [] [] []
  | left (a : A) {u v w} : Weave u v w → Weave (a::u) v (a::w)
  | right (a : A) {u v w} : Weave u v w → Weave u (a::v) (a::w)

theorem Weave.swap {u v w : List A} (h : Weave u v w) : Weave v u w := by
  induction h with
  | nil => exact .nil
  | left a _ ih => exact .right a ih
  | right a _ ih => exact .left a ih

theorem Weave.append {u v w u' v' w' : List A} (h : Weave u v w) (k : Weave u' v' w') :
    Weave (u++u') (v++v') (w++w') := by
  induction h with
  | nil => exact k
  | left a _ ih => exact .left a ih
  | right a _ ih => exact .right a ih

theorem Weave.empty (w : List A) : Weave [] w w := by
  induction w with
  | nil => exact .nil
  | cons h _ ih => exact .right h ih

theorem Weave.empty_forces {v w : List A} (h : Weave [] v w) : v=w := by
  generalize e : ([] : List A) = u at h
  induction h with
  | nil => rfl
  | left _ _ _ => contradiction
  | right a _ ih => exact congrArg (List.cons a) (ih e)

theorem Weave.regroup {u v w t z : List A} (h : Weave u v t) (k : Weave t w z) :
    ∃ s, Weave v w s ∧ Weave u s z := by
  induction k generalizing u v with
  | nil => cases h; exact ⟨[],.nil,.nil⟩
  | left a _ ih =>
    cases h with
    | left _ h =>
      obtain ⟨s,e,f⟩ := ih h
      exact ⟨s,e,.left a f⟩
    | right _ h =>
      obtain ⟨s,e,f⟩ := ih h
      exact ⟨a::s,.left a e,.right a f⟩
  | right a _ ih =>
    obtain ⟨s,e,f⟩ := ih h
    exact ⟨a::s,.right a e,.right a f⟩

abbrev Language (A : Type u) := Set (List A)
def unit : Language A := {[]}
def seq (X Y : Language A) : Language A := {w | ∃ x ∈ X, ∃ y ∈ Y, x++y=w}
def parallel (X Y : Language A) : Language A := {w | ∃ x ∈ X, ∃ y ∈ Y, Weave x y w}

theorem seq_assoc (X Y Z : Language A) : seq (seq X Y) Z = seq X (seq Y Z) := by
  ext w; constructor
  · rintro ⟨_,⟨x,hx,y,hy,rfl⟩,z,hz,rfl⟩; exact ⟨x,hx,y++z,⟨y,hy,z,hz,rfl⟩,(List.append_assoc _ _ _).symm⟩
  · rintro ⟨x,hx,_,⟨y,hy,z,hz,rfl⟩,rfl⟩; exact ⟨x++y,⟨x,hx,y,hy,rfl⟩,z,hz,List.append_assoc _ _ _⟩

theorem seq_unit (X : Language A) : seq unit X = X ∧ seq X unit = X := by
  constructor <;> ext w <;> constructor
  · rintro ⟨_,rfl,y,hy,rfl⟩; exact hy
  · intro h; exact ⟨[],rfl,w,h,rfl⟩
  · rintro ⟨x,hx,_,rfl,rfl⟩; simpa using hx
  · intro h; exact ⟨w,h,[],rfl,List.append_nil w⟩

theorem parallel_unit (X : Language A) : parallel unit X = X := by
  ext w; constructor
  · rintro ⟨_,rfl,v,hv,e⟩; exact e.empty_forces ▸ hv
  · intro h; exact ⟨[],rfl,w,h,Weave.empty w⟩

theorem parallel_symm (X Y : Language A) : parallel X Y = parallel Y X := by
  ext w; constructor <;> rintro ⟨u,hu,v,hv,e⟩ <;> exact ⟨v,hv,u,hu,e.swap⟩

theorem parallel_assoc (X Y Z : Language A) : parallel (parallel X Y) Z = parallel X (parallel Y Z) := by
  ext w; constructor
  · rintro ⟨_,⟨x,hx,y,hy,h⟩,z,hz,k⟩
    obtain ⟨s,e,f⟩ := h.regroup k
    exact ⟨x,hx,s,⟨y,hy,z,hz,e⟩,f⟩
  · rintro ⟨x,hx,_,⟨y,hy,z,hz,h⟩,k⟩
    obtain ⟨s,e,f⟩ := h.swap.regroup k.swap
    exact ⟨s,⟨x,hx,y,hy,e.swap⟩,z,hz,f.swap⟩

theorem colax (X X' Y Y' : Language A) :
    seq (parallel X X') (parallel Y Y') ⊆ parallel (seq X Y) (seq X' Y') := by
  rintro _ ⟨_,⟨a,ha,b,hb,h⟩,_,⟨c,hc,d,hd,k⟩,rfl⟩
  exact ⟨a++c,⟨a,ha,c,hc,rfl⟩,b++d,⟨b,hb,d,hd,rfl⟩,h.append k⟩

def comparison (X X' Y Y' : Language A) :
    seq (parallel X X') (parallel Y Y') ⟶ parallel (seq X Y) (seq X' Y') := homOfLE (colax X X' Y Y')

def letter (a : ℕ) : Language ℕ := {[a]}

theorem two_letters {a b : ℕ} {w : List ℕ} (h : w ∈ parallel (letter a) (letter b)) :
    w=[a,b] ∨ w=[b,a] := by
  rcases h with ⟨_,rfl,_,rfl,e⟩
  cases e with
  | left _ e => exact Or.inl (congrArg (List.cons _) e.empty_forces.symm)
  | right _ e => exact Or.inr (congrArg (List.cons _) e.swap.empty_forces.symm)

theorem separating_word :
    [0,2,1,3] ∈ parallel (seq (letter 0) (letter 2)) (seq (letter 1) (letter 3)) ∧
    [0,2,1,3] ∉ seq (parallel (letter 0) (letter 1)) (parallel (letter 2) (letter 3)) := by
  constructor
  · exact ⟨[0,2],⟨[0],rfl,[2],rfl,rfl⟩,[1,3],⟨[1],rfl,[3],rfl,rfl⟩,
      .left 0 (.left 2 (.right 1 (.right 3 .nil)))⟩
  · rintro ⟨p,hp,q,hq,e⟩
    rcases two_letters hp with rfl | rfl <;> rcases two_letters hq with rfl | rfl <;> contradiction

theorem noninvertible_interchange : ¬IsIso (comparison (letter 0) (letter 1) (letter 2) (letter 3)) := by
  intro h
  exact separating_word.2 ((leOfHom (inv (comparison (letter 0) (letter 1) (letter 2) (letter 3)))) separating_word.1)

end ContextualComposition.ShuffleInterchange
