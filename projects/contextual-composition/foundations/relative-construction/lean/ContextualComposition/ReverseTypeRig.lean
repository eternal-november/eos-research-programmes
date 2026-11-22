module

public import ContextualComposition.RaggedFubini

@[expose] public section

/-! Concrete discharge of every elementary diagram of the ragged binary
theorem in reverse functions, disjoint union and Cartesian product. The
additive sum is not a categorical coproduct in this category. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
universe u w
def coeff : Coeff (Type u) where
  Hom A B := B → A
  id _ := id
  seq f g := f ∘ g
  id_seq _ := rfl
  seq_id _ := rfl
  assoc _ _ _ := rfl
abbrev sum : Bi coeff.{u} where
  obj := Sum
  map := Sum.map
  map_id _ _ := by funext x; cases x <;> rfl
  map_seq _ _ _ _ := by funext x; cases x <;> rfl
abbrev tensor : Bi coeff.{u} where
  obj := Prod
  map f g x := (f x.1,g x.2)
  map_id _ _ := rfl
  map_seq _ _ _ _ := rfl
abbrev gather : Gather sum.{u} tensor PEmpty where
  nil _ := fun x => x.1.elim
  cons _ _ _ := fun ⟨s,c⟩ => match s with
    | .inl a => .inl (a,c)
    | .inr b => .inr (b,c)
  nil_nat _ := by funext x; exact x.1.elim
  cons_nat _ _ {_ _} _ := by funext ⟨t,_⟩; cases t <;> rfl
abbrev left : LeftGather sum.{u} tensor PEmpty where
  nil _ := fun x => x.2.elim
  cons _ _ _ := fun ⟨a,s⟩ => match s with
    | .inl b => .inl (a,b)
    | .inr c => .inr (a,c)
abbrev middle : Middle tensor.{u} PUnit where
  empty _ := ⟨⟩
  cell _ _ _ _ := fun ⟨⟨a,c⟩,b,d⟩ => ((a,b),(c,d))
  nat _ _ _ _ := rfl
def inv : MiddleInv middle.{u} where
  empty := ⟨fun _ => (⟨⟩,⟨⟩),rfl,rfl⟩
  cell _ _ _ _ := ⟨fun ⟨⟨a,b⟩,c,d⟩ => ((a,c),(b,d)),rfl,rfl⟩
theorem outerLaws : MedialLinear middle.{u} gather left where
  x _ _ _ := {
    nil := by funext x; exact x.1.1.elim
    cons := by intro a b; funext ⟨⟨x,_⟩,_⟩; cases x <;> rfl }
  y _ _ _ := {
    nil := by funext x; exact x.1.2.elim
    cons := by intro a b; funext ⟨⟨_,x⟩,_⟩; cases x <;> rfl }
theorem innerLaws : MedialInner middle.{u} gather left where
  b _ _ _ := {
    nil := by funext x; exact x.2.1.elim
    cons := by intro a b; funext ⟨_,x,_⟩; cases x <;> rfl }
  d _ _ _ := {
    nil := by funext x; exact x.2.2.elim
    cons := by intro a b; funext ⟨_,_,x⟩; cases x <;> rfl }
theorem gatherNat : GatherOuterNat gather.{u} where
  cons p q c := by funext ⟨x,_⟩; cases x <;> rfl
def unitCompat : UnitCompat gather.{u} PUnit where
  ρ _ a := (a,⟨⟩)
  natural _ := rfl
  nil := by funext x; exact x.elim
  cons _ _ := by funext x; cases x <;> rfl
abbrev fibre {n m : Nat} (f : Fin n → Fin m) (A : Fin n → Type u) (j : Fin m) :=
  (i : {i : Fin n // f i = j}) × A i.val
def push : Push coeff.{u} where
  obj := fibre
  map := fun {_ _} _ {_ _} p _ z => ⟨z.1,p _ z.2⟩
  map_id _ _ := rfl
  map_seq := by intros; rfl
  single := fun {_} _ j x => ⟨⟨j,rfl⟩,x⟩
  split := fun {_ _ _} _ g _ _ z =>
    ⟨⟨z.2.1.val,(congrArg g z.2.1.property).trans z.1.property⟩,z.2.2⟩
  single_nat _ := rfl
  split_nat := by intros; rfl
  left_unit _ _ := rfl
  right_unit _ _ := rfl
  pent _ _ _ _ := rfl

/-- Every coefficient of the canonical sum is recoverable at its literal
address, not just as an untagged union. Type equality to a right-fold sum
is neither needed nor assumed. -/
def lookup {X : Type w} {A : X → Type u} : (xs : List X) → fold sum PEmpty A xs → (x : X) × A x
  | [], v => v.elim
  | x::_, .inl a => ⟨x,a⟩
  | _::xs, .inr t => lookup xs t

/-- Two singleton coefficient labels are equal, but tags 0 and 1 remain
observable after native aggregation. -/
def repX : Fin 2 → Type := fun _ => Unit
def repF : Fin 2 → Fin 1 := fun _ => 0
def choose (i : Fin 2) : Hom push (⟨2, repX⟩ : Family Type) (⟨1, fun _ => Unit⟩ : Family Type) :=
  ⟨repF, fun j _ => ⟨⟨i,Subsingleton.elim _ j⟩,()⟩⟩
theorem same_carrier : (choose 0).addr = (choose 1).addr := rfl
theorem different_address : choose 0 ≠ choose 1 := by
  intro h
  have h' := congrArg (fun f : Hom push (⟨2,repX⟩ : Family Type) (⟨1,fun _ => Unit⟩ : Family Type) =>
    ((f.cell 0) ()).1.val) h
  exact (by decide : (0:Fin 2) ≠ 1) h'
end ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
