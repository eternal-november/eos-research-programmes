import RecurrentSupport

/-! The two actually exercised orders at one candidate normal-seat strobe.
    This is a projection of a fully funded, eligible zero stop with one paid
    permanent physical takeover. Later cuts query this same historical duty. -/
namespace SeatSupport
open ContextualJobs RecurrentSupport

inductive Query where | heldPole | missedSeat deriving DecidableEq
def site := 100
def physical (takeoverFirst : Bool) := if takeoverFirst then 1 else 2
def capture (takeoverFirst : Bool) := if takeoverFirst then 2 else 1
def time (i : Nat) := if i ≤ 1 then i else i-1

def clock : BudgetClock Nat where
  within i j c := i ≤ j ∧ time j ≤ time i + c
  now i := ⟨Nat.le_refl _,by omega⟩
  append := by rintro i j k a b ⟨ij,tij⟩ ⟨jk,tjk⟩; exact ⟨Nat.le_trans ij jk,by omega⟩

def policy : Policy where
  Role := Unit
  View := fun _ => Unit
  Command := fun _ => Unit
  prescribe := fun _ _ => ()

def operations (first : Bool) : Operations policy where
  Id := Unit
  start := fun _ => 0
  Cursor := fun _ j => PLift (j = 0 ∨ j = capture first)
  entry := fun _ => ⟨Or.inl rfl⟩
  Done := fun _ j => PLift (first=false ∧ j=capture first)
  Stop := fun _ j => PLift (first=true ∧ j=capture first)
  actor := fun _ => ()
  view := fun _ _ => ()
  observed := fun _ i _ => if i=0 then .advance (capture first) 1
    else if first then .stopped i 0 else .terminal
  follows := fun _ {i j} _ _ => (i=0 ∧ j=capture first) ∨ (i=j ∧ j=capture first)

def world (first : Bool) : World where
  policy := policy
  ops := operations first
  Query := Query
  Token := Nat
  clock := clock
  forward := fun _ _ _ c => c.1
  demand := fun q => match q with | .heldPole => none | .missedSeat => some ()
  bad := fun q n => PLift (match q with
    | .heldPole => physical first ≤ n
    | .missedSeat => first=true ∧ capture first ≤ n)
  cap := fun q n => PLift (q = .heldPole ∧ physical first ≤ n)
  seed := fun _ n _ => PLift (n=physical first)
  keeps := fun _ _ _ _ => True
  initial := by
    intro q x
    have h := x.down.2
    cases first <;> simp [physical] at h
  predecessor := by
    intro q i x
    by_cases born : i+1=physical first
    · exact .source ⟨born⟩
    · have h := x.down.2
      exact .parent ⟨x.down.1,by omega⟩ True.intro
  owner := fun _ => site
  repairId := fun _ => none
  covered := fun t n _ => t=site ∧ physical first ≤ n
  stableCover := by
    intro t n _ stable
    by_cases h : t=site ∧ physical first ≤ n
    · exact h
    · exact False.elim (stable h)
  affects := fun t _ => t=site
  seedFoot := fun _ => rfl

def counted (first : Bool) (n : Nat) : Job (world first) n () where
  rank := fun p => if p.1=0 then 1 else 0
  remaining := fun p => if p.1=0 then 1 else 0
  reads := fun _ _ => ⟨0,Fin.elim0,Fin.elim0,(fun k => nomatch k),(fun k => nomatch k)⟩
  step := by
    intro p spent _ _ _
    let j : Position (world first) () := ⟨capture first,⟨Or.inr rfl⟩⟩
    have pos : 0 < capture first := by cases first <;> decide
    by_cases init : p.1=0
    · have duration : clock.within p.1 (capture first) 1 := by
        rw [init]; cases first <;> simp [clock,capture,time]
      refine ⟨.advance j 1 duration ?_ ?_,?_⟩
      · simp [j,init,Nat.ne_of_gt pos]
      · simp [j,init,Nat.ne_of_gt pos]
      · exact ⟨by simp [form,world,Operations.atCut,operations,init,j],
               Or.inl ⟨init,rfl⟩⟩
    · have stop : p.1=capture first := p.2.down.resolve_left init
      by_cases order : first=true
      · refine ⟨.interrupted p 0 (clock.now _) (Nat.zero_le _) ⟨order,stop⟩,?_⟩
        exact ⟨by simp [form,world,Operations.atCut,operations,init,order],Or.inr ⟨rfl,stop⟩⟩
      · have no : first=false := by cases first <;> simp_all
        exact ⟨.terminal ⟨no,stop⟩,
          by simp [form,world,Operations.atCut,operations,init,no,cursorFollows]⟩

def adapter (first : Bool) : Adapter (world first) where
  active := by
    intro q n h bad
    cases q with
    | heldPole => exact ⟨rfl,bad.down⟩
    | missedSeat => cases h
  missed := by
    intro q n op h bad
    cases q with
    | heldPole => cases h
    | missedSeat =>
      cases op
      have order := bad.down.1
      have due := bad.down.2
      refine ⟨counted first n,?_,?_,?_⟩
      · intro j c _ _ stopped
        exact Nat.le_trans (Nat.le_of_eq stopped.down.2) due
      · intro j c _ _ done
        have contrary := done.down.1
        simp [order] at contrary
      · intro j _ stopped
        have before : physical first < n := by
          simp [capture,order] at due
          simp [physical,order]
          omega
        exact .inr ⟨Query.heldPole,physical first,before,⟨Nat.le_refl _⟩,
          fun _ atPole reaches => ⟨⟨atPole.1,Nat.le_of_lt before⟩,reaches⟩⟩
  repair := by
    intro q n r a seed byCut excluded
    exact False.elim (excluded ⟨rfl,Nat.le_trans (Nat.le_of_eq seed.down.symm) byCut⟩)

def family : Family := ⟨Bool,policy,world,fun _ => rfl,adapter⟩

example : (family.support true 2 Query.missedSeat ⟨rfl,by decide⟩).val = site :=
  (family.support true 2 Query.missedSeat ⟨rfl,by decide⟩).property.2

#eval (show Nat from (family.support true 2 Query.missedSeat ⟨rfl,by decide⟩).val)
example (n : Nat) : (world false).bad Query.missedSeat n → False := fun bad => by cases bad.down.1

#print axioms adapter
end SeatSupport
