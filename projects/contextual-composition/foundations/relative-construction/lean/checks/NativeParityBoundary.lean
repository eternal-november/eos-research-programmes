import ContextualComposition.DependentComposition

/-! Parity-labelled maps. Objects carry a Boolean additive grading; the
tested objects are generated from the finite empty and singleton sets.
The function and independent parity label both remain observable. -/
namespace ParityFixture
open ContextualComposition.NativeFinitePush
open ContextualComposition.NativeFinitePush.DependentFibre

structure Obj where
  carrier : Type
  parity : Bool
structure Arrow (A B : Obj) where
  run : A.carrier → B.carrier
  grade : A.parity = B.parity
  tag : Bool
@[ext] theorem Arrow.ext {A B : Obj} {f g : Arrow A B} (hr : f.run = g.run) (ht : f.tag = g.tag) :
    f = g := by cases f; cases g; cases hr; cases ht; rfl

def K : Coeff Obj where
  Hom := Arrow
  id _ := ⟨id,rfl,false⟩
  seq f g := ⟨g.run ∘ f.run,f.grade.trans g.grade,xor f.tag g.tag⟩
  id_seq f := Arrow.ext rfl (by cases f.tag <;> rfl)
  seq_id f := Arrow.ext rfl (by cases f.tag <;> rfl)
  assoc f g h := Arrow.ext rfl (by cases f.tag <;> cases g.tag <;> cases h.tag <;> rfl)

abbrev sum (A B : Obj) : Obj := ⟨Sum A.carrier B.carrier,xor A.parity B.parity⟩
abbrev prod (A B : Obj) : Obj := ⟨A.carrier × B.carrier,A.parity && B.parity⟩
def S : Bi K where
  obj := sum
  map f g := ⟨Sum.map f.run g.run,(congrArg (fun d => xor d _) f.grade).trans (congrArg (xor _) g.grade),xor f.tag g.tag⟩
  map_id _ _ := Arrow.ext (funext fun x => by cases x <;> rfl) rfl
  map_seq f g h i := Arrow.ext (funext fun x => by cases x <;> rfl)
    (by change xor (xor f.tag g.tag) (xor h.tag i.tag) = xor (xor f.tag h.tag) (xor g.tag i.tag); cases f.tag <;> cases g.tag <;> cases h.tag <;> cases i.tag <;> rfl)

def T : Bi K where
  obj := prod
  map {A B C D} f g := ⟨Prod.map f.run g.run,(congrArg (fun d => d && _) f.grade).trans (congrArg (Bool.and _) g.grade),
    xor (f.tag && C.parity) (A.parity && g.tag)⟩
  map_id a c := Arrow.ext rfl (by change xor (false && c.parity) (a.parity && false) = false; cases a.parity <;> cases c.parity <;> rfl)
  map_seq {A B C D E F} f g h i := Arrow.ext rfl (by
    change xor ((xor f.tag g.tag) && D.parity) (A.parity && xor h.tag i.tag) =
      xor (xor (f.tag && D.parity) (A.parity && h.tag)) (xor (g.tag && E.parity) (B.parity && i.tag))
    rw [← f.grade, ← h.grade]
    cases A.parity <;> cases D.parity <;> cases f.tag <;> cases g.tag <;> cases h.tag <;> cases i.tag <;> rfl)

def zero : Obj := ⟨Empty,false⟩
def one : Obj := ⟨Unit,true⟩
def two : Obj := sum one one
def three : Obj := sum one two

def gdist (a b c : Obj) : Arrow (sum (prod a c) (prod b c)) (prod (sum a b) c) :=
  ⟨fun
    | .inl (x,z) => (.inl x,z)
    | .inr (y,z) => (.inr y,z),
   by rcases a with ⟨_,a⟩; rcases b with ⟨_,b⟩; rcases c with ⟨_,c⟩; cases a <;> cases b <;> cases c <;> rfl,false⟩

def G : Gather S T zero where
  nil _ := ⟨Empty.elim,rfl,false⟩
  cons := gdist
  nil_nat {_ _} _ :=  Arrow.ext (funext fun x => nomatch x) (by rfl)
  cons_nat a b {_ _} f := Arrow.ext (funext fun x => by cases x <;> rfl) (by
    change xor false (xor (false && _) (xor a.parity b.parity && f.tag)) =
      xor (xor (xor (false && _) (a.parity && f.tag)) (xor (false && _) (b.parity && f.tag))) false
    cases a.parity <;> cases b.parity <;> cases f.tag <;> rfl)

def L : LeftGather S T zero where
  nil a := ⟨Empty.elim,by rcases a with ⟨_,a⟩; cases a <;> rfl,false⟩
  cons a b c := ⟨fun
    | .inl (x,y) => (x,.inl y)
    | .inr (x,z) => (x,.inr z),
   by rcases a with ⟨_,a⟩; rcases b with ⟨_,b⟩; rcases c with ⟨_,c⟩; cases a <;> cases b <;> cases c <;> rfl,false⟩

def emptyMap (s : Bool) : Arrow zero two := ⟨Empty.elim,rfl,s⟩
theorem emptyMaps_distinct : emptyMap false ≠ emptyMap true := by
  intro h
  cases congrArg Arrow.tag h

/-- Three source parents coalesce into one of two targets. Every source
and target has one continuation, carrying an odd three-element coefficient. -/
abbrev carriers : Carrier :=
  ⟨3,2,fun _ => 1,fun _ => 1,fun _ => 0,fun _ _ => 0⟩
def targetV (j : Fin 2) : Obj := if j.val = 0 then one else two
def actArrow (s : Bool) : Arrow (fold S zero (fun _ : carriers.Parent 0 => one) (carriers.parents 0)) one :=
  ⟨fun _ => (),rfl,s⟩
def contArrow (j : Fin 2) (p : carriers.Parent j) :
    Arrow (fold S zero id ((carriers.children p 0).map (fun _ => three))) three := by
  have hj : j = 0 := p.property.symm
  subst j
  exact ⟨(fun | .inl x => x | .inr z => nomatch z),rfl,false⟩
def pairData (s : Bool) : PairData S zero carriers where
  V _ := one
  W _ _ := three
  V' := targetV
  W' _ _ := three
  outer j := by
    by_cases h : j = 0
    · subst j; exact actArrow s
    · have e : j = 1 := by
        have hj : j.val < 2 := j.isLt
        have hn : j.val ≠ 0 := fun e => h (Fin.ext e)
        exact Fin.ext (by change j.val = 1; omega)
      subst j; exact emptyMap s
  cont j z p := by
    have h : z = 0 := Subsingleton.elim _ _
    subst z; exact contArrow j p

theorem carrier_collapses : carriers.f ⟨0, by decide⟩ = carriers.f ⟨1, by decide⟩ ∧
    (⟨0,by decide⟩ : Fin 3) ≠ ⟨1,by decide⟩ := by decide

def totalOuter (s : Bool) : Arrow (fold S zero (fun _ : carriers.Parent 0 => one) (carriers.parents 0))
    (sum one two) :=
  K.seq (⟨Sum.inl,rfl,false⟩ : Arrow _ (sum (fold S zero (fun _ : carriers.Parent 0 => one) (carriers.parents 0)) zero)) (S.map (actArrow s) (emptyMap s))
theorem same_total : totalOuter false = totalOuter true := Arrow.ext rfl rfl
def targetAug : Arrow (sum one two) one := ⟨fun _ => (),rfl,false⟩
theorem same_aug : K.seq (totalOuter false) targetAug = K.seq (totalOuter true) targetAug :=
  congrArg (fun m => K.seq m targetAug) same_total

theorem inactive_tag (s : Bool) : ((pairData s).component G L 1 0).tag = s := by cases s <;> rfl
theorem inactive_distinct : (pairData false).component G L 1 0 ≠ (pairData true).component G L 1 0 := by
  intro h
  have e := congrArg Arrow.tag h
  rw [inactive_tag, inactive_tag] at e
  cases e
theorem inactive_followed (s : Bool) :
    (K.seq ((pairData s).component G L 1 0) (T.map (K.id two) (⟨id,rfl,true⟩ : Arrow three three))).tag = s := by
  cases s <;> rfl

def sourceAug : Arrow (fold S zero (fun _ : carriers.Parent 0 => one) (carriers.parents 0)) one :=
  ⟨fun _ => (),rfl,false⟩
theorem both_preserve_global (s : Bool) : K.seq (totalOuter s) targetAug = sourceAug := by
  cases s <;> exact Arrow.ext rfl rfl

theorem no_empty_aug (a : Arrow zero one) : False := by cases a.grade

def liftUnit (A : Obj) : Arrow (prod A one) A :=
  ⟨Prod.fst,by rcases A with ⟨_,a⟩; cases a <;> rfl,false⟩
def unitLaws : UnitCompat G one where
  ρ := liftUnit
  natural {a b} f := Arrow.ext rfl (by
    change xor (xor (f.tag && true) (a.parity && false)) false = xor false f.tag
    cases a.parity <;> cases f.tag <;> rfl)
  nil := Arrow.ext (funext fun x => nomatch x) rfl
  cons a b := Arrow.ext (funext fun x => by cases x <;> rfl) rfl

def swapSame : Arrow (sum one one) (sum one one) :=
  ⟨(fun | .inl a => .inr a | .inr a => .inl a), rfl, false⟩
theorem equal_labels_do_not_erase_addresses : swapSame ≠ K.id (sum one one) := by
  intro h
  have e := congrArg (fun a : Arrow (sum one one) (sum one one) => a.run (.inl ())) h
  cases e

theorem continuation_first_exchange (s : Bool) :
    K.seq ((pairData s).component G L 1 0) (T.map (K.id two) (⟨id,rfl,true⟩ : Arrow three three)) =
    dep G ((pairData s).fibre 1 0).V ((pairData s).fibre 1 0).J L (carriers.parents 1)
      (fun x => K.seq ((pairData s).cont 1 0 x) (⟨id,rfl,true⟩ : Arrow three three))
      (K.seq ((pairData s).outer 1) (K.id two)) :=
  (pairData s).compat G L 1 0 (K.id two) ⟨id,rfl,true⟩

end ParityFixture

#print axioms ParityFixture.both_preserve_global
#print axioms ParityFixture.carrier_collapses
#print axioms ParityFixture.inactive_distinct
#print axioms ParityFixture.inactive_followed
#print axioms ParityFixture.equal_labels_do_not_erase_addresses
#print axioms ParityFixture.no_empty_aug
#print axioms ParityFixture.unitLaws
#print axioms ParityFixture.continuation_first_exchange
