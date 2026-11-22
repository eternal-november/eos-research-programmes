import ContextualComposition.OppositeTypeFamilies
open ContextualComposition.OppositeTypeFamilies
namespace OppositeTypeFamiliesChecks
def two : Family := ⟨Bool,Bool,fun a => a,false⟩
def merged : Family := ⟨Unit,Bool,fun _ => (),false⟩
def select : Hom two merged := ⟨fun _ => (),fun b => b,fun _ => rfl,rfl⟩
def collapse : Hom two merged := ⟨fun _ => (),fun _ => false,fun _ => rfl,rfl⟩
theorem proxy_failure : select.f = collapse.f ∧ select ≠ collapse := by
  refine ⟨rfl,fun h => ?_⟩
  have := congrArg (fun (k : Hom two merged) => k.back true) h
  cases this
theorem selects_different_summands :
    (select.blocks () ⟨false,rfl⟩).val = false ∧
    (select.blocks () ⟨true,rfl⟩).val = true := ⟨rfl,rfl⟩

def unused : Family := ⟨Bool,Unit,fun _ => false,()⟩
def insertUnused : Hom (unit : Family.{0}) unused := ⟨fun _ => false,fun _ => ⟨⟩,fun _ => rfl,rfl⟩
theorem unused_empty (b : {a : unused.Tok // unused.atPos a = true}) : False := by cases b.property
theorem no_empty_aug (P : Family.{0}) (no : P.Pos → False) : False := no (P.atPos P.mark)
theorem unequal_draws : ∃ a : (ind fun _ : Bool => two).Tok, a false ≠ a true :=
  ⟨fun i => i, Bool.false_ne_true⟩
theorem no_draws (a : (ind fun i : Empty => nomatch i).Tok) :
    a = (ind fun i : Empty => nomatch i).mark := by funext i; cases i
-- Which continuation is used depends on the summand selected by the outer token.
def gate (x : Bool) : Hom merged merged :=
  ⟨fun _ => (),fun b => x && b,fun _ => rfl, by cases x <;> rfl⟩
theorem dependence :
    (depMap (Q := fun _ => merged) (S := fun _ => merged) select gate).back ⟨true,true⟩ = ⟨true,true⟩ ∧
    (depMap (Q := fun _ => merged) (S := fun _ => merged) select gate).back ⟨false,true⟩ = ⟨false,false⟩ := ⟨rfl,rfl⟩

-- Regression for the limit of an unused position. Nonempty coefficient at
-- an unreachable destination cannot yield a reverse function into the empty fibre.
theorem no_lift : ¬ ∃ h : Hom unit two, h.f = fun _ => false := by
  rintro ⟨h,e⟩
  have k := h.over true
  rw [e] at k
  cases k
end OppositeTypeFamiliesChecks
#print axioms OppositeTypeFamiliesChecks.proxy_failure
#print axioms OppositeTypeFamiliesChecks.selects_different_summands
#print axioms OppositeTypeFamiliesChecks.unused_empty
#print axioms OppositeTypeFamiliesChecks.no_empty_aug
#print axioms OppositeTypeFamiliesChecks.unequal_draws
#print axioms OppositeTypeFamiliesChecks.no_draws
#print axioms OppositeTypeFamiliesChecks.dependence
#print axioms OppositeTypeFamiliesChecks.no_lift
