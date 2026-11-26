import Lean

namespace InFlightWithdrawal

universe u v w
variable {World : Type u} {X : Type v} {Y : Type w}

def PermitEarly (admitted needsY : World → Prop) : Prop :=
  ∀ world, admitted world → ¬ needsY world

theorem unknown_must_hold {admitted needsY : World → Prop} {w : World}
    (stillPossible : admitted w) (touchesY : needsY w) :
    ¬ PermitEarly admitted needsY := by
  intro attempt
  exact attempt w stillPossible touchesY

theorem scope_restrict {current later needsY : World → Prop}
    (h : PermitEarly current needsY) (covered : ∀ w, later w → current w) :
    PermitEarly later needsY :=
  fun w a => h w (covered w a)

theorem selected_disjoint_updates (old : X → X) (new : Y → Y) (x : X) (y : Y) :
    let oldStep : X × Y → X × Y := fun p => (old p.1,p.2)
    let newStep : X × Y → X × Y := fun p => (p.1,new p.2)
    newStep (oldStep (x,y)) = oldStep (newStep (x,y)) := rfl

#print axioms unknown_must_hold
#print axioms scope_restrict
#print axioms selected_disjoint_updates

end InFlightWithdrawal
