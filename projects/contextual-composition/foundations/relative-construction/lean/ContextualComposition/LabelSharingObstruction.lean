module
public import Init

/-! The two fair-bit fixtures for sharing within the current list in §4 of the harder structural tests. All sample lists below enumerate equiprobable atoms. -/

@[expose] public section
namespace ContextualComposition.LabelSharingObstruction

def bits : List Bool := [false, true]

/-- Allocate one fair bit per distinct label of a two-position list. -/
def sharePair {L : Type} [DecidableEq L] (x y : L) : List (Bool × Bool) :=
  if x = y then bits.map (fun b => (b, b)) else
    bits.flatMap (fun a => bits.map (fun b => (a, b)))

/-- Applying the recipe separately to two singleton lists starts each with its own draw. -/
def twoSingletons : List (Bool × Bool) :=
  bits.flatMap (fun a => bits.map (fun b => (a, b)))

def disagree (xs : List (Bool × Bool)) := xs.countP (fun p => p.1 != p.2)

/-- A noninjective reindexing preserves the two output positions and their bits. -/
theorem merging_labels :
    let v : Bool → Unit := fun _ => ()
    let before := sharePair false true
    let after := sharePair (v false) (v true)
    (disagree before, before.length) = (2, 4) ∧ (disagree after, after.length) = (0, 2) := by
  decide

/-- For [[x],[x]], crossing the inner lists separately and flattening their outputs gives a different law from flattening the inputs first. -/
theorem flattening_singletons :
    (disagree twoSingletons, twoSingletons.length) = (2, 4) ∧
    (disagree (sharePair () ()), (sharePair () ()).length) = (0, 2) := by
  decide

end ContextualComposition.LabelSharingObstruction
