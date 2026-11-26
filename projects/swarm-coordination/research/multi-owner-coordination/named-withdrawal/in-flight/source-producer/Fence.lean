import Lean

namespace LiveEffectFence

universe u
variable {Token : Type u}

def Clear (claim : Token → Prop) (tape : List (Token → Prop)) : Prop :=
  ∀ op, op ∈ tape → ∀ resource, claim resource → ¬op resource

theorem advance {claim : Token → Prop} {done : Token → Prop}
    {suffix : List (Token → Prop)} (h : Clear claim (done :: suffix)) :
    Clear claim suffix := by
  intro op occurs r reserved
  exact h op (List.mem_cons_of_mem _ occurs) r reserved

theorem concurrent_replacement {claim : Token → Prop}
    {current replacement : List (Token → Prop)} (h : Clear claim current)
    (install : Bool) (checked : install = true → Clear claim replacement) :
    Clear claim (if install then replacement else current) := by
  cases install
  · exact h
  · exact checked rfl

theorem same_old_snapshot_cannot_acquire
    {claim : Token → Prop} {replacement : List (Token → Prop)}
    {op : Token → Prop} {r : Token} (o : op ∈ replacement)
    (held : claim r) (touches : op r) : ¬Clear claim replacement := by
  intro h
  exact h op o r held touches

#print axioms advance
#print axioms concurrent_replacement
#print axioms same_old_snapshot_cannot_acquire

end LiveEffectFence
