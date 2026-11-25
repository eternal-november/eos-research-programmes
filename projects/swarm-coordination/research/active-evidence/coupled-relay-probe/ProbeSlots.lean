import Mathlib
namespace ProbeSlots

def canSend (a b : Fin 3) (bad : Finset (Fin 3)) : Prop :=
  (a = 0 ∨ a = 1) ∧ (b = 1 ∨ b = 2) ∧ a ≠ b ∧ a ∉ bad ∧ b ∉ bad

theorem hidden_loss_no_joint_forward (a b : Fin 3) :
    ¬ (canSend a b {0} ∧ canSend a b {2}) := by
  rintro ⟨⟨ha,hb,hn,ha0,hb0⟩,⟨_,_,_,ha2,hb2⟩⟩
  simp at ha0 hb2
  have h1 := ha.resolve_left ha0
  have h2 := hb.resolve_right hb2
  exact hn (h1.trans h2.symm)

theorem powered_read_allows_each (w : Fin 2) :
    ∃ a b, canSend a b (if w = 0 then {0} else {2}) := by
  fin_cases w
  · exact ⟨1,2,by simp [canSend]⟩
  · exact ⟨0,1,by simp [canSend]⟩

theorem shared_probe_breaks_forwarding (w : Fin 2) :
    ¬ ∃ a b, canSend a b (if w = 0 then {0,1} else {1,2}) := by
  rintro ⟨a,b,ha,hb,hn,ha0,hb0⟩
  fin_cases w
  · simp at ha0
    exact ha.elim ha0.1 ha0.2
  · simp at hb0
    exact hb.elim hb0.1 hb0.2

end ProbeSlots
#print axioms ProbeSlots.hidden_loss_no_joint_forward
#print axioms ProbeSlots.powered_read_allows_each
#print axioms ProbeSlots.shared_probe_breaks_forwarding
