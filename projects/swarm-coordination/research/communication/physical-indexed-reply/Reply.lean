import Mathlib
set_option maxHeartbeats 60000
namespace ScopedOpticalReply

def Comp {V S C : Type} (seen : V → S → Prop)
     (bit : V → S → Bool) (f : V → C) :=
  ∀ a b s, seen a s → seen b s → f a=f b → bit a s=bit b s

theorem decoder_iff {V S C : Type} (seen : V → S → Prop)
    (bit : V → S → Bool) (f : V → C) :
    (∃ dec : S → C → Bool, ∀ a s, seen a s → dec s (f a)=bit a s) ↔
     Comp seen bit f := by
  classical
  unfold Comp
  constructor
  · intro hd a b s ha hb he
    obtain ⟨d,h⟩ := hd
    exact (h a s ha).symm.trans ((congrArg (d s) he).trans (h b s hb))
  · intro rules
    have ex (s : S) (c : C) : ∃ z : Bool, ∀ v : V, seen v s → f v = c → bit v s = z := by
      by_cases hh : ∃ v : V, seen v s ∧ f v = c
      · obtain ⟨a,ha,eq⟩ := hh
        exact ⟨bit a s, fun v hv ev => rules v a s hv ha (ev.trans eq.symm)⟩
      · exact ⟨false, fun v hv ev => False.elim (hh ⟨v,hv,ev⟩)⟩
    refine ⟨fun s c => Classical.choose (ex s c), ?_⟩
    intro v s hv
    exact (Classical.choose_spec (ex s (f v)) v hv rfl).symm

theorem ack_refines {V S T C : Type}
    (seen : V → S → T → Prop) (bit : V → S → Bool) (f : V → C)
    (h : Comp (fun v s => ∃ t, seen v s t) bit f) :
    Comp (fun (v : V) (st : S × T) => seen v st.1 st.2) (fun v st => bit v st.1) f := by
  intro a b st ha hb he
  exact h a b st.1 ⟨st.2,ha⟩ ⟨st.2,hb⟩ he

theorem byte_boundary :
    8 + (2:Nat)^1*8 = 24 ∧ 8 + (2:Nat)^0*8 < 24 := by decide

#print axioms decoder_iff
#print axioms ack_refines
#print axioms byte_boundary
end ScopedOpticalReply
