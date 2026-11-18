import CoreBridge
import Structure

namespace ByzantineAssembly
open ByzantineControlIntegration
variable {I W F Mem Obs Cmd : Type}
abbrev State := Boundary I W (fun _ => Mem) (fun _ => Obs)
abbrev Choice := I × (Mem × Option Obs) → Cmd × Mem

noncomputable def structural
    (K : CausalKernel I W F (fun _ => Mem) (fun _ => Obs) (fun _ => Cmd))
    (G : F → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) →
      (I → Option Cmd) → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) → Prop) :
    ByzantineStructure.Kernel I F (State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs))
      (Mem × Option Obs) (Cmd × Mem) where
  view i s := (s.memory i,s.seen i)
  compliant := K.correct
  next := (boundaryModel K).next
  edgeGood f s a t := G f s (issuedMask K f s a) t

def programs (a : Choice (I:=I) (Mem:=Mem) (Obs:=Obs) (Cmd:=Cmd))
    (fallback : I → Cmd) : LocalProgram I (fun _ => Mem) (fun _ => Obs) (fun _ => Cmd) where
  output i m o := (a (i,(m,some o))).1
  update i m o := (a (i,(m,some o))).2
  fallback := fallback

def chosen (a : Choice (I:=I) (Mem:=Mem) (Obs:=Obs) (Cmd:=Cmd))
    (s : State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs)) : I → Cmd × Mem :=
  fun i => a (i,(s.memory i,s.seen i))

theorem chosen_masks
    (K : CausalKernel I W F (fun _ => Mem) (fun _ => Obs) (fun _ => Cmd))
    (a : Choice (I:=I) (Mem:=Mem) (Obs:=Obs) (Cmd:=Cmd))
    (fallback : I → Cmd) (f : F) (s : State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs)) :
    issuedMask K f s (chosen a s) = issuedMask K f s (evalProfile (programs a fallback) s) ∧
    memoryMask K f s (chosen a s) = memoryMask K f s (evalProfile (programs a fallback) s) := by
  classical
  constructor <;> funext i <;> by_cases hc : K.correct f i
  · cases ho : s.seen i <;> simp [issuedMask,hc,ho,chosen,evalProfile,programPolicy,programs]
  · simp [issuedMask,hc]
  · cases ho : s.seen i <;> simp [memoryMask,hc,ho,chosen,evalProfile,programPolicy,programs]
  · simp [memoryMask,hc]

theorem joined_source_step
    (K : CausalKernel I W F (fun _ => Mem) (fun _ => Obs) (fun _ => Cmd))
    (G : F → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) →
      (I → Option Cmd) → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) → Prop)
    (Q : F → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) → Prop)
    (a : Choice (I:=I) (Mem:=Mem) (Obs:=Obs) (Cmd:=Cmd))
    (joined : ByzantineStructure.Joint (structural K G) Q a)
    (fallback : I → Cmd) (f : F) (s t : State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs))
    (hq : Q f s) (step : SourceRound K (programs a fallback) f s t) :
    G f s (issuedMask K f s (evalProfile (programs a fallback) s)) t ∧ Q f t := by
  have hm := chosen_masks K a fallback f s
  have hn : (structural K G).next f s (chosen a s) t := by
    change K.effects f s.world s.seen (issuedMask K f s (chosen a s)) t.world ∧
      t.memory = memoryMask K f s (chosen a s) ∧ K.observations f t.world t.seen
    rw [hm.1,hm.2]
    exact step
  have hg := (joined f s hq).2 (chosen a s) t (fun _ _ => rfl) hn
  change G f s (issuedMask K f s (chosen a s)) t ∧ Q f t at hg
  rwa [hm.1] at hg

theorem joined_source_nonblocking
    (K : CausalKernel I W F (fun _ => Mem) (fun _ => Obs) (fun _ => Cmd))
    (G : F → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) →
      (I → Option Cmd) → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) → Prop)
    (Q : F → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) → Prop)
    (a : Choice (I:=I) (Mem:=Mem) (Obs:=Obs) (Cmd:=Cmd))
    (joined : ByzantineStructure.Joint (structural K G) Q a)
    (fallback : I → Cmd) (f : F) (s : State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs))
    (hq : Q f s) : ∃ t, SourceRound K (programs a fallback) f s t := by
  obtain ⟨t,ht⟩ := (joined f s hq).1 (chosen a s) (fun _ _ => rfl)
  have hm := chosen_masks K a fallback f s
  refine ⟨t,?_⟩
  change K.effects f s.world s.seen (issuedMask K f s (chosen a s)) t.world ∧
    t.memory = memoryMask K f s (chosen a s) ∧ K.observations f t.world t.seen at ht
  change K.effects f s.world s.seen (issuedMask K f s (evalProfile (programs a fallback) s)) t.world ∧
    t.memory = memoryMask K f s (evalProfile (programs a fallback) s) ∧ K.observations f t.world t.seen
  rwa [hm.1,hm.2] at ht

theorem joined_source_run
    (K : CausalKernel I W F (fun _ => Mem) (fun _ => Obs) (fun _ => Cmd))
    (G : F → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) →
      (I → Option Cmd) → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) → Prop)
    (Q : F → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs) → Prop)
    (a : Choice (I:=I) (Mem:=Mem) (Obs:=Obs) (Cmd:=Cmd))
    (joined : ByzantineStructure.Joint (structural K G) Q a)
    (fallback : I → Cmd) (f : F)
    (r : Nat → State (I:=I) (W:=W) (Mem:=Mem) (Obs:=Obs))
    (initial : Q f (r 0))
    (run : ByzantineControlProgram.IsRun (boundaryModel K)
      (programPolicy (programs a fallback)) f r) :
    ∀ t, Q f (r t) ∧
      G f (r t) (issuedMask K f (r t) (evalProfile (programs a fallback) (r t))) (r (t+1)) := by
  have steps := ((core_run_iff_source_rounds K (programs a fallback) f r).mp run).2
  have invariant : ∀ t, Q f (r t) := by
    intro t
    induction t with
    | zero => exact initial
    | succ t ih => exact (joined_source_step K G Q a joined fallback f (r t) (r (t+1)) ih (steps t)).2
  intro t
  exact ⟨invariant t,(joined_source_step K G Q a joined fallback f (r t) (r (t+1)) (invariant t) (steps t)).1⟩

end ByzantineAssembly
#print axioms ByzantineAssembly.chosen_masks
#print axioms ByzantineAssembly.joined_source_step
#print axioms ByzantineAssembly.joined_source_nonblocking
#print axioms ByzantineAssembly.joined_source_run
