module
public import ContextualComposition.JointOccurrenceAdmission

/-! State-indexed tree admission. Each choice of joint law supplies a system on the entire raw state overlap and actual native maps to every component system. -/

@[expose] public section
namespace ContextualComposition.JointOccurrenceSystem
open CategoryTheory CouplingPullbacks TreeOverlapAdmission JointOccurrenceAdmission
universe u
variable (F : Type u ⥤ Type u) (S : Polynomial.{u})

structure System (X : Type u) where
  witness : X → Type u
  effect : ∀ x, F.obj (witness x)
  output : ∀ x, witness x → Body S X

variable {F S} {X Y V : Type u}
structure NativeMap (A : System F S X) (B : System F S Y) (h : X → Y) where
  onWitness : ∀ x, A.witness x → B.witness (h x)
  marginal : ∀ x, push F (onWitness x) (A.effect x) = B.effect (h x)
  body : ∀ x w, map S h (A.output x w) = B.output (h x) (onWitness x w)

variable (D : Diagram V) (A : ∀ v, System F S (D.space v))

def atState (x : Raw D) : Layer S D F where
  witness v := (A v).witness (coord D v x)
  effect v := (A v).effect (coord D v x)
  body v := (A v).output (coord D v x)

abbrev Choices := ∀ x : Raw D, Joint F (witnesses (atState D A x)) (atState D A x).effect

noncomputable def jointSystem (conn : D.graph.Connected) (q : Choices D A) : System F S (Raw D) where
  witness x := Raw (witnesses (atState D A x))
  effect x := (q x).val
  output x := (canonicalStep (atState D A x) conn (q x)).body

noncomputable def componentMap (conn : D.graph.Connected) (q : Choices D A) (v : V) :
    NativeMap (jointSystem D A conn q) (A v) (coord D v) where
  onWitness x := coord (witnesses (atState D A x)) v
  marginal x := (q x).property v
  body x := (canonicalStep (atState D A x) conn (q x)).native v

theorem global_admission [Fintype V] (tree : D.graph.IsTree) (weak : WeakPullbacks F) :
    (∀ x, BoundaryAgreement (atState D A x)) ↔
    ∃ J : System F S (Raw D), Nonempty (∀ v, NativeMap J (A v) (coord D v)) := by
  constructor
  · intro h
    let q : Choices D A := fun x =>
      ((TreeOverlapAdmission.admission F (witnesses (atState D A x)) weak tree (atState D A x).effect).mp (h x)).some
    exact ⟨jointSystem D A tree.connected q,⟨componentMap D A tree.connected q⟩⟩
  · rintro ⟨J,⟨maps⟩⟩ x
    apply JointOccurrenceAdmission.necessary (atState D A x)
    exact ⟨J.witness x,J.effect x,fun v => (maps v).onWitness x,J.output x,
      fun v => (maps v).marginal x,fun v => (maps v).body x⟩

end ContextualComposition.JointOccurrenceSystem
