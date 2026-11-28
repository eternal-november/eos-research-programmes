import Mathlib
namespace TwoCut

variable {W E L R A : Type}

def Realizable (early : W → E) (late : R → W → L)
    (reachable : W → R → Prop) (good : W → R → A → Prop) : Prop :=
  ∃ send : E → R, ∃ act : R → L → A, ∀ w,
    reachable w (send (early w)) ∧
    good w (send (early w)) (act (send (early w)) (late (send (early w)) w))

def Cut (early : W → E) (late : R → W → L)
    (reachable : W → R → Prop) (good : W → R → A → Prop) : Prop :=
  ∃ send : E → R, (∀ w, reachable w (send (early w))) ∧
    ∀ r v, ∃ a, ∀ w, send (early w) = r → late r w = v → good w r a

theorem feasible_iff_cut (early : W → E) (late : R → W → L)
    (reach : W → R → Prop) (good : W → R → A → Prop) :
    Realizable early late reach good ↔ Cut early late reach good := by
  classical
  constructor
  · rintro ⟨send, act, works⟩
    refine ⟨send, fun w => (works w).1, ?_⟩
    intro r v
    refine ⟨act r v, ?_⟩
    intro w hr hv
    simpa [hr, hv] using (works w).2
  · rintro ⟨send, ok, choices⟩
    choose act lawful using choices
    exact ⟨send, act, fun w => ⟨ok w, lawful _ _ w rfl rfl⟩⟩

theorem separate_sender_cells_do_not_suffice :
    (∀ world : Bool, ∃ actor : Bool, actor = world) ∧
    ¬ Realizable (id : Bool → Bool) (fun (_ : Unit) (_ : Bool) => ())
      (fun _ _ => True) (fun world (_ : Unit) (actor : Bool) => actor = world) := by
  refine ⟨fun w => ⟨w,rfl⟩, ?_⟩
  rintro ⟨send, act, ok⟩
  have h0 : act (send false) () = false := (ok false).2
  have h1 : act (send true) () = true := (ok true).2
  have hs : send false = send true := Subsingleton.elim _ _
  rw [hs,h1] at h0
  contradiction

theorem route_can_carry_a_distinction :
    Realizable (id : Bool → Bool) (fun (_ : Bool) (_ : Bool) => ())
      (fun _ _ => True) (fun world (_ : Bool) (actor : Bool) => actor = world) :=
  ⟨id,fun r _ => r,fun _ => ⟨trivial,rfl⟩⟩

end TwoCut
