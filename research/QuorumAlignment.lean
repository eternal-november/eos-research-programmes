import Control

/-! Operational alignment for the Q3 certificate-exclusion specialization.
This is a signing/verification theorem, not a consensus or termination theorem. -/
namespace ByzantineQuorumAlignment
open ByzantineControlResearch

abbrev History (I V : Type) := List (I × V)
def Seen (h : History I V) (i : I) (v : V) : Prop := (i,v) ∈ h
def Exclusive (B : I → Prop) (h : History I V) : Prop :=
  ∀ i, ¬ B i → ∀ v w, Seen h i v → Seen h i w → v = w

/- A scheduled request at a correct signer checks only its own signed history.
B chooses which implementation is followed; it is not a correct policy input.
Rejected requests leave the signing facts unchanged; the enclosing clock advances. -/
noncomputable def issue (B : I → Prop) (h : History I V) (i : I) (v : V) : History I V := by
  classical
  exact if B i ∨ (∀ w, Seen h i w → w = v) then (i,v)::h else h

theorem empty_exclusive (B : I → Prop) : Exclusive B ([] : History I V) := by
  intro i hi v w hv
  simp [Seen] at hv

theorem issue_preserves (B : I → Prop) (h : History I V) (i : I) (v : V)
    (good : Exclusive B h) : Exclusive B (issue B h i v) := by
  classical
  unfold issue
  split
  · rename_i allowed
    intro j hj a b ha hb
    simp only [Seen, List.mem_cons, Prod.mk.injEq] at ha hb
    rcases ha with ⟨hji,hav⟩ | ha
    · subst j
      subst a
      rcases hb with ⟨_,hbv⟩ | hb
      · exact hbv.symm
      · rcases allowed with bad | guard
        · exact False.elim (hj bad)
        · exact (guard b hb).symm
    · rcases hb with ⟨hji,hbv⟩ | hb
      · subst j
        subst b
        rcases allowed with bad | guard
        · exact False.elim (hj bad)
        · exact guard a ha
      · exact good j hj a b ha hb
  · exact good

theorem generated_exclusive (B : I → Prop) (events : Nat → I × V)
    (hist : Nat → History I V) (initial : hist 0 = [])
    (next : ∀ t, hist (t+1) = issue B (hist t) (events t).1 (events t).2) :
    ∀ t, Exclusive B (hist t) := by
  intro t
  induction t with
  | zero => rw [initial]; exact empty_exclusive B
  | succ t ih => rw [next]; exact issue_preserves B (hist t) _ _ ih

def Certificate (supports : (I → Prop) → Prop) (h : History I V) (v : V) : Prop :=
  ∃ Q, supports Q ∧ ∀ i, Q i → Seen h i v

theorem operational_certificate_exclusion (F supports : (I → Prop) → Prop)
    (B : I → Prop) (actual : F B)
    (intersect : ∀ Q R, supports Q → supports R → Hits F (fun i => Q i ∧ R i))
    (h : History I V) (guard : Exclusive B h) (v w : V)
    (cv : Certificate supports h v) (cw : Certificate supports h w) : v = w := by
  obtain ⟨Q,hQ,sQ⟩ := cv
  obtain ⟨R,hR,sR⟩ := cw
  obtain ⟨i,⟨hiQ,hiR⟩,honest⟩ := intersect Q R hQ hR B actual
  exact guard i honest v w (sQ i hiQ) (sR i hiR)

theorem operational_certificate_available (F supports : (I → Prop) → Prop)
    (B : I → Prop) (actual : F B) (available : Available F supports)
    (h : History I V) (v : V) (delivered : ∀ i, ¬ B i → Seen h i v) :
    Certificate supports h v := by
  obtain ⟨Q,hQ,outside⟩ := available B actual
  exact ⟨Q,hQ,fun i hi => delivered i (outside i hi)⟩


theorem issue_seen_preserved (B : I → Prop) (h : History I V) (i : I) (v : V)
    (j : I) (w : V) (old : Seen h j w) : Seen (issue B h i v) j w := by
  classical
  unfold issue
  split
  · exact List.mem_cons_of_mem _ old
  · exact old

def ReceiptSound (issued received : History I V) : Prop :=
  ∀ i v, Seen received i v → Seen issued i v

theorem receipt_certificate_issued (supports : (I → Prop) → Prop)
    (issued received : History I V) (sound : ReceiptSound issued received)
    (v : V) (cert : Certificate supports received v) :
    Certificate supports issued v := by
  obtain ⟨Q,hQ,shares⟩ := cert
  exact ⟨Q,hQ,fun i hi => sound i v (shares i hi)⟩

theorem received_certificate_exclusion (F supports : (I → Prop) → Prop)
    (B : I → Prop) (actual : F B)
    (intersect : ∀ Q R, supports Q → supports R → Hits F (fun i => Q i ∧ R i))
    (issued first second : History I V) (guard : Exclusive B issued)
    (firstSound : ReceiptSound issued first) (secondSound : ReceiptSound issued second)
    (v w : V) (cv : Certificate supports first v) (cw : Certificate supports second w) : v = w := by
  exact operational_certificate_exclusion F supports B actual intersect issued guard v w
    (receipt_certificate_issued supports issued first firstSound v cv)
    (receipt_certificate_issued supports issued second secondSound w cw)

#print axioms issue_seen_preserved
#print axioms receipt_certificate_issued
#print axioms received_certificate_exclusion

#print axioms empty_exclusive
#print axioms issue_preserves
#print axioms generated_exclusive
#print axioms operational_certificate_exclusion
#print axioms operational_certificate_available
end ByzantineQuorumAlignment
