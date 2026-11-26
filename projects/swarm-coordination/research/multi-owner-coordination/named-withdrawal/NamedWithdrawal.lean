import Lean

namespace NamedWithdrawal
universe u v w
variable {Bay : Type u} {Cargo : Type v} {Query : Type w}

/-- Laws and place are consumed by an authorized named-object withdrawal.
The old occupancy bit need not identify the response. -/
def row (mem : Query → Cargo → Prop) (p : Bay → Cargo) (bay : Bay) (q : Query) :=
  mem q (p bay)
def role (mem : Query → Cargo → Prop) (c : Cargo) :=
  fun q => mem q c

theorem exact_profile (mem : Query → Cargo → Prop) (p p' : Bay → Cargo) :
    (∀ b q, row mem p b q ↔ row mem p' b q) ↔
    ∀ b, role mem (p b) = role mem (p' b) := by
  constructor
  · intro same b
    funext q
    exact propext (same b q)
  · intro same b q
    change role mem (p b) q ↔ role mem (p' b) q
    rw [same b]

theorem no_summary_after_split {Summary : Type*}
    (record : (Bay → Cargo) → Summary)
    (answer : Summary → Bay → Prop)
    (widen : Cargo → Prop) (p p' : Bay → Cargo) (bay : Bay)
    (same : record p = record p')
    (native₁ : widen (p bay)) (native₂ : ¬widen (p' bay))
    (correct : ∀ q b, answer (record q) b ↔ widen (q b)) :
    False := by
  have permitted := (correct p bay).2 native₁
  rw [same] at permitted
  exact native₂ ((correct p' bay).1 permitted)

theorem lawful_local {TrueWorld : Type*} (compatible authorized : TrueWorld → Prop)
    (w : TrueWorld) (seen : compatible w)
    (guard : ∀ v, compatible v → authorized v) : authorized w := guard w seen

#print axioms exact_profile
#print axioms no_summary_after_split
#print axioms lawful_local
end NamedWithdrawal
