import Mathlib
namespace TransitWindow

theorem offset_forbids (s o d l u : Int) (hd : 0 < d) (hlu : l < u) :
    (∃ t : Int, s+o ≤ t ∧ t < s+o+d ∧ l ≤ t ∧ t < u)
     ↔ (l-o-d+1 ≤ s ∧ s < u-o) := by
  constructor
  · rintro ⟨t,a,b,c,e⟩
    omega
  · intro h
    exact ⟨max (s+o) l, by omega, by omega, by omega, by omega⟩

theorem box_offsets (s lo hi d l u : Int)
    (ho : lo ≤ hi) (hd : 0 < d) (hlu : l < u) :
    (∃ o : Int, lo ≤ o ∧ o ≤ hi ∧
      (∃ t : Int, s+o ≤ t ∧ t < s+o+d ∧ l ≤ t ∧ t < u))
      ↔ l-hi-d+1 ≤ s ∧ s < u-lo := by
  constructor
  · rintro ⟨o,a,b,t,c,e,f,g⟩
    omega
  · intro H
    let o := max lo (l+1-s-d)
    have ho1 : lo ≤ o := by omega
    have ho2 : o ≤ hi := by omega
    refine ⟨o,ho1,ho2,?_⟩
    apply (offset_forbids s o d l u hd hlu).mpr
    omega

end TransitWindow
#print axioms TransitWindow.offset_forbids
#print axioms TransitWindow.box_offsets
