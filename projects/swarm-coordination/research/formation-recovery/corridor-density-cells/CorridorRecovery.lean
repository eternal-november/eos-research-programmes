import Mathlib
namespace CorridorRecovery

theorem radiusNecessary {x0 x1 y0 y1 k0 k1 r c : ℚ}
    (hi : y0 ≤ x0+k0*r) (lo : x1-k1*r ≤ y1) (span : y1-y0 ≤ c) :
    x1-x0-c ≤ (k0+k1)*r := by linarith

theorem shortestPotential {base left middle w : ℚ}
    (next : middle ≤ base+w) (asked : base = left) :
    middle-left ≤ w := by linarith

theorem selectUpper {u0 d0 d1 c yj : ℚ}
    (edge : d1 ≤ d0+c) (pot : yj ≤ u0+d1) :
    yj ≤ (u0+d0)+c := by linarith

theorem affineHard {a0 a1 b0 b1 c z : ℚ}
    (start : a1-a0≤c) (finish : b1-b0≤c) (h0 : 0≤z) (h1 : z≤1) :
    ((1-z)*a1+z*b1)-((1-z)*a0+z*b0)≤c := by
  have p := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr start)
  have q := mul_nonneg h0 (sub_nonneg.mpr finish)
  nlinarith

theorem sharedTravel {left right span δ : ℚ} {n : Nat}
    (h1 : -span ≤ left) (h2 : right ≤ span) (h3 : n*δ ≤ right-left) :
    n*δ ≤ 2*span := by linarith

theorem areaLowerTime {t a distance : ℚ} (h : distance ≤ a*t*t/4)
    (late : a*t*t < 4*distance) : False := by linarith

theorem foldTwoCycles {b c : ℚ} (h : b+c<0) :
    ¬∃ x y : ℚ, y-x≤b ∧ x-y≤c := by
  rintro ⟨x,y,xy,yx⟩
  linarith


theorem feasibleClosedBox {ι : Type} [Fintype ι] [Nonempty ι]
    (d : ι → ι → ℝ) (l u : ι → ℝ)
    (diagonal : ∀ i, d i i = 0)
    (triangle : ∀ i j k, d i k ≤ d i j + d j k) :
    (∀ i j, l j ≤ u i + d i j) ↔
    ∃ y : ι → ℝ, (∀ i, l i ≤ y i ∧ y i ≤ u i) ∧
      ∀ i j, y j - y i ≤ d i j := by
  constructor
  · intro h
    classical
    have attains (j : ι) : ∃ i, ∀ q, u i + d i j ≤ u q + d q j := by
      obtain ⟨i, _, hmin⟩ := Finset.exists_min_image
        (Finset.univ : Finset ι) (fun i => u i + d i j) Finset.univ_nonempty
      exact ⟨i, fun q => hmin q (Finset.mem_univ q)⟩
    choose f hmin using attains
    refine ⟨fun i => u (f i) + d (f i) i, ?_, ?_⟩
    · intro i
      refine ⟨h (f i) i, ?_⟩
      simpa [diagonal i] using hmin i i
    · intro i j
      have hm := hmin j (f i)
      have ht := triangle (f i) i j
      linarith
  · rintro ⟨y, box, diff⟩ i j
    have lo := (box j).1
    have hi := (box i).2
    have hd := diff i j
    linarith

#print axioms feasibleClosedBox
#print axioms radiusNecessary
#print axioms shortestPotential
#print axioms selectUpper
#print axioms affineHard
#print axioms sharedTravel
#print axioms areaLowerTime
#print axioms foldTwoCycles
end CorridorRecovery
