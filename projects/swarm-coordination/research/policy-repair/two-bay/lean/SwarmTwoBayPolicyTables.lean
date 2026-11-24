import Mathlib.Data.Set.Basic

/-! Two-bay pilot, with one observation class for A and arbitrary local modes for B. -/
namespace SwarmTwoBay

variable {Mode : Type*}

/-- The passive guide preserves bay order when the mask is false and reverses it
when the mask is true. A still chooses only one Boolean. -/
def actualBay (g : Mode → Bool) (a : Bool) (m : Mode) : Bool :=
  if g m then !a else a

def complement (g : Mode → Bool) : Mode → Bool := fun m => !g m

def admitted (g : Mode → Bool) (a : Bool) (b : Mode → Bool) : Prop :=
  ∀ m, actualBay g a m ≠ b m

def compatible (g : Mode → Bool) : Set (Mode → Bool) :=
  { b | ∃ a : Bool, admitted g a b }

theorem complement_complement (g : Mode → Bool) : complement (complement g) = g := by
  funext m
  simp [complement]

theorem distinct_bay (a t b : Bool) :
    (if t then !a else a) ≠ b ↔ b = (if a then t else !t) := by
  cases a <;> cases t <;> cases b <;> decide

theorem admitted_iff (g : Mode → Bool) (a : Bool) (b : Mode → Bool) :
    admitted g a b ↔ b = (if a then g else complement g) := by
  constructor
  · intro h
    funext m
    have hm := (distinct_bay a (g m) (b m)).mp (h m)
    cases a <;> exact hm
  · intro h m
    apply (distinct_bay a (g m) (b m)).mpr
    rw [h]
    cases a <;> rfl

theorem compatible_iff (g b : Mode → Bool) :
    b ∈ compatible g ↔ b = g ∨ b = complement g := by
  constructor
  · rintro ⟨a, h⟩
    have he := (admitted_iff g a b).mp h
    cases a
    · exact Or.inr he
    · exact Or.inl he
  · rintro (h | h)
    · exact ⟨true, (admitted_iff g true b).mpr h⟩
    · exact ⟨false, (admitted_iff g false b).mpr h⟩

/-- Every requested bit at a single coordinate extends to a compatible table. -/
theorem coordinate_surjective (g : Mode → Bool) (m : Mode) (v : Bool) :
    ∃ b ∈ compatible g, b m = v := by
  by_cases h : g m = v
  · exact ⟨g, (compatible_iff g g).mpr (Or.inl rfl), h⟩
  · refine ⟨complement g, (compatible_iff g _).mpr (Or.inr rfl), ?_⟩
    cases hg : g m <;> cases v <;> simp_all [complement]

theorem compatible_complement (g : Mode → Bool) :
    compatible (complement g) = compatible g := by
  ext b
  simp only [compatible_iff, complement_complement, or_comm]

theorem compatible_eq_iff (g h : Mode → Bool) :
    compatible g = compatible h ↔ g = h ∨ g = complement h := by
  constructor
  · intro e
    have hg : g ∈ compatible g := (compatible_iff g g).mpr (Or.inl rfl)
    rw [e] at hg
    exact (compatible_iff h g).mp hg
  · rintro (rfl | rfl)
    · rfl
    · exact compatible_complement h

theorem compatible_eq_of_common (g h b : Mode → Bool)
    (hg : b ∈ compatible g) (hh : b ∈ compatible h) :
    compatible g = compatible h := by
  have eqTo (f : Mode → Bool) (hf : b ∈ compatible f) : compatible b = compatible f :=
    (compatible_eq_iff b f).mpr ((compatible_iff f b).mp hf)
  exact (eqTo g hg).symm.trans (eqTo h hh)

/-- Single-coordinate extension is compatible in both layouts, yet the fixed
old table is compatible with the base layout and incompatible with the flip. -/
theorem twoMode_witness :
    let baseMask : Bool → Bool := fun _ => false
    let flipMask : Bool → Bool := id
    let oldTable : Bool → Bool := fun _ => false
    admitted baseMask true oldTable ∧ oldTable ∉ compatible flipMask ∧
      (∀ m v : Bool, ∃ b ∈ compatible flipMask, b m = v) := by
  refine ⟨(admitted_iff _ true _).mpr rfl, ?_, coordinate_surjective id⟩
  intro h
  rcases (compatible_iff _ _).mp h with e | e
  · have htrue := congrFun e true
    cases htrue
  · have hfalse := congrFun e false
    cases hfalse

#print axioms admitted_iff
#print axioms compatible_iff
#print axioms coordinate_surjective
#print axioms compatible_eq_iff
#print axioms compatible_eq_of_common
#print axioms twoMode_witness
end SwarmTwoBay
