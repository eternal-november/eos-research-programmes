module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Native augmented families in the finite free matrix rig

The global augmentation is a matrix with domain the tagged sum of all coefficient
bases. Source-indexed blocks are a presentation of maps *out of* the native
aggregated block. The packing equivalence is given below; no entry is forgotten.
-/

open scoped BigOperators

namespace ContextualComposition.AugmentedMatrixFubini

universe u v w
variable {R : Type v} [CommSemiring R]

noncomputable section

noncomputable local instance (priority := 10) classicalDecEq (X : Type u) : DecidableEq X := Classical.decEq X

/-- Execution-order composition in the coefficient category. -/
def mul {A B C : Type u} [Fintype B] (m : Matrix B A R) (n : Matrix C B R) :
    Matrix C A R := fun c a => ∑ b : B, n c b * m b a

/-- The actual matrix of a basis bijection. -/
def perm {A B : Type u} (e : A ≃ B) : Matrix B A R := by
  classical exact fun b a => if e a = b then 1 else 0

@[simp] theorem mul_perm_left {A B C : Type u} [Fintype B]
    (e : A ≃ B) (n : Matrix C B R) (c : C) (a : A) :
    mul (perm e) n c a = n c (e a) := by
  classical
  unfold mul perm
  rw [Fintype.sum_eq_single (e a)]
  · simp
  · intro b h
    simp [Ne.symm h]

@[simp] theorem mul_perm_right {A B C : Type u} [Fintype B]
    (m : Matrix B A R) (e : B ≃ C) (c : C) (a : A) :
    mul m (perm e) c a = m (e.symm c) a := by
  classical
  unfold mul perm
  rw [Fintype.sum_eq_single (e.symm c)]
  · simp
  · intro b h
    have : e b ≠ c := fun hb => h (e.injective (hb.trans (e.apply_symm_apply c).symm))
    simp [this]

theorem mul_assoc {A B C D : Type u} [Fintype B] [Fintype C]
    (l : Matrix B A R) (m : Matrix C B R) (n : Matrix D C R) :
    mul (mul l m) n = mul l (mul m n) := by
  classical
  funext d a
  simp only [mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ac_rfl

theorem perm_comp {A B C : Type u} [Fintype B] (e : A ≃ B) (f : B ≃ C) :
    mul (perm e) (perm f : Matrix C B R) = perm (e.trans f) := by
  funext c a
  rw [mul_perm_left]
  rfl

/-- Binary tensor of actual coefficient matrices. -/
def kron {A B C D : Type u} (m : Matrix B A R) (n : Matrix D C R) :
    Matrix (B × D) (A × C) R := fun b a => m b.1 a.1 * n b.2 a.2

/-- Finite, addressed tensor of actual coefficient matrices. -/
def tensorMatrix {E : Type u} [Fintype E] {A B : E → Type u}
    (m : ∀ i, Matrix (B i) (A i) R) : Matrix (∀ i, B i) (∀ i, A i) R :=
  fun b a => ∏ i, m i (b i) (a i)

theorem mul_kron {A B C X Y Z : Type u} [Fintype B] [Fintype Y]
    (m : Matrix B A R) (n : Matrix C B R) (r : Matrix Y X R) (s : Matrix Z Y R) :
    mul (kron m r) (kron n s) = kron (mul m n) (mul r s) := by
  classical
  funext c a
  simp only [mul, kron, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro y _
  ac_rfl

theorem mul_tensorMatrix {E : Type u} [Fintype E] {A B C : E → Type u}
    [∀ i, Fintype (B i)] (m : ∀ i, Matrix (B i) (A i) R)
    (n : ∀ i, Matrix (C i) (B i) R) :
    mul (tensorMatrix m) (tensorMatrix n) = tensorMatrix (fun i => mul (m i) (n i)) := by
  classical
  funext c a
  simp only [mul, tensorMatrix, ← Finset.prod_mul_distrib, Fintype.prod_sum]
  
theorem kron_perm {A B C D : Type u} (e : A ≃ B) (f : C ≃ D) :
    kron (perm e) (perm f) = (perm (Equiv.prodCongr e f) : Matrix (B × D) (A × C) R) := by
  classical
  funext b a
  simp only [kron, perm]
  simp only [Equiv.prodCongr_apply]
  rcases b with ⟨b₁, b₂⟩
  by_cases h₁ : e a.1 = b₁ <;> by_cases h₂ : f a.2 = b₂ <;>
    simp [h₁, h₂, Prod.map, Prod.mk.injEq]

theorem tensorMatrix_perm {E : Type u} [Fintype E] {A B : E → Type u}
    (e : ∀ i, A i ≃ B i) :
    tensorMatrix (fun i => perm (e i)) = (perm (Equiv.piCongrRight e) :
      Matrix (∀ i, B i) (∀ i, A i) R) := by
  classical
  funext b a
  simp only [tensorMatrix, perm]
  split
  · rename_i h
    have hi (i : E) : e i (a i) = b i := congrFun h i
    simp [hi]
  · rename_i h
    have hx : ∃ i, e i (a i) ≠ b i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    rcases hx with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Finite native carriers and finite free coefficients; the row is one global
augmentation, not a scalar mass per carrier. -/
structure Family (R : Type v) where
  Pos : Type u
  posFintype : Fintype Pos
  Basis : Pos → Type u
  basisFintype : ∀ x, Fintype (Basis x)
  epsilon : Matrix PUnit.{u+1} (Σ x, Basis x) R

attribute [instance] Family.posFintype Family.basisFintype

/-- Per-column evaluation of the global augmentation. -/
def Family.weight (A : Family.{u,v} R) (x : A.Pos) (a : A.Basis x) : R :=
  A.epsilon PUnit.unit ⟨x, a⟩

/-- The coefficient arrow indexed by a target carrier, as in the source. -/
abbrev NativeCoefficients (A B : Family.{u,v} R) (f : A.Pos → B.Pos) :=
  ∀ z : B.Pos, Matrix (B.Basis z) (Σ x : {x // f x = z}, A.Basis x.1) R

/-- Equivalent source-indexed columns of the actual coefficient arrows. -/
abbrev BlockColumns (A B : Family.{u,v} R) (f : A.Pos → B.Pos) :=
  ∀ x : A.Pos, Matrix (B.Basis (f x)) (A.Basis x) R

def packBlock {A B : Family.{u,v} R} {f : A.Pos → B.Pos}
    (m : BlockColumns A B f) : NativeCoefficients A B f :=
  fun _ b a => (a.1.2 ▸ m a.1.1) b a.2

def unpackBlock {A B : Family.{u,v} R} {f : A.Pos → B.Pos}
    (m : NativeCoefficients A B f) : BlockColumns A B f :=
  fun x b a => m (f x) b ⟨⟨x,rfl⟩, a⟩

def nativeColumns (A B : Family.{u,v} R) (f : A.Pos → B.Pos) :
    BlockColumns A B f ≃ NativeCoefficients A B f where
  toFun := packBlock
  invFun := unpackBlock
  left_inv := by intro m; rfl
  right_inv := by
    intro m
    funext z b a
    rcases a with ⟨⟨x,h⟩,a⟩
    subst z
    rfl

/-- The induced matrix on total coefficients, with zero outside the carrier
map's fibres. The zeros here are entries; no carrier is removed. -/
def totalMap {A B : Family.{u,v} R} {f : A.Pos → B.Pos} (m : BlockColumns A B f) :
    Matrix (Σ z, B.Basis z) (Σ x, A.Basis x) R := by
  classical
  exact fun b a => if h : f a.1 = b.1 then
    packBlock m b.1 b.2 ⟨⟨a.1,h⟩,a.2⟩ else 0

theorem augmentation_iff {A B : Family.{u,v} R} {f : A.Pos → B.Pos}
    (m : BlockColumns A B f) :
    mul (totalMap m) B.epsilon = A.epsilon ↔
      ∀ x a, (∑ b : B.Basis (f x), B.weight (f x) b * m x b a) = A.weight x a := by
  classical
  have he (x : A.Pos) (a : A.Basis x) :
      mul (totalMap m) B.epsilon PUnit.unit ⟨x,a⟩ =
        ∑ b : B.Basis (f x), B.weight (f x) b * m x b a := by
    simp only [mul, Fintype.sum_sigma]
    rw [Fintype.sum_eq_single (f x)]
    · simp [totalMap, packBlock, Family.weight]
    · intro z hz
      apply Finset.sum_eq_zero
      intro b _
      simp [totalMap, Ne.symm hz]
  constructor
  · intro h x a
    rw [← he, h]
    rfl
  · intro h
    funext p xa
    rcases xa with ⟨x,a⟩
    cases p
    rw [he, h]
    rfl

structure Hom (A B : Family.{u,v} R) where
  pos : A.Pos → B.Pos
  block : BlockColumns A B pos
  aug : ∀ x a, (∑ b : B.Basis (pos x), B.weight (pos x) b * block x b a) = A.weight x a

private def row {A : Type u} (w : A → R) : Matrix PUnit.{u+1} A R := fun _ => w

namespace Hom

def native {A B : Family.{u,v} R} (m : Hom A B) :
    NativeCoefficients A B m.pos := packBlock m.block

/-- Preservation of the actual global augmentation by the actual total arrow. -/
theorem globalAug {A B : Family.{u,v} R} (m : Hom A B) :
    mul (totalMap m.block) B.epsilon = A.epsilon :=
  (augmentation_iff m.block).2 m.aug

def ofNative {A B : Family.{u,v} R} (f : A.Pos → B.Pos) (m : NativeCoefficients A B f)
    (h : mul (totalMap (unpackBlock m)) B.epsilon = A.epsilon) : Hom A B :=
  ⟨f, unpackBlock m, (augmentation_iff _).1 h⟩

@[simp] theorem ofNative_native {A B : Family.{u,v} R} (f : A.Pos → B.Pos)
    (m : NativeCoefficients A B f) (h) : (ofNative f m h).native = m :=
  (nativeColumns A B f).right_inv m

/-- Equality of source-indexed matrices with the necessary target transport
is equality of native arrows, including their carrier maps. -/
theorem ext {A B : Family.{u,v} R} {f g : Hom A B}
    (h : ∀ x, f.pos x = g.pos x)
    (hb : ∀ x, (h x ▸ f.block x) = g.block x) : f = g := by
  have hp := funext h
  cases f with
  | mk f fm fa =>
    cases g with
    | mk g gm ga =>
      dsimp at hp
      subst g
      have hh : h = fun _ => rfl := Subsingleton.elim _ _
      cases hh
      have hm := funext hb
      dsimp at hm
      subst gm
      rfl

def id (A : Family.{u,v} R) : Hom A A where
  pos x := x
  block _ := perm (Equiv.refl _)
  aug x a := by
    change mul (perm (Equiv.refl (A.Basis x))) (row (A.weight x)) PUnit.unit a = _
    simp [row]

def comp {A B C : Family.{u,v} R} (f : Hom A B) (g : Hom B C) : Hom A C where
  pos x := g.pos (f.pos x)
  block x := mul (f.block x) (g.block (f.pos x))
  aug x a := by
    classical
    change mul (mul (f.block x) (g.block (f.pos x))) (row (C.weight _)) PUnit.unit a = _
    rw [mul_assoc]
    simp only [mul, row, g.aug, f.aug]

theorem id_comp {A B : Family.{u,v} R} (f : Hom A B) : comp (id A) f = f := by
  refine ext (fun _ => rfl) ?_
  intro x
  funext b a
  simp [comp, id]

theorem comp_id {A B : Family.{u,v} R} (f : Hom A B) : comp f (id B) = f := by
  refine ext (fun _ => rfl) ?_
  intro x
  funext b a
  simp [comp, id]

theorem comp_assoc {A B C D : Family.{u,v} R} (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp (comp f g) h = comp f (comp g h) := by
  refine ext (fun _ => rfl) ?_
  intro x
  exact mul_assoc _ _ _

/-- Carrier and basis equivalences preserving every augmentation column
produce an actual native map with permutation coefficient matrices. -/
def relabel {A B : Family.{u,v} R} (e : A.Pos ≃ B.Pos)
    (eb : ∀ x, A.Basis x ≃ B.Basis (e x))
    (h : ∀ x a, B.weight (e x) (eb x a) = A.weight x a) : Hom A B where
  pos := e
  block x := perm (eb x)
  aug x a := by
    change mul (perm (eb x)) (row (B.weight _)) PUnit.unit a = _
    simpa [row] using h x a

end Hom

/-- The singleton context unit has one carrier and one basis vector. -/
def unit (R : Type v) [CommSemiring R] : Family.{u,v} R where
  Pos := PUnit
  posFintype := inferInstance
  Basis _ := PUnit
  basisFintype _ := inferInstance
  epsilon _ _ := 1

def toUnit (A : Family.{u,v} R) : Hom A (unit R) where
  pos _ := PUnit.unit
  block x _ a := A.weight x a
  aug x a := by
    change (∑ _ : PUnit, 1 * A.weight x a) = A.weight x a
    simp

theorem unit_terminal (A : Family.{u,v} R) (m : Hom A (unit R)) : m = toUnit A := by
  have ep (x : A.Pos) : m.pos x = (toUnit A).pos x := by
    exact Subsingleton.elim (α := PUnit) _ _
  refine Hom.ext ep ?_
  intro x
  have hrec (p q : (unit R).Pos) (e : p = q) (k : Matrix PUnit.{u+1} (A.Basis x) R) :
      (Eq.rec (motive := fun z _ => Matrix ((unit R).Basis z) (A.Basis x) R) k e) = k := by
    cases e
    rfl
  refine (hrec _ _ (ep x) (m.block x)).trans ?_
  funext b a
  have h := m.aug x a
  change (∑ b : PUnit, 1 * m.block x b a) = _ at h
  cases b
  simpa [toUnit] using h


/-- The dependent sum of choice carriers with binary tensor on coefficients.
The coefficient-basis product and multiplication of row entries implement
the continuation augmentation followed by the outer augmentation. -/
def dependent (A : Family.{u,v} R) (Q : A.Pos → Family.{u,v} R) : Family.{u,v} R where
  Pos := Σ x : A.Pos, (Q x).Pos
  posFintype := inferInstance
  Basis xy := A.Basis xy.1 × (Q xy.1).Basis xy.2
  basisFintype _ := inferInstance
  epsilon _ s := A.weight s.1.1 s.2.1 * (Q s.1.1).weight s.1.2 s.2.2

/-- A native map of dependent pairs; nothing requires either carrier map to
be injective or to belong to the projection class. -/
structure DepHom {A B : Family.{u,v} R} (Q : A.Pos → Family.{u,v} R)
    (S : B.Pos → Family.{u,v} R) where
  outer : Hom A B
  inner : ∀ x, Hom (Q x) (S (outer.pos x))

namespace DepHom

def id {A : Family.{u,v} R} (Q : A.Pos → Family.{u,v} R) : DepHom Q Q :=
  ⟨Hom.id A, fun x => Hom.id (Q x)⟩

def comp {A B C : Family.{u,v} R} {Q : A.Pos → Family.{u,v} R}
    {S : B.Pos → Family.{u,v} R} {T : C.Pos → Family.{u,v} R}
    (f : DepHom Q S) (g : DepHom S T) : DepHom Q T :=
  ⟨f.outer.comp g.outer, fun x => (f.inner x).comp (g.inner (f.outer.pos x))⟩

def accumulate {A B : Family.{u,v} R} {Q : A.Pos → Family.{u,v} R}
    {S : B.Pos → Family.{u,v} R} (f : DepHom Q S) : Hom (dependent A Q) (dependent B S) where
  pos xy := ⟨f.outer.pos xy.1, (f.inner xy.1).pos xy.2⟩
  block xy := kron (f.outer.block xy.1) ((f.inner xy.1).block xy.2)
  aug xy a := by
    let wr₁ := row (B.weight (f.outer.pos xy.1))
    let wr₂ := row ((S (f.outer.pos xy.1)).weight ((f.inner xy.1).pos xy.2))
    change mul (kron (f.outer.block xy.1) ((f.inner xy.1).block xy.2)) (kron wr₁ wr₂)
        (PUnit.unit, PUnit.unit) a = _
    rw [mul_kron]
    change (∑ b, B.weight (f.outer.pos xy.1) b * f.outer.block xy.1 b a.1) *
      (∑ d, (S (f.outer.pos xy.1)).weight ((f.inner xy.1).pos xy.2) d *
        (f.inner xy.1).block xy.2 d a.2) = _
    rw [f.outer.aug, (f.inner xy.1).aug]
    rfl

theorem accumulate_id {A : Family.{u,v} R} (Q : A.Pos → Family.{u,v} R) :
    (id Q).accumulate = Hom.id (dependent A Q) := by
  refine Hom.ext (fun _ => rfl) ?_
  · intro x
    change kron (perm (Equiv.refl (A.Basis x.1))) (perm (Equiv.refl ((Q x.1).Basis x.2))) = _
    rw [kron_perm]
    rfl

theorem accumulate_comp {A B C : Family.{u,v} R} {Q : A.Pos → Family.{u,v} R}
    {S : B.Pos → Family.{u,v} R} {T : C.Pos → Family.{u,v} R}
    (f : DepHom Q S) (g : DepHom S T) :
    (f.comp g).accumulate = f.accumulate.comp g.accumulate := by
  refine Hom.ext (fun _ => rfl) ?_
  · intro x
    exact (mul_kron (f.outer.block x.1) (g.outer.block (f.outer.pos x.1))
      ((f.inner x.1).block x.2) ((g.inner (f.outer.pos x.1)).block ((f.inner x.1).pos x.2))).symm

/-- Native fibre entries: the inner map is evaluated at the source outer
position before merging by the outer map. This is the column form of the
source's two-stage block composite. -/
theorem accumulate_native_apply {A B : Family.{u,v} R} {Q : A.Pos → Family.{u,v} R}
    {S : B.Pos → Family.{u,v} R} (f : DepHom Q S)
    (xy : (dependent A Q).Pos) (b : (dependent B S).Basis (f.accumulate.pos xy))
    (a : (dependent A Q).Basis xy) :
    f.accumulate.native (f.accumulate.pos xy) b ⟨⟨xy,rfl⟩,a⟩ =
      f.outer.block xy.1 b.1 a.1 * (f.inner xy.1).block xy.2 b.2 a.2 := rfl

end DepHom

/-- All positions are separately addressed; repeated objects do not imply
shared choices. No coefficient basis or raw choice is deduplicated. -/
def occurrence {E : Type u} [Fintype E] (A : E → Family.{u,v} R) : Family.{u,v} R where
  Pos := ∀ i, (A i).Pos
  posFintype := inferInstance
  Basis x := ∀ i, (A i).Basis (x i)
  basisFintype _ := inferInstance
  epsilon _ s := ∏ i, (A i).weight (s.1 i) (s.2 i)

def occurrenceMap {E : Type u} [Fintype E] {A B : E → Family.{u,v} R}
    (f : ∀ i, Hom (A i) (B i)) : Hom (occurrence A) (occurrence B) where
  pos x i := (f i).pos (x i)
  block x := tensorMatrix (fun i => (f i).block (x i))
  aug x a := by
    let wr := fun i => row ((B i).weight ((f i).pos (x i)))
    change mul (tensorMatrix (fun i => (f i).block (x i))) (tensorMatrix wr)
      (fun _ => PUnit.unit) a = _
    rw [mul_tensorMatrix]
    change (∏ i, ∑ b, (B i).weight ((f i).pos (x i)) b * (f i).block (x i) b (a i)) = _
    simp only [Hom.aug]
    rfl

theorem occurrenceMap_id {E : Type u} [Fintype E] (A : E → Family.{u,v} R) :
    occurrenceMap (fun i => Hom.id (A i)) = Hom.id (occurrence A) := by
  refine Hom.ext (fun _ => rfl) ?_
  · intro x
    change tensorMatrix (fun i => perm (Equiv.refl ((A i).Basis (x i)))) = _
    rw [tensorMatrix_perm]
    rfl

theorem occurrenceMap_comp {E : Type u} [Fintype E] {A B C : E → Family.{u,v} R}
    (f : ∀ i, Hom (A i) (B i)) (g : ∀ i, Hom (B i) (C i)) :
    occurrenceMap (fun i => (f i).comp (g i)) = (occurrenceMap f).comp (occurrenceMap g) := by
  refine Hom.ext (fun _ => rfl) ?_
  · intro x
    exact (mul_tensorMatrix (fun i => (f i).block (x i))
      (fun i => (g i).block ((f i).pos (x i)))).symm

theorem occurrenceMap_native_apply {E : Type u} [Fintype E] {A B : E → Family.{u,v} R}
    (f : ∀ i, Hom (A i) (B i)) (x : (occurrence A).Pos)
    (b : (occurrence B).Basis ((occurrenceMap f).pos x)) (a : (occurrence A).Basis x) :
    (occurrenceMap f).native ((occurrenceMap f).pos x) b ⟨⟨x,rfl⟩,a⟩ =
      ∏ i, (f i).block (x i) (b i) (a i) := rfl

section Fubini

variable {E : Type u} [Fintype E]
variable (A : E → Family.{u,v} R) (Q : ∀ i, (A i).Pos → Family.{u,v} R)

abbrev leftFamily := occurrence (fun i => dependent (A i) (Q i))
abbrev rightFamily := dependent (occurrence A) (fun x => occurrence (fun i => Q i (x i)))

/-- The tagged dependent choice permutation, with no diagonal. -/
def fubiniPos : (leftFamily A Q).Pos ≃ (rightFamily A Q).Pos where
  toFun xy := ⟨fun i => (xy i).1, fun i => (xy i).2⟩
  invFun ab i := ⟨ab.1 i, ab.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tagged coefficient shuffle, with no evaluation to totals. -/
def fubiniBasis (xy : (leftFamily A Q).Pos) :
    (leftFamily A Q).Basis xy ≃ (rightFamily A Q).Basis (fubiniPos A Q xy) where
  toFun a := (fun i => (a i).1, fun i => (a i).2)
  invFun ab i := (ab.1 i, ab.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem fubiniAug (xy : (leftFamily A Q).Pos) (a : (leftFamily A Q).Basis xy) :
    (rightFamily A Q).weight (fubiniPos A Q xy) (fubiniBasis A Q xy a) =
      (leftFamily A Q).weight xy a := by
  exact (Finset.prod_mul_distrib
    (f := fun i => (A i).weight (xy i).1 (a i).1)
    (g := fun i => (Q i (xy i).1).weight (xy i).2 (a i).2)).symm

def fubini : Hom (leftFamily A Q) (rightFamily A Q) :=
  Hom.relabel (fubiniPos A Q) (fubiniBasis A Q) (fubiniAug A Q)

def fubiniInv : Hom (rightFamily A Q) (leftFamily A Q) :=
  Hom.relabel (fubiniPos A Q).symm (fun xy => (fubiniBasis A Q ((fubiniPos A Q).symm xy)).symm)
    (fun xy a => (fubiniAug A Q ((fubiniPos A Q).symm xy)
      ((fubiniBasis A Q ((fubiniPos A Q).symm xy)).symm a)).symm)

theorem fubini_hom_inv : (fubini A Q).comp (fubiniInv A Q) = Hom.id (leftFamily A Q) := by
  refine Hom.ext (fun _ => rfl) ?_
  · intro x
    change mul (perm (fubiniBasis A Q x)) (perm (fubiniBasis A Q x).symm) = _
    rw [perm_comp, Equiv.self_trans_symm]
    rfl

theorem fubini_inv_hom : (fubiniInv A Q).comp (fubini A Q) = Hom.id (rightFamily A Q) := by
  refine Hom.ext (fun _ => rfl) ?_
  · intro x
    change mul (perm (fubiniBasis A Q ((fubiniPos A Q).symm x)).symm)
      (perm (fubiniBasis A Q ((fubiniPos A Q).symm x))) = _
    rw [perm_comp, Equiv.symm_trans_self]
    rfl

variable {A Q}

def fubiniLeftMap {B : E → Family.{u,v} R} {S : ∀ i, (B i).Pos → Family.{u,v} R}
    (f : ∀ i, DepHom (Q i) (S i)) : Hom (leftFamily A Q) (leftFamily B S) :=
  occurrenceMap fun i => (f i).accumulate

def fubiniRightMap {B : E → Family.{u,v} R} {S : ∀ i, (B i).Pos → Family.{u,v} R}
    (f : ∀ i, DepHom (Q i) (S i)) : Hom (rightFamily A Q) (rightFamily B S) :=
  DepHom.accumulate
    ⟨occurrenceMap (fun i => (f i).outer), fun x => occurrenceMap (fun i => (f i).inner (x i))⟩

/-- Naturality holds as equality of native carrier-and-matrix arrows, even
for simultaneous many-to-one outer and inner carrier maps. -/
theorem fubini_natural {B : E → Family.{u,v} R} {S : ∀ i, (B i).Pos → Family.{u,v} R}
    (f : ∀ i, DepHom (Q i) (S i)) :
    (fubiniLeftMap f).comp (fubini B S) = (fubini A Q).comp (fubiniRightMap f) := by
  refine Hom.ext (fun _ => rfl) ?_
  · intro x
    funext b a
    change mul ((fubiniLeftMap f).block x) (perm (fubiniBasis B S ((fubiniLeftMap f).pos x))) b a =
      mul (perm (fubiniBasis A Q x)) ((fubiniRightMap f).block (fubiniPos A Q x)) b a
    refine (mul_perm_right _ _ _ _).trans ?_
    refine Eq.trans ?_ (mul_perm_left _ _ _ _).symm
    exact Finset.prod_mul_distrib
      (f := fun i => (f i).outer.block (x i).1 (b.1 i) (a i).1)
      (g := fun i => ((f i).inner (x i).1).block (x i).2 (b.2 i) (a i).2)

end Fubini

/-- The native total map is functorial. In particular the sum over the intermediate
carrier is the actual partition by the first native carrier map. -/
theorem totalMap_comp {A B C : Family.{u,v} R} (f : Hom A B) (g : Hom B C) :
    totalMap (f.comp g).block = mul (totalMap f.block) (totalMap g.block) := by
  classical
  funext zb xa
  rcases zb with ⟨z,b⟩
  rcases xa with ⟨x,a⟩
  simp only [mul, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single (f.pos x)]
  · by_cases h : g.pos (f.pos x) = z
    · subst z
      simp [totalMap, packBlock, Hom.comp, mul]
    · simp [totalMap, packBlock, Hom.comp, h]
  · intro y hy
    apply Finset.sum_eq_zero
    intro c _
    simp [totalMap, Ne.symm hy]

/-- A projection class is an input concerning extension projections, not native
arrow carrier maps. Its universe accommodates possibly infinite base sets. -/
structure ProjectionClass where
  admits : ∀ {X Y : Type w}, (X → Y) → Prop
  equiv : ∀ {X Y : Type w} (e : X ≃ Y), admits e
  comp : ∀ {X Y Z : Type w} {f : X → Y} {g : Y → Z}, admits f → admits g → admits (g ∘ f)
  pullback : ∀ {X Y Z : Type w} (g : Y → Z) (f : X → Z), admits f →
    admits (fun yx : {p : Y × X // g p.1 = f p.2} => yx.1.1)

section Projections

variable {Base : Type u}

/-- Raw extension, with its base projection. This does not test coefficients. -/
abbrev Extension (A : Base → Family.{u,v} R) := Σ i, (A i).Pos

def proj (A : Base → Family.{u,v} R) : Extension A → Base := Sigma.fst

variable {Base' : Type u}

def reindexPullback (A : Base → Family.{u,v} R) (f : Base' → Base) :
    Extension (A ∘ f) ≃ {p : Base' × Extension A // f p.1 = proj A p.2} where
  toFun ax := ⟨(ax.1, ⟨f ax.1, ax.2⟩), rfl⟩
  invFun ax := ⟨ax.1.1, cast (congrArg (fun i => (A i).Pos) ax.2.symm) ax.1.2.2⟩
  left_inv _ := rfl
  right_inv ax := by
    rcases ax with ⟨⟨i, ⟨j,x⟩⟩, e⟩
    change f i = j at e
    subst j
    rfl

omit [CommSemiring R] in
theorem admits_reindex (J : ProjectionClass.{u}) (A : Base → Family.{u,v} R)
    (f : Base' → Base) (h : J.admits (proj A)) : J.admits (proj (A ∘ f)) :=
  J.comp (f := reindexPullback A f)
    (g := fun yx : {p : Base' × Extension A // f p.1 = proj A p.2} => yx.1.1)
    (J.equiv (reindexPullback A f)) (J.pullback f (proj A) h)

def dependentExtension (A : Base → Family.{u,v} R) (Q : Extension A → Family.{u,v} R) :
    Extension (fun i => dependent (A i) (fun x => Q ⟨i,x⟩)) ≃ Extension Q where
  toFun ixy := ⟨⟨ixy.1, ixy.2.1⟩, ixy.2.2⟩
  invFun ixy := ⟨ixy.1.1, ⟨ixy.1.2, ixy.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem admits_dependent (J : ProjectionClass.{u}) (A : Base → Family.{u,v} R)
    (Q : Extension A → Family.{u,v} R) (hA : J.admits (proj A)) (hQ : J.admits (proj Q)) :
    J.admits (proj (fun i => dependent (A i) (fun x => Q ⟨i,x⟩))) :=
  J.comp (f := dependentExtension A Q) (g := proj A ∘ proj Q)
    (J.equiv (dependentExtension A Q)) (J.comp (f := proj Q) (g := proj A) hQ hA)

theorem admits_unit (J : ProjectionClass.{u}) :
    J.admits (proj (fun _ : Base => unit R)) :=
  J.equiv ⟨Sigma.fst, fun i => ⟨i,PUnit.unit⟩,
    fun ⟨_,.unit⟩ => rfl, fun _ => rfl⟩

end Projections

/-- A structural path records its tagged carrier and coefficient rewiring and
the preservation of the global augmentation. It is not an arbitrary matrix. -/
structure Wiring (A B : Family.{u,v} R) where
  pos : A.Pos ≃ B.Pos
  basis : ∀ x, A.Basis x ≃ B.Basis (pos x)
  aug : ∀ x a, B.weight (pos x) (basis x a) = A.weight x a

namespace Wiring

def hom {A B : Family.{u,v} R} (m : Wiring A B) : Hom A B :=
  Hom.relabel m.pos m.basis m.aug

def comp {A B C : Family.{u,v} R} (a : Wiring A B) (b : Wiring B C) : Wiring A C where
  pos := a.pos.trans b.pos
  basis x := (a.basis x).trans (b.basis (a.pos x))
  aug x ba := (b.aug (a.pos x) (a.basis x ba)).trans (a.aug x ba)

theorem hom_comp {A B C : Family.{u,v} R} (a : Wiring A B) (b : Wiring B C) :
    a.hom.comp b.hom = (a.comp b).hom := by
  refine Hom.ext (fun _ => rfl) ?_
  intro x
  exact perm_comp (a.basis x) (b.basis (a.pos x))

private theorem transport_perm {A B : Family.{u,v} R} {x : A.Pos} {y z : B.Pos}
    (h : y = z) (f : A.Basis x ≃ B.Basis y) (g : A.Basis x ≃ B.Basis z)
    (he : ∀ a, h ▸ f a = g a) :
    (h ▸ (perm f : Matrix (B.Basis y) (A.Basis x) R)) = perm g := by
  cases h
  exact congrArg perm (Equiv.ext he)

/-- A mechanized local coherence principle: the tagged paths must have the same
position and the same basis routing, not simply share untagged endpoints. -/
theorem compare {A B : Family.{u,v} R} (a b : Wiring A B)
    (ep : ∀ x, a.pos x = b.pos x)
    (eb : ∀ x c, (ep x ▸ a.basis x c) = b.basis x c) : a.hom = b.hom := by
  refine Hom.ext ep ?_
  intro x
  exact transport_perm (A := A) (B := B) (x := x) (ep x) _ _ (eb x)

def occurrenceWiring {E : Type u} [Fintype E] {A B : E → Family.{u,v} R}
    (m : ∀ i, Wiring (A i) (B i)) : Wiring (occurrence A) (occurrence B) where
  pos := Equiv.piCongrRight (fun i => (m i).pos)
  basis x := Equiv.piCongrRight (fun i => (m i).basis (x i))
  aug x a := by
    change (∏ i, (B i).weight ((m i).pos (x i)) ((m i).basis (x i) (a i))) =
      ∏ i, (A i).weight (x i) (a i)
    simp only [Wiring.aug]

theorem occurrenceWiring_hom {E : Type u} [Fintype E] {A B : E → Family.{u,v} R}
    (m : ∀ i, Wiring (A i) (B i)) :
    occurrenceMap (fun i => (m i).hom) = (occurrenceWiring m).hom := by
  refine Hom.ext (fun _ => rfl) ?_
  intro x
  exact tensorMatrix_perm (fun i => (m i).basis (x i))

def dependentWiring {A B : Family.{u,v} R} {Q : A.Pos → Family.{u,v} R}
    {S : B.Pos → Family.{u,v} R} (m : Wiring A B) (q : ∀ x, Wiring (Q x) (S (m.pos x))) :
    Wiring (dependent A Q) (dependent B S) where
  pos := Equiv.sigmaCongr m.pos (fun x => (q x).pos)
  basis xy := Equiv.prodCongr (m.basis xy.1) ((q xy.1).basis xy.2)
  aug xy a := by
    change B.weight (m.pos xy.1) (m.basis xy.1 a.1) *
      (S (m.pos xy.1)).weight ((q xy.1).pos xy.2) ((q xy.1).basis xy.2 a.2) =
      A.weight xy.1 a.1 * (Q xy.1).weight xy.2 a.2
    rw [m.aug, (q xy.1).aug]

theorem dependentWiring_hom {A B : Family.{u,v} R} {Q : A.Pos → Family.{u,v} R}
    {S : B.Pos → Family.{u,v} R} (m : Wiring A B) (q : ∀ x, Wiring (Q x) (S (m.pos x))) :
    DepHom.accumulate (Q := Q) (S := S) ⟨m.hom, fun x => (q x).hom⟩ =
      (dependentWiring m q).hom := by
  refine Hom.ext (fun _ => rfl) ?_
  intro x
  exact kron_perm (m.basis x.1) ((q x.1).basis x.2)

def id (A : Family.{u,v} R) : Wiring A A :=
  ⟨Equiv.refl _, fun _ => Equiv.refl _, fun _ _ => rfl⟩

theorem id_hom (A : Family.{u,v} R) : (id A).hom = Hom.id A := rfl

end Wiring

def fubiniWiring {E : Type u} [Fintype E]
    (A : E → Family.{u,v} R) (Q : ∀ i, (A i).Pos → Family.{u,v} R) :
    Wiring (leftFamily A Q) (rightFamily A Q) :=
  ⟨fubiniPos A Q, fubiniBasis A Q, fubiniAug A Q⟩

theorem fubiniWiring_hom {E : Type u} [Fintype E]
    (A : E → Family.{u,v} R) (Q : ∀ i, (A i).Pos → Family.{u,v} R) :
    (fubiniWiring A Q).hom = fubini A Q := rfl

/-- Dependent association is native, with tensor association on basis vectors. -/
def dependentAssoc (A : Family.{u,v} R) (Q : A.Pos → Family.{u,v} R)
    (T : (dependent A Q).Pos → Family.{u,v} R) :
    Wiring (dependent (dependent A Q) T)
      (dependent A (fun x => dependent (Q x) (fun y => T ⟨x,y⟩))) where
  pos := ⟨fun xyz => ⟨xyz.1.1, ⟨xyz.1.2, xyz.2⟩⟩,
    fun xyz => ⟨⟨xyz.1, xyz.2.1⟩, xyz.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  basis _ := Equiv.prodAssoc _ _ _
  aug x a := by
    change _ * (_ * _) = (_ * _) * _
    exact (_root_.mul_assoc _ _ _).symm

/-- The empty occurrence is the terminal context, with one coefficient basis
vector and augmentation the identity. -/
def occurrenceEmpty {E : Type u} [Fintype E] [IsEmpty E] (A : E → Family.{u,v} R) :
    Wiring (occurrence A) (unit R) where
  pos := ⟨fun _ => PUnit.unit, fun _ i => isEmptyElim i,
    fun _ => funext fun i => isEmptyElim i, fun _ => rfl⟩
  basis _ := ⟨fun _ => PUnit.unit, fun _ i => isEmptyElim i,
    fun _ => funext fun i => isEmptyElim i, fun _ => rfl⟩
  aug _ _ := by
    change 1 = ∏ i, _
    simp

/-- Rebracket a partition of occurrence addresses indexed by dependent pairs. -/
def occurrenceRegroup {E : Type u} [Fintype E] {F : E → Type u} [∀ i, Fintype (F i)]
    (A : (Σ i,F i) → Family.{u,v} R) :
    Wiring (occurrence A) (occurrence (fun i => occurrence (fun j : F i => A ⟨i,j⟩))) where
  pos := Equiv.piCurry (fun (i : E) (j : F i) => (A ⟨i,j⟩).Pos)
  basis x := Equiv.piCurry (fun (i : E) (j : F i) => (A ⟨i,j⟩).Basis (x ⟨i,j⟩))
  aug x a := by
    change (∏ i, ∏ j : F i, (A ⟨i,j⟩).weight (x ⟨i,j⟩) (a ⟨i,j⟩)) =
      ∏ ij : (Σ i,F i), (A ij).weight (x ij) (a ij)
    rw [Fintype.prod_sigma]

/-- Permute the occurrence addresses, including repeated identical objects. -/
def occurrencePermute {E F : Type u} [Fintype E] [Fintype F] (e : E ≃ F) (A : F → Family.{u,v} R) :
    Wiring (occurrence A) (occurrence (A ∘ e)) where
  pos := Equiv.piCongrLeft' (fun i => (A i).Pos) e.symm
  basis x := Equiv.piCongrLeft' (fun i => (A i).Basis (x i)) e.symm
  aug x a := by
    change (∏ i : E, (A (e i)).weight (x (e i)) (a (e i))) =
      ∏ i : F, (A i).weight (x i) (a i)
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Fubini commutes with every regrouping along a partition of the addresses.
Both composites are compared as native augmented arrows. -/
theorem fubini_regroup {E : Type u} [Fintype E] {F : E → Type u} [∀ i, Fintype (F i)]
    (A : (Σ i,F i) → Family.{u,v} R) (Q : ∀ i, (A i).Pos → Family.{u,v} R) :
    let BB := fun i => occurrence (fun j : F i => A ⟨i,j⟩)
    let SS := fun i (x : (BB i).Pos) => occurrence (fun j : F i => Q ⟨i,j⟩ (x j))
    ((occurrenceRegroup (fun i => dependent (A i) (Q i))).hom.comp
        (occurrenceMap (fun i => fubini (fun j : F i => A ⟨i,j⟩) (fun j => Q ⟨i,j⟩)))).comp
          (fubini BB SS) =
      (fubini A Q).comp
        (DepHom.accumulate (S := fun x : (occurrence BB).Pos => occurrence (fun i => SS i (x i)))
          ⟨(occurrenceRegroup A).hom, fun x => (occurrenceRegroup (fun i => Q i (x i))).hom⟩) := by
  dsimp only
  simp only [← fubiniWiring_hom, Wiring.occurrenceWiring_hom, Wiring.hom_comp]
  rw [Wiring.dependentWiring_hom
    (Q := fun x : (occurrence A).Pos => occurrence (fun i => Q i (x i)))
    (S := fun x : (occurrence (fun i => occurrence (fun j : F i => A ⟨i,j⟩))).Pos =>
      occurrence (fun i => occurrence (fun j : F i => Q ⟨i,j⟩ (x i j))))
    (occurrenceRegroup A) (fun x => occurrenceRegroup (fun i => Q i (x i)))]
  rw [Wiring.hom_comp]
  exact Wiring.compare (R := R) _ _ (fun _ => rfl) (fun _ _ => rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Fubini commutes with every permutation of occurrence addresses. -/
theorem fubini_permute {E F : Type u} [Fintype E] [Fintype F]
    (e : E ≃ F) (A : F → Family.{u,v} R) (Q : ∀ i, (A i).Pos → Family.{u,v} R) :
    (occurrencePermute e (fun i => dependent (A i) (Q i))).hom.comp
      (fubini (A ∘ e) (fun i => Q (e i))) =
    (fubini A Q).comp (DepHom.accumulate
      (S := fun x : (occurrence (A ∘ e)).Pos => occurrence (fun i => Q (e i) (x i)))
      ⟨(occurrencePermute e A).hom, fun x => (occurrencePermute e (fun i => Q i (x i))).hom⟩) := by
  simp only [← fubiniWiring_hom, Wiring.hom_comp]
  rw [Wiring.dependentWiring_hom
    (Q := fun x : (occurrence A).Pos => occurrence (fun i => Q i (x i)))
    (S := fun x : (occurrence (A ∘ e)).Pos => occurrence (fun i => Q (e i) (x i)))
    (occurrencePermute e A) (fun x => occurrencePermute e (fun i => Q i (x i)))]
  rw [Wiring.hom_comp]
  exact Wiring.compare (R := R) _ _ (fun _ => rfl) (fun _ _ => rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The two routes from three layers of dependent choices to three layers of
addressed tensors. The occurrence addresses are untouched; the two routes
only regroup the same tagged choices and basis factors. -/
theorem fubini_dependentAssoc {E : Type u} [Fintype E]
    (A : E → Family.{u,v} R) (Q : ∀ i, (A i).Pos → Family.{u,v} R)
    (T : ∀ i, (dependent (A i) (Q i)).Pos → Family.{u,v} R) :
    let mid := fun x : (occurrence A).Pos => occurrence (fun i => Q i (x i))
    let last := fun xy : (dependent (occurrence A) mid).Pos =>
      occurrence (fun i => T i ⟨xy.1 i, xy.2 i⟩)
    let seq := fun i x => dependent (Q i x) (fun y => T i ⟨x,y⟩)
    let seqLast := fun x : (occurrence A).Pos =>
      dependent (mid x) (fun y => last ⟨x,y⟩)
    ((occurrenceMap (fun i => (dependentAssoc (A i) (Q i) (T i)).hom)).comp
      (fubini A seq)).comp
        (DepHom.accumulate (S := seqLast)
          ⟨Hom.id (occurrence A), fun x => fubini (fun i => Q i (x i)) (fun i y => T i ⟨x i,y⟩)⟩) =
    ((fubini (fun i => dependent (A i) (Q i)) T).comp
      (DepHom.accumulate (S := last) ⟨fubini A Q, fun _ => Hom.id _⟩)).comp
        (dependentAssoc (occurrence A) mid last).hom := by
  dsimp only
  simp only [← fubiniWiring_hom, ← Wiring.id_hom, Wiring.occurrenceWiring_hom,
    Wiring.hom_comp]
  let mid := fun x : (occurrence A).Pos => occurrence (fun i => Q i (x i))
  let last := fun xy : (dependent (occurrence A) mid).Pos =>
    occurrence (fun i => T i ⟨xy.1 i, xy.2 i⟩)
  let left := fun x : (occurrence A).Pos =>
    occurrence (fun i => dependent (Q i (x i)) (fun y => T i ⟨x i,y⟩))
  let right := fun x : (occurrence A).Pos => dependent (mid x) (fun y => last ⟨x,y⟩)
  rw [Wiring.dependentWiring_hom (Q := left) (S := right)
    (Wiring.id (occurrence A)) (fun x => fubiniWiring (fun i => Q i (x i)) (fun i y => T i ⟨x i,y⟩))]
  rw [Wiring.dependentWiring_hom
    (Q := fun x : (leftFamily A Q).Pos => occurrence (fun i => T i (x i)))
    (S := last) (fubiniWiring A Q) (fun x => Wiring.id (occurrence (fun i => T i (x i))))]
  simp only [Wiring.hom_comp]
  exact Wiring.compare (R := R) _ _ (fun _ => rfl) (fun _ _ => rfl)

def dependentRightUnit (A : Family.{u,v} R) : Wiring (dependent A (fun _ => unit R)) A where
  pos := ⟨Sigma.fst, fun x => ⟨x,PUnit.unit⟩, fun ⟨x,.unit⟩ => rfl, fun _ => rfl⟩
  basis x := Equiv.prodPUnit (A.Basis x.1)
  aug x a := by change A.weight x.1 a.1 = A.weight x.1 a.1 * 1; simp

def dependentLeftUnit (A : Family.{u,v} R) : Wiring (dependent (unit R) (fun _ => A)) A where
  pos := ⟨Sigma.snd, fun x => ⟨PUnit.unit,x⟩, fun ⟨.unit,_⟩ => rfl, fun _ => rfl⟩
  basis x := Equiv.punitProd (A.Basis x.2)
  aug x a := by change A.weight x.2 a.2 = 1 * A.weight x.2 a.2; simp

def occurrenceUnit {E : Type u} [Fintype E] :
    Wiring (occurrence (fun _ : E => unit R)) (unit R) where
  pos := ⟨fun _ => PUnit.unit, fun _ _ => PUnit.unit,
    fun x => funext (fun i => Subsingleton.elim (α := PUnit) _ (x i)), fun _ => rfl⟩
  basis _ := ⟨fun _ => PUnit.unit, fun _ _ => PUnit.unit,
    fun x => funext (fun i => Subsingleton.elim (α := PUnit) _ (x i)), fun _ => rfl⟩
  aug _ _ := by
    change 1 = ∏ _ : E, (1 : R)
    simp

/-- Right dependent unit compatibility with the Fubini shuffle. -/
theorem fubini_rightUnit {E : Type u} [Fintype E] (A : E → Family.{u,v} R) :
    occurrenceMap (fun i => (dependentRightUnit (A i)).hom) =
      (((fubini A (fun _ _ => unit R)).comp
        (DepHom.accumulate (S := fun _ => unit R)
          ⟨Hom.id (occurrence A), fun _ => occurrenceUnit.hom⟩))).comp
            (dependentRightUnit (occurrence A)).hom := by
  change occurrenceMap (fun i => (dependentRightUnit (A i)).hom) =
      ((fubini A (fun _ _ => unit R)).comp
        (DepHom.accumulate (S := fun _ => unit R)
          ⟨(Wiring.id (occurrence A)).hom, fun _ => occurrenceUnit.hom⟩)).comp
            (dependentRightUnit (occurrence A)).hom
  simp only [← fubiniWiring_hom, Wiring.occurrenceWiring_hom,
    Wiring.dependentWiring_hom, Wiring.hom_comp]
  exact Wiring.compare (R := R) _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- Left dependent unit compatibility with the Fubini shuffle. -/
theorem fubini_leftUnit {E : Type u} [Fintype E] (A : E → Family.{u,v} R) :
    occurrenceMap (fun i => (dependentLeftUnit (A i)).hom) =
      ((fubini (fun _ : E => unit R) (fun i _ => A i)).comp
        (DepHom.accumulate (S := fun _ => occurrence A)
          ⟨occurrenceUnit.hom, fun _ => Hom.id (occurrence A)⟩)).comp
            (dependentLeftUnit (occurrence A)).hom := by
  change occurrenceMap (fun i => (dependentLeftUnit (A i)).hom) =
      ((fubini (fun _ : E => unit R) (fun i _ => A i)).comp
        (DepHom.accumulate (S := fun _ => occurrence A)
          ⟨occurrenceUnit.hom, fun _ => (Wiring.id (occurrence A)).hom⟩)).comp
            (dependentLeftUnit (occurrence A)).hom
  simp only [← fubiniWiring_hom, Wiring.occurrenceWiring_hom,
    Wiring.dependentWiring_hom, Wiring.hom_comp]
  exact Wiring.compare (R := R) _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- Empty occurrence coherence uses two unit coefficients, not an empty family. -/
theorem fubini_empty {E : Type u} [Fintype E] [IsEmpty E]
    (A : E → Family.{u,v} R) (Q : ∀ i, (A i).Pos → Family.{u,v} R) :
    (occurrenceEmpty (fun i => dependent (A i) (Q i))).hom =
      ((fubini A Q).comp
        (DepHom.accumulate (S := fun _ => unit R)
          ⟨(occurrenceEmpty A).hom, fun x => (occurrenceEmpty (fun i => Q i (x i))).hom⟩)).comp
            (dependentRightUnit (unit R)).hom := by
  rw [unit_terminal _ ((occurrenceEmpty (fun i => dependent (A i) (Q i))).hom)]
  exact (unit_terminal _ _).symm

/-- Matrix of a basis map. No injectivity is needed for the column formula. -/
def basisMap {A B : Type u} (f : A → B) : Matrix B A R := by
  classical exact fun b a => if f a = b then 1 else 0

theorem mul_basisMap_left {A B C : Type u} [Fintype B]
    (f : A → B) (n : Matrix C B R) (c : C) (a : A) :
    mul (basisMap f) n c a = n c (f a) := by
  classical
  unfold mul basisMap
  rw [Fintype.sum_eq_single (f a)]
  · simp
  · intro b h
    simp [Ne.symm h]

namespace DepHom

variable {A B : Family.{u,v} R} {Q : A.Pos → Family.{u,v} R} {S : B.Pos → Family.{u,v} R}

/-- The source's intermediate sum after the inner arrow and before merging
outer branches. This sum still contains the original outer position tags. -/
abbrev Intermediate (m : DepHom Q S) (target : (dependent B S).Pos) :=
  Σ x : {x : A.Pos // m.outer.pos x = target.1},
    A.Basis x.1 × (S target.1).Basis target.2

/-- First apply each branch's actual inner coefficient arrow, putting its
output into the as-yet-unmerged outer summand. -/
def innerStageColumn (m : DepHom Q S) (xy : (dependent A Q).Pos) :
    Matrix (m.Intermediate (m.accumulate.pos xy)) ((dependent A Q).Basis xy) R :=
  mul (kron (perm (Equiv.refl (A.Basis xy.1))) ((m.inner xy.1).block xy.2))
    (basisMap (fun d => ⟨⟨xy.1,rfl⟩,d⟩))

def innerStage (m : DepHom Q S) (target : (dependent B S).Pos) :
    Matrix (m.Intermediate target)
      (Σ xy : {xy // m.accumulate.pos xy = target}, (dependent A Q).Basis xy.1) R :=
  fun d p => (p.1.2 ▸ m.innerStageColumn p.1.1) d p.2

/-- Only after the inner stage does the outer block combine the outer
summands, tensored with identity on the common target inner basis. -/
def outerStage (m : DepHom Q S) (target : (dependent B S).Pos) :
    Matrix ((dependent B S).Basis target) (m.Intermediate target) R :=
  fun b d => m.outer.native target.1 b.1 ⟨d.1, d.2.1⟩ *
    (perm (Equiv.refl ((S target.1).Basis target.2))) b.2 d.2.2

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual matrix on the full native target fibre factors in
the source's order, including when the original fibre is empty. This is
not merely a calculation on the augmentation of that fibre. -/
theorem accumulate_native_factor (m : DepHom Q S) (target : (dependent B S).Pos) :
    m.accumulate.native target = mul (m.innerStage target) (m.outerStage target) := by
  funext b p
  rcases p with ⟨⟨xy,h⟩,a⟩
  subst target
  change _ = mul (m.innerStageColumn xy) (m.outerStage (m.accumulate.pos xy)) b a
  let inj : A.Basis xy.1 × (S (m.outer.pos xy.1)).Basis ((m.inner xy.1).pos xy.2) →
      m.Intermediate (m.accumulate.pos xy) := fun d => ⟨⟨xy.1,rfl⟩,d⟩
  have hinj :
      mul (basisMap inj) (m.outerStage (m.accumulate.pos xy)) =
        kron (m.outer.block xy.1)
          (perm (Equiv.refl ((S (m.outer.pos xy.1)).Basis ((m.inner xy.1).pos xy.2)))) := by
    funext t d
    exact mul_basisMap_left inj _ t d
  change _ = mul
    (mul (kron (perm (Equiv.refl (A.Basis xy.1))) ((m.inner xy.1).block xy.2)) (basisMap inj))
    (m.outerStage (m.accumulate.pos xy)) b a
  rw [mul_assoc, hinj, mul_kron]
  change m.outer.block xy.1 b.1 a.1 * (m.inner xy.1).block xy.2 b.2 a.2 =
    mul (perm (Equiv.refl (A.Basis xy.1))) (m.outer.block xy.1) b.1 a.1 *
      mul ((m.inner xy.1).block xy.2)
         (perm (Equiv.refl ((S (m.outer.pos xy.1)).Basis ((m.inner xy.1).pos xy.2)))) b.2 a.2
  rw [mul_perm_left, mul_perm_right]
  rfl

end DepHom

end

end ContextualComposition.AugmentedMatrixFubini
