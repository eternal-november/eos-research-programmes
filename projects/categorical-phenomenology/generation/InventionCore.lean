import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Group.Action.Pi

/-!
# Retained symmetry resources: a formal algebraic core

For a group `G` acting on `X`, `Y`, and a transitive token space `C`, choosing a
point `p : C` identifies token-preserving equivariant operations
`X × C → Y × C` with maps `X → Y` equivariant under the stabilizer of `p`.

The theorem is about sets with group actions. It does not assert that a token
can be physically acquired, or that a chosen set map has a physical realizer.
Neither finiteness nor a normal subgroup is assumed.
-/

namespace InventionCore

universe uG uX uY uC
variable {G : Type uG} [Group G]
variable {X : Type uX} {Y : Type uY} {C : Type uC}
variable [MulAction G X] [MulAction G Y] [MulAction G C]

/-- A map respecting precisely the symmetries that fix a specified token. -/
structure StabilizerMap (G : Type uG) [Group G] (X : Type uX) (Y : Type uY)
    (C : Type uC) [MulAction G X] [MulAction G Y] [MulAction G C] (p : C) where
  toFun : X → Y
  equivariant : ∀ (g : G) (x : X), g • p = p → toFun (g • x) = g • toFun x

/-- An equivariant operation whose token output equals its token input. -/
structure RetainedOperation (G : Type uG) [Group G] (X : Type uX) (Y : Type uY)
    (C : Type uC) [MulAction G X] [MulAction G Y] [MulAction G C] where
  toFun : X × C → Y × C
  equivariant : ∀ (g : G) (z : X × C), toFun (g • z) = g • toFun z
  retained : ∀ z, (toFun z).2 = z.2

@[ext] theorem StabilizerMap.ext {p : C} {f k : StabilizerMap G X Y C p}
    (h : ∀ x, f.toFun x = k.toFun x) : f = k := by
  cases f
  cases k
  simp_all only [mk.injEq]
  exact funext h

@[ext] theorem RetainedOperation.ext {F K : RetainedOperation G X Y C}
    (h : ∀ z, F.toFun z = K.toFun z) : F = K := by
  cases F
  cases K
  simp_all only [mk.injEq]
  exact funext h

/-- Evaluate an operation at the chosen token. -/
def restrict (p : C) (F : RetainedOperation G X Y C) : StabilizerMap G X Y C p where
  toFun x := (F.toFun (x, p)).1
  equivariant g x hg := by
    have h := congrArg Prod.fst (F.equivariant g (x, p))
    simpa [hg] using h

/-- Transport a stabilizer-equivariant map along a proposed frame `g`. -/
def transport {p : C} (f : StabilizerMap G X Y C p) (g : G) (x : X) : Y :=
  g • f.toFun (g⁻¹ • x)

/-- Different representatives of the same token give identical transported maps. -/
theorem transport_independent {p : C} (f : StabilizerMap G X Y C p)
    (a b : G) (hab : a • p = b • p) (x : X) :
    transport f a x = transport f b x := by
  have hs : (b⁻¹ * a) • p = p := by
    rw [mul_smul, hab, inv_smul_smul]
  have he := f.equivariant (b⁻¹ * a) (a⁻¹ • x) hs
  have he' : f.toFun (b⁻¹ • x) = (b⁻¹ * a) • f.toFun (a⁻¹ • x) := by
    simpa [mul_smul] using he
  simp only [transport]
  rw [he', smul_smul]
  simp

/-- Simultaneously moving the frame and the input moves the output. -/
theorem transport_mul {p : C} (f : StabilizerMap G X Y C p)
    (g a : G) (x : X) : transport f (g * a) (g • x) = g • transport f a x := by
  simp [transport, mul_smul]

/-- A selected frame for every token. This is a set-theoretic choice, not acquisition. -/
noncomputable def frame (p : C) (transitive : ∀ c : C, ∃ g : G, g • p = c) (c : C) : G :=
  Classical.choose (transitive c)

theorem frame_spec (p : C) (transitive : ∀ c : C, ∃ g : G, g • p = c) (c : C) :
    frame p transitive c • p = c :=
  Classical.choose_spec (transitive c)

/-- Extend a stabilizer map to an operation carrying its token unchanged. -/
noncomputable def extend (p : C) (transitive : ∀ c : C, ∃ g : G, g • p = c)
    (f : StabilizerMap G X Y C p) : RetainedOperation G X Y C where
  toFun z := (transport f (frame p transitive z.2) z.1, z.2)
  retained z := rfl
  equivariant g z := by
    apply Prod.ext
    · change transport f (frame p transitive (g • z.2)) (g • z.1) =
          g • transport f (frame p transitive z.2) z.1
      calc
        _ = transport f (g * frame p transitive z.2) (g • z.1) := by
          apply transport_independent
          simp [mul_smul, frame_spec]
        _ = _ := transport_mul f g _ z.1
    · rfl

@[simp] theorem restrict_extend (p : C)
    (transitive : ∀ c : C, ∃ g : G, g • p = c) (f : StabilizerMap G X Y C p) :
    restrict p (extend p transitive f) = f := by
  ext x
  change transport f (frame p transitive p) x = f.toFun x
  calc
    _ = transport f 1 x := transport_independent f _ _ (by simp [frame_spec]) x
    _ = _ := by simp [transport]

@[simp] theorem extend_restrict (p : C)
    (transitive : ∀ c : C, ∃ g : G, g • p = c) (F : RetainedOperation G X Y C) :
    extend p transitive (restrict p F) = F := by
  apply RetainedOperation.ext
  intro z
  apply Prod.ext
  · change transport (restrict p F) (frame p transitive z.2) z.1 = (F.toFun z).1
    let g := frame p transitive z.2
    have hg : g • p = z.2 := frame_spec p transitive z.2
    have he := congrArg Prod.fst (F.equivariant g (g⁻¹ • z.1, p))
    simpa [transport, restrict, hg] using he.symm
  · exact (F.retained z).symm

/-- Main theorem: retained transitive tokens remove exactly their broken symmetries. -/
noncomputable def retainedOperationEquiv (p : C)
    (transitive : ∀ c : C, ∃ g : G, g • p = c) :
    RetainedOperation G X Y C ≃ StabilizerMap G X Y C p where
  toFun := restrict p
  invFun := extend p transitive
  left_inv := extend_restrict p transitive
  right_inv := restrict_extend p transitive

/-- Stabilizer equivariance at the identity coset is exactly `H`-equivariance. -/
def quotientStabilizerEquiv (H : Subgroup G) :
    StabilizerMap G X Y (G ⧸ H) ((1 : G) : G ⧸ H) ≃ (X →[H] Y) where
  toFun f := {
    toFun := f.toFun
    map_smul' := fun h x => f.equivariant h x (by
      have hh : (h : G) ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
        simpa only [MulAction.stabilizer_quotient] using h.property
      exact hh) }
  invFun f := {
    toFun := f
    equivariant := fun g x hg => by
      have hmem : g ∈ H := by
        rw [← MulAction.stabilizer_quotient H]
        exact hg
      exact f.map_smul ⟨g, hmem⟩ x }
  left_inv f := by apply StabilizerMap.ext; intro x; rfl
  right_inv f := by apply MulActionHom.ext; intro x; rfl

/-- Coset form of the main theorem, using mathlib's actual `H`-equivariant maps.
The subgroup need not be normal and the group need not be finite. -/
noncomputable def cosetRetainedOperationEquiv (H : Subgroup G) :
    RetainedOperation G X Y (G ⧸ H) ≃ (X →[H] Y) :=
  (retainedOperationEquiv ((1 : G) : G ⧸ H)
    (fun c => MulAction.exists_smul_eq G _ c)).trans (quotientStabilizerEquiv H)

/-- Retained operations compose without resetting or reselecting their token. -/
def RetainedOperation.comp {Z : Type*} [MulAction G Z]
    (K : RetainedOperation G Y Z C) (F : RetainedOperation G X Y C) :
    RetainedOperation G X Z C where
  toFun z := K.toFun (F.toFun z)
  equivariant g z := by rw [F.equivariant, K.equivariant]
  retained z := by rw [K.retained, F.retained]

/-- Stabilizer-equivariant maps compose. -/
def StabilizerMap.comp {Z : Type*} [MulAction G Z] {p : C}
    (k : StabilizerMap G Y Z C p) (f : StabilizerMap G X Y C p) :
    StabilizerMap G X Z C p where
  toFun x := k.toFun (f.toFun x)
  equivariant g x hg := by rw [f.equivariant g x hg, k.equivariant g _ hg]

/-- Evaluation respects sequential composition, not just individual operations. -/
theorem restrict_comp {Z : Type*} [MulAction G Z] (p : C)
    (K : RetainedOperation G Y Z C) (F : RetainedOperation G X Y C) :
    restrict p (K.comp F) = (restrict p K).comp (restrict p F) := by
  apply StabilizerMap.ext
  intro x
  change (K.toFun (F.toFun (x, p))).1 =
    (K.toFun ((F.toFun (x, p)).1, p)).1
  have hp : F.toFun (x, p) = ((F.toFun (x, p)).1, p) :=
    Prod.ext rfl (F.retained (x, p))
  rw [hp]

/-- Exact boundary for eliminating the token: the map obtained at the base token
is globally equivariant iff the operation's value is independent of the token. -/
theorem globally_equivariant_iff_token_independent (p : C)
    (transitive : ∀ c : C, ∃ g : G, g • p = c) (F : RetainedOperation G X Y C) :
    (∀ (g : G) (x : X), (restrict p F).toFun (g • x) =
      g • (restrict p F).toFun x) ↔
    (∀ (x : X) (c d : C), (F.toFun (x, c)).1 = (F.toFun (x, d)).1) := by
  constructor
  · intro hf
    have hc (x : X) (c : C) : (F.toFun (x, c)).1 = (restrict p F).toFun x := by
      obtain ⟨g, hg⟩ := transitive c
      have he := congrArg Prod.fst (F.equivariant g (g⁻¹ • x, p))
      calc
        _ = g • (restrict p F).toFun (g⁻¹ • x) := by
          simpa [restrict, hg] using he
        _ = _ := by simpa using (hf g (g⁻¹ • x)).symm
    intro x c d
    exact (hc x c).trans (hc x d).symm
  · intro hi g x
    change (F.toFun (g • x, p)).1 = g • (F.toFun (x, p)).1
    calc
      _ = (F.toFun (g • x, g • p)).1 := hi _ _ _
      _ = _ := by simpa using congrArg Prod.fst (F.equivariant g (x, p))

/-- In cartesian set semantics, a reference can be read while retaining it.
This is a set-level construction; physical copying or realization is not asserted. -/
def copyToken : RetainedOperation G X C C where
  toFun z := (z.2, z.2)
  equivariant _ _ := rfl
  retained _ := rfl

/-- Equivariance sends an invariant source point to an invariant output point. -/
theorem invariant_output_of_invariant_source (f : X → C)
    (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (x : X) (hx : ∀ g : G, g • x = x) : ∀ g : G, g • f x = f x := by
  intro g
  rw [← hf, hx]

/-- A nontrivial transitive token cannot be extracted equivariantly from an invariant point. -/
theorem no_equivariant_token_from_invariant_source [Nontrivial C]
    (transitive : ∀ c d : C, ∃ g : G, g • c = d)
    (x : X) (hx : ∀ g : G, g • x = x) :
    ¬ ∃ f : X → C, ∀ (g : G) (z : X), f (g • z) = g • f z := by
  rintro ⟨f, hf⟩
  have hi := invariant_output_of_invariant_source f hf x hx
  obtain ⟨c, hc⟩ := exists_ne (f x)
  obtain ⟨g, hg⟩ := transitive (f x) c
  exact hc (hg.symm.trans (hi g))

/-- Proper subgroups give precisely the nontrivial coset-token no-go case. -/
theorem no_coset_token_from_invariant_source (H : Subgroup G) (hH : H ≠ ⊤)
    (x : X) (hx : ∀ g : G, g • x = x) :
    ¬ ∃ f : X → G ⧸ H, ∀ (g : G) (z : X), f (g • z) = g • f z := by
  let : Nontrivial (G ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  exact no_equivariant_token_from_invariant_source
    (fun c d => MulAction.exists_smul_eq G c d) x hx

/-- A concrete strict expressibility witness: the reference can be output and
retained when supplied, but cannot be produced from an invariant source alone. -/
theorem strict_reference_capability [Nontrivial C]
    (transitive : ∀ c d : C, ∃ g : G, g • c = d)
    (x : X) (hx : ∀ g : G, g • x = x) :
    (∃ F : RetainedOperation G X C C, ∀ z, F.toFun z = (z.2, z.2)) ∧
    (¬ ∃ f : X → C, ∀ (g : G) (z : X), f (g • z) = g • f z) := by
  exact ⟨⟨copyToken, fun _ => rfl⟩,
    no_equivariant_token_from_invariant_source transitive x hx⟩

/-- Retaining a family of references leaves exactly the intersection of their
stabilizers. This concerns the resource after acquisition, not its source. -/
theorem stabilizer_family {ι : Type*} {D : ι → Type*}
    [∀ i, MulAction G (D i)] (p : ∀ i, D i) :
    MulAction.stabilizer G p = ⨅ i, MulAction.stabilizer G (p i) := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_iInf, funext_iff,
    Pi.smul_apply]

/-- Strict subgroup shrinkage has a separating classifier on the same input and
output sorts: membership in `K` is `K`-invariant but not `H`-invariant.
The displayed equations are equivariance for the trivial action on `Bool`. -/
theorem strict_subgroup_indicator (K H : Subgroup G) (hKH : K < H) :
    ∃ f : G → Bool,
      (∀ k ∈ K, ∀ x : G, f (k * x) = f x) ∧
      ¬ (∀ h ∈ H, ∀ x : G, f (h * x) = f x) := by
  classical
  have hex : ∃ h : G, h ∈ H ∧ h ∉ K := by
    by_contra hn
    have hle : H ≤ K := by
      intro h hh
      by_contra hk
      exact hn ⟨h, hh, hk⟩
    exact (not_le_of_gt hKH) hle
  obtain ⟨h, hhH, hhK⟩ := hex
  let f : G → Bool := fun x => decide (x ∈ K)
  refine ⟨f, ?_, ?_⟩
  · intro k hk x
    simp [f, K.mul_mem_cancel_left hk]
  · intro hf
    have bad := hf h hhH 1
    simp [f, hhK] at bad

end InventionCore

#print axioms InventionCore.retainedOperationEquiv
#print axioms InventionCore.no_equivariant_token_from_invariant_source

#print axioms InventionCore.cosetRetainedOperationEquiv

#print axioms InventionCore.restrict_comp
#print axioms InventionCore.no_coset_token_from_invariant_source
#print axioms InventionCore.strict_reference_capability

#print axioms InventionCore.globally_equivariant_iff_token_independent

#print axioms InventionCore.stabilizer_family
#print axioms InventionCore.strict_subgroup_indicator
