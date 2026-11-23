module
public import ContextualComposition.NativeDependentPairArrow
@[expose] public section

/-! Accumulation of unpresented native families, with an exact comparison
to the dependent-sum carrier and coefficient objects of the manuscript. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)

namespace NativeDependentPair
variable (A : NativeDependentPair I)

abbrev Branch := (x : Fin A.parent.base.n) × Fin (A.child x).base.n

def rawBranch (x : A.Branch) : A.ordered.X × A.ordered.U := (⟨x.1⟩, A.childTag x.1 x.2)

theorem rawBranch_mem (x : A.Branch) : A.rawBranch x ∈ dependentWord A.ordered.xs A.ordered.us := by
  apply (dependentWord_mem _ _ _).mpr
  exact ⟨List.mem_map.mpr ⟨x.1,List.mem_finRange _,rfl⟩,
    List.mem_map.mpr ⟨x.2,List.mem_finRange _,rfl⟩⟩

theorem rawBranch_inj : Function.Injective A.rawBranch := by
  intro ⟨x,i⟩ ⟨y,j⟩ h
  have e : x = y := congrArg (fun z : A.ordered.X × A.ordered.U => z.1.down) h
  subst y
  have e' : A.childTag x i = A.childTag x j := congrArg (fun z : A.ordered.X × A.ordered.U => z.2) h
  have k := (A.childView x).tag_injective e'
  subst j
  rfl

noncomputable def rawBranchEquiv :
    A.Branch ≃ {z // z ∈ dependentWord A.ordered.xs A.ordered.us} :=
  Equiv.ofBijective (fun z => ⟨A.rawBranch z,A.rawBranch_mem z⟩) (by
    constructor
    · exact fun x y h => A.rawBranch_inj (congrArg Subtype.val h)
    · intro ⟨⟨x,y⟩,hy⟩
      have h := (dependentWord_mem A.ordered.xs A.ordered.us (x,y)).mp hy
      obtain ⟨i,_,e⟩ := List.mem_map.mp h.2
      refine ⟨⟨x.down,i⟩,Subtype.ext ?_⟩
      exact Prod.ext (by cases x; rfl) e)

noncomputable def accumulate : Aug ℙ I := A.ordered.accumulate R L J

/-- Exact extension reassociation, with no ordering choice in the
dependent-sum target. -/
noncomputable def readBranch : Fin (A.accumulate R L J).base.n ≃ A.Branch :=
  (wordPositions (dependentWord A.ordered.xs A.ordered.us)
    (dependentWord_nodup A.ordered.xs_unique A.ordered.us_unique)).trans A.rawBranchEquiv.symm

set_option backward.isDefEq.respectTransparency false in
theorem read_rawBranch (i : Fin (A.accumulate R L J).base.n) :
    A.rawBranch (A.readBranch R L J i) = (dependentWord A.ordered.xs A.ordered.us)[i] := by
  let t := wordPositions (dependentWord A.ordered.xs A.ordered.us)
    (dependentWord_nodup A.ordered.xs_unique A.ordered.us_unique)
  exact congrArg Subtype.val (A.rawBranchEquiv.apply_symm_apply (t i))

set_option backward.isDefEq.respectTransparency false in
theorem read_coef (i : Fin (A.accumulate R L J).base.n) :
    let z := A.readBranch R L J i
    (A.accumulate R L J).base.val i = T.obj (A.parent.base.val z.1) ((A.child z.1).base.val z.2) :=
  congrArg (dependentLabels (T:=T) A.ordered.V A.ordered.A) (A.read_rawBranch R L J i).symm

end NativeDependentPair

namespace NativeDependentPairHom
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
variable {A B : NativeDependentPair I} (p : NativeDependentPairHom A B)

noncomputable def accumulate : AugHom ℙ (A.accumulate R L J) (B.accumulate R L J) :=
  p.ordered.accumulate R L J N NL hl

def branchMap (z : A.Branch) : B.Branch :=
  ⟨p.parent.native.addr z.1, (p.child z.1).native.addr z.2⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem read_addr (i : Fin (A.accumulate R L J).base.n) :
    B.readBranch R L J ((p.accumulate R L J N NL hl).native.addr i) =
      p.branchMap (A.readBranch R L J i) := by
  letI := B.ordered.eqX
  letI := B.ordered.eqU
  let D := p.ordered.map
  let xs := dependentWord A.ordered.xs A.ordered.us
  let ys := dependentWord B.ordered.xs B.ordered.us
  let j := (p.accumulate R L J N NL hl).native.addr i
  let z := A.readBranch R L J i
  have h : ys[j] = origDepCarrier D xs[i] :=
    wordCarrier_get (origDepCarrier D) (origDepCarrier_support D)
      (dependentWord_nodup B.ordered.xs_unique B.ordered.us_unique) i
  have e (v : A.Branch) : origDepCarrier D (A.rawBranch v) = B.rawBranch (p.branchMap v) := by
    rcases v with ⟨x,y⟩
    exact Prod.ext rfl (p.childFunction_tag x y)
  apply B.rawBranch_inj
  exact (B.read_rawBranch R L J j).trans (h.trans
    ((congrArg (origDepCarrier D) (A.read_rawBranch R L J i).symm).trans (e z)))

end NativeDependentPairHom
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
