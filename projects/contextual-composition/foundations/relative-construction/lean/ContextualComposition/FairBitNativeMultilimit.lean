module

public import ContextualComposition.FairBitCouplingFamily
public import ContextualComposition.NativeMultilimitComparisons
public import ContextualComposition.ProbabilityPullbackGluing

/-! The interval family occurs among the actual component indices of a finite two-object native multilimit, with terminal coefficients. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.FairBitNativeMultilimit

open CategoryTheory CategoryTheory.Limits NativeMultilimits NativeFamilyCompletion FiniteProbabilityLaws IndependentProbabilityProduct AllCouplings

abbrev V := Discrete Unit
abbrev star : V := ⟨()⟩
abbrev F := raw.{0} V ⋙ distribution
def bit : Native distribution V := nativeMk distribution Bool coin.law (fun _ => star)
abbrev diagram : Discrete Bool ⥤ Native distribution V := Discrete.functor (fun _ => bit)

def pairFamily : FormalCoproduct.{0} V := ⟨Bool × Bool,fun _ => star⟩
def leg (i : Bool) : pairFamily ⟶ bit.obj :=
  ⟨fun p => if i then p.2 else p.1,fun _ => 𝟙 _⟩

def base : Cone (Base F diagram) := ⟨pairFamily,Discrete.natTrans (fun i => leg i.as)⟩

def baseLimit : IsLimit base where
  lift s := ⟨fun i => ((s.π.app ⟨false⟩).f i,(s.π.app ⟨true⟩).f i),
    fun i => eqToHom (Subsingleton.elim (s.pt.obj i) star)⟩
  fac s := by
    rintro ⟨i⟩
    apply (FormalCoproduct.hom_ext_iff' _ _).mpr; intro j
    cases i <;> exact ⟨rfl,Subsingleton.elim _ _⟩
  uniq s m eq := by
    apply (FormalCoproduct.hom_ext_iff' _ _).mpr; intro j
    exact ⟨Prod.ext (congrArg (fun f : s.pt ⟶ bit.obj => f.f j) (eq ⟨false⟩))
      (congrArg (fun f : s.pt ⟶ bit.obj => f.f j) (eq ⟨true⟩)),Subsingleton.elim _ _⟩

def indices : Index F diagram base ≃ Hom distribution coin coin where
  toFun t := ⟨t.val,t.property ⟨false⟩,t.property ⟨true⟩⟩
  invFun t := ⟨t.val,fun ⟨i⟩ => by cases i; exact t.property.1; exact t.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def component (x : Interval) : Index F diagram base := indices.symm (FairBitCouplingFamily.coupling x)

theorem interval_components : Function.Injective component := indices.symm.injective.comp FairBitCouplingFamily.coupled_interval

/-- The interval-valued choice is inside this binary categorical limit of singleton families. -/
def completedLimit : IsLimit (singletonCone F diagram base) := singletonIsLimit F diagram base baseLimit

/-- Quadrilateral uniqueness on probability effects would force every two fair-bit joint laws with these marginals to coincide. -/
theorem quadrilateral_failure : ¬ CouplingPullbacks.QuadBijective distribution.{0} := by
  intro quad
  let a : Interval := ⟨0,by constructor <;> norm_num⟩
  let b : Interval := ⟨1,by constructor <;> norm_num⟩
  let u := FairBitCouplingFamily.coupling a
  let v := FairBitCouplingFamily.coupling b
  have e : u.val = v.val := by
    apply (CouplingPullbacks.pair_of_quad distribution ProbabilityPullbackGluing.weak quad Bool Bool).injective
    apply Subtype.ext; apply Prod.ext
    · exact (CouplingPullbacks.pair_left distribution u.val).trans (u.property.1.trans
        (v.property.1.symm.trans (CouplingPullbacks.pair_left distribution v.val).symm))
    · exact (CouplingPullbacks.pair_right distribution u.val).trans (u.property.2.trans
        (v.property.2.symm.trans (CouplingPullbacks.pair_right distribution v.val).symm))
  exact zero_ne_one (congrArg Subtype.val (FairBitCouplingFamily.coupled_interval (show u=v from Subtype.ext e)))

end ContextualComposition.FairBitNativeMultilimit
