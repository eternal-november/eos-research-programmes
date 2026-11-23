module
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! Strict and strong maps in the terminal-base case of the telescope
comparison. A normalized nontrivial C₂-valued cocycle gives the identity
functor a coherent tensorator which no compatible 2-cell carries to
identity comparisons. -/

@[expose] public section
namespace ContextualComposition.TelescopeTensoratorObstruction
open CategoryTheory MonoidalCategory

structure Grade where
  value : Bool
  deriving DecidableEq

structure Arrow (x y : Grade) where
  same : x = y
  phase : Bool

@[ext] theorem arrow_ext {x y : Grade} {f g : Arrow x y} (p : f.phase = g.phase) : f = g := by
  cases f; cases g; cases p; rfl

instance : Category Grade where
  Hom := Arrow
  id _ := ⟨rfl,false⟩
  comp f g := ⟨f.same.trans g.same,f.phase ^^ g.phase⟩
  id_comp f := by apply arrow_ext; exact Bool.false_xor _
  comp_id f := by apply arrow_ext; exact Bool.xor_false _
  assoc f g h := by apply arrow_ext; exact Bool.xor_assoc _ _ _

def sum (x y : Grade) : Grade := ⟨x.value ^^ y.value⟩
def zero : Grade := ⟨false⟩

def changeGrade {x y : Grade} (h : x = y) (bit : Bool) : x ≅ y where
  hom := ⟨h,bit⟩
  inv := ⟨h.symm,bit⟩
  hom_inv_id := by apply arrow_ext; exact Bool.xor_self _
  inv_hom_id := by apply arrow_ext; exact Bool.xor_self _

instance : MonoidalCategory Grade where
  tensorObj := sum
  tensorHom f g := ⟨congrArg₂ sum f.same g.same,f.phase ^^ g.phase⟩
  whiskerLeft x {_ _} f := ⟨congrArg (sum x) f.same,f.phase⟩
  whiskerRight f x := ⟨congrArg (sum · x) f.same,f.phase⟩
  tensorUnit := zero
  associator x y z := changeGrade (by cases x; cases y; cases z; simp [sum]) false
  leftUnitor x := changeGrade (by cases x; simp [sum,zero]) false
  rightUnitor x := changeGrade (by cases x; simp [sum,zero]) false
  tensorHom_def f g := rfl
  id_tensorHom_id _ _ := rfl
  tensorHom_comp_tensorHom f g h k := by
    apply arrow_ext
    change ((f.phase ^^ g.phase) ^^ (h.phase ^^ k.phase)) = ((f.phase ^^ h.phase) ^^ (g.phase ^^ k.phase))
    cases f.phase <;> cases g.phase <;> cases h.phase <;> cases k.phase <;> rfl
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality f g h := by
    apply arrow_ext
    change (((f.phase ^^ g.phase) ^^ h.phase) ^^ false) = (false ^^ (f.phase ^^ (g.phase ^^ h.phase)))
    simp
  leftUnitor_naturality f := by apply arrow_ext; exact (Bool.xor_false _).trans (Bool.false_xor _).symm
  rightUnitor_naturality f := by apply arrow_ext; exact (Bool.xor_false _).trans (Bool.false_xor _).symm
  pentagon _ _ _ _ := by apply arrow_ext; rfl
  triangle _ _ := by apply arrow_ext; rfl

def cocycle (x y : Grade) := x.value && y.value

/-- All grade-changing and tensor operations have actual natural invertible
comparisons. Over a terminal base these are the ordinary strong monoidal
functor equations of the strict contextad with this apex. -/
def twist : (𝟭 Grade).CoreMonoidal where
  εIso := Iso.refl _
  μIso x y := changeGrade rfl (cocycle x y)
  μIso_hom_natural_left {x y} f t := by
    obtain ⟨rfl,k⟩ := f
    apply arrow_ext
    exact Bool.xor_comm _ _
  μIso_hom_natural_right {x y} t f := by
    obtain ⟨rfl,k⟩ := f
    apply arrow_ext
    exact Bool.xor_comm _ _
  associativity x y z := by
    apply arrow_ext
    cases x with | mk x =>
      cases y with | mk y =>
        cases z with | mk z =>
          cases x <;> cases y <;> cases z <;> rfl
  left_unitality x := by apply arrow_ext; cases x with | mk x => cases x <;> rfl
  right_unitality x := by apply arrow_ext; cases x with | mk x => cases x <;> rfl

/-- The two compatibility equations for a monoidal natural transformation,
written with the two comparison structures supplied explicitly. -/
def Compatible {F G : Grade ⥤ Grade} (f : F.CoreMonoidal) (g : G.CoreMonoidal) (t : F ⟶ G) : Prop :=
  f.εIso.hom ≫ t.app (𝟙_ Grade) = g.εIso.hom ∧
    ∀ x y, (f.μIso x y).hom ≫ t.app (x ⊗ y) = (t.app x ⊗ₘ t.app y) ≫ (g.μIso x y).hom

theorem compatible_iff {F G : Grade ⥤ Grade} (f : F.CoreMonoidal) (g : G.CoreMonoidal) (t : F ⟶ G) :
    let _ := f.toLaxMonoidal
    let _ := g.toLaxMonoidal
    Compatible f g t ↔ t.IsMonoidal := by
  let _ := f.toLaxMonoidal
  let _ := g.toLaxMonoidal
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.unit,h.tensor⟩⟩

theorem eqToHom_phase {x y : Grade} (e : x = y) : (eqToHom e).phase = false := by cases e; rfl

/-- Every identity comparison, including an identity transported along
an object equality, has phase false. The result allows arbitrary target
functors with this property. -/
theorem no_strict_comparison {F : Grade ⥤ Grade} (k : F.CoreMonoidal)
    (unitPhase : k.εIso.hom.phase = false) (tensorPhase : ∀ x y, (k.μIso x y).hom.phase = false) :
    ¬ ∃ t : 𝟭 Grade ⟶ F, Compatible twist k t := by
  rintro ⟨t,hu,ht⟩
  have e := congrArg Arrow.phase hu
  change (false ^^ (t.app zero).phase) = _ at e
  rw [Bool.false_xor,unitPhase] at e
  let x : Grade := ⟨true⟩
  have bad := congrArg Arrow.phase (ht x x)
  change (true ^^ (t.app zero).phase) = (((t.app x).phase ^^ (t.app x).phase) ^^ (k.μIso x x).hom.phase) at bad
  rw [e,tensorPhase,Bool.xor_self] at bad
  contradiction

end ContextualComposition.TelescopeTensoratorObstruction
