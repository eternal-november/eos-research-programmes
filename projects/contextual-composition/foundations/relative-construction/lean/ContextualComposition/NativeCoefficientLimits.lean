module

public import ContextualComposition.NativeFamilyCompletion

/-! Limits in the coefficient-family base built on the full compatible raw tuple set and on a genuine coefficient diagram at each tuple. This exhibits the specific cone used in the native multilimit formula. -/

@[expose] public section
namespace ContextualComposition.NativeCoefficientLimits

open CategoryTheory CategoryTheory.Limits NativeMultilimits NativeFamilyCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u v
variable {V : Type u} [Category.{v} V] {J : Type w} [Category.{w} J]

/-- The component of a family map, transported to a specified equal target index. -/
def atIndex {P Q : FormalCoproduct.{w} V} (f : P ⟶ Q) (i : P.I) (j : Q.I) (h : f.f i = j) :
    P.obj i ⟶ Q.obj j := f.φ i ≫ eqToHom (congrArg Q.obj h)

theorem at_same {P Q : FormalCoproduct.{w} V} (f : P ⟶ Q) (i : P.I) :
    atIndex f i (f.f i) rfl = f.φ i := by simp [atIndex]

theorem at_equal {P Q : FormalCoproduct.{w} V} {f g : P ⟶ Q} (e : f = g) (i j) (h : f.f i = j) (k : g.f i = j) :
    atIndex f i j h = atIndex g i j k := by cases e; rfl

theorem at_comp {P Q R : FormalCoproduct.{w} V} (f : P ⟶ Q) (g : Q ⟶ R) (i j k)
    (e : f.f i = j) (h : g.f j = k) :
    atIndex (f ≫ g) i k (congrArg g.f e |>.trans h) = atIndex f i j e ≫ atIndex g j k h := by
  subst j; subst k; simp [atIndex]

variable (D : J ⥤ FormalCoproduct.{w} V)

abbrev Tuple := {t : ∀ i, (D.obj i).I // ∀ {i j} (f : i ⟶ j), (D.map f).f (t i) = t j}

def coefficients (z : Tuple D) : J ⥤ V where
  obj i := (D.obj i).obj (z.val i)
  map f := atIndex (D.map f) _ _ (z.property f)
  map_id i := (at_equal (D.map_id i) (z.val i) _ _ rfl).trans (at_same (𝟙 (D.obj i)) _)
  map_comp f g := (at_equal (D.map_comp f g) _ _ _ _).trans (at_comp _ _ _ _ _ (z.property f) (z.property g))

def tupleOfCone (a : Cone D) (i : a.pt.I) : Tuple D :=
  ⟨fun j => (a.π.app j).f i,fun f => congrArg (fun g => g.f i) (a.w f)⟩

def pointCone (a : Cone D) (i : a.pt.I) : Cone (coefficients D (tupleOfCone D a i)) where
  pt := a.pt.obj i
  π := {
    app := fun j => (a.π.app j).φ i
    naturality := by
      intro j k f
      refine (Category.id_comp _).trans ?_
      let z := tupleOfCone D a i
      exact ((at_same _ _).symm.trans ((at_equal (a.w f).symm i (z.val k) rfl _).trans
        (at_comp (a.π.app j) (D.map f) i (z.val j) (z.val k) rfl (z.property f)))).trans
          (congrArg (· ≫ (coefficients D z).map f) (at_same (a.π.app j) i)) }

variable [∀ z : Tuple D, HasLimit (coefficients D z)]

noncomputable def baseCone : Cone D where
  pt := ⟨Tuple D,fun z => limit (coefficients D z)⟩
  π := {
    app := fun j => ⟨fun z => z.val j,fun z => limit.π (coefficients D z) j⟩
    naturality := by
      intro i j f
      refine (Category.id_comp _).trans ?_
      symm
      apply (FormalCoproduct.hom_ext_iff' _ _).mpr
      intro z
      refine ⟨z.property f,?_⟩
      exact (Category.assoc _ _ _).trans (limit.w (coefficients D z) f) }

noncomputable def lift (a : Cone D) : a.pt ⟶ (baseCone D).pt :=
  ⟨tupleOfCone D a,fun i => limit.lift _ (pointCone D a i)⟩

private theorem projection_transport {z z' : Tuple D} (h : z = z') (j : J) :
    eqToHom (congrArg (fun t => limit (coefficients D t)) h) ≫ limit.π (coefficients D z') j =
    limit.π (coefficients D z) j ≫ eqToHom (congrArg (fun t : Tuple D => (D.obj j).obj (t.val j)) h) := by
  subst z'; simp

noncomputable def baseIsLimit : IsLimit (baseCone D) where
  lift := lift D
  fac a j := by
    apply (components _ _).injective
    funext i
    exact congrArg (Sigma.mk _) (limit.lift_π (pointCone D a i) j)
  uniq a f hf := by
    apply (FormalCoproduct.hom_ext_iff' _ _).mpr
    intro i
    have eq : f.f i = tupleOfCone D a i := by
      apply Subtype.ext; funext j
      exact congrArg (fun g => g.f i) (hf j)
    refine ⟨eq,?_⟩
    apply limit.hom_ext
    intro j
    have h := (FormalCoproduct.hom_ext_iff' _ _).mp (hf j) i
    exact (Category.assoc (f.φ i) _ _).trans ((congrArg (f.φ i ≫ ·) (projection_transport D eq j)).trans
      ((Category.assoc (f.φ i) _ _).symm.trans (h.choose_spec.trans (limit.lift_π (pointCone D a i) j).symm)))

/-- Specializing the categories-of-elements multilimit gives the required tuple carrier, the pointwise coefficient limits, and every compatible root effect. -/
noncomputable def nativeTupleMultilimit (T : Type w ⥤ Type w) (E : J ⥤ Native T V)
    [∀ z : Tuple (Base (raw V ⋙ T) E), HasLimit (coefficients (Base (raw V ⋙ T) E) z)] (A : Native T V) :
    (Σ (t : Index (raw V ⋙ T) E (baseCone (Base (raw V ⋙ T) E))),
      A ⟶ joint (raw V ⋙ T) E (baseCone (Base (raw V ⋙ T) E)) t) ≃ FixedCone E A :=
  multilimit _ E _ (baseIsLimit _) A

end ContextualComposition.NativeCoefficientLimits
