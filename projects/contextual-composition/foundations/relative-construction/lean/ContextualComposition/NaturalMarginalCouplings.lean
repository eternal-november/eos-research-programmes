module

public import ContextualComposition.FiniteProbabilityLaws
public import ContextualComposition.IntervalAdditivity

/-! Independently natural coupling of two extensional finite-support laws is forced to multiply point masses. Additivity is proved through the three indicator images of one supplied three-by-two law. -/

@[expose] public section
noncomputable section

namespace ContextualComposition.NaturalMarginalCouplings

open FiniteProbabilityLaws
universe u
structure Choice where
  couple : {X Y : Type u} → Law X → Law Y → Law (X × Y)
  fst : ∀ {X Y} (p : Law X) (q : Law Y), image Prod.fst (couple p q) = p
  snd : ∀ {X Y} (p : Law X) (q : Law Y), image Prod.snd (couple p q) = q
  natural : ∀ {X Y X' Y'} (f : X → X') (g : Y → Y') (p : Law X) (q : Law Y),
    image (Prod.map f g) (couple p q) = couple (image f p) (image g q)

variable (c : Choice.{0})

def corner (v : Interval) (x : ℝ) := if h : x ∈ Set.Icc (0:ℝ) 1 then
  (c.couple (bern ⟨x,h⟩) (bern v)).mass (true,true) else 0

private theorem as_corner (v : Interval) (p : Law Bool) :
    (c.couple p (bern v)).mass (true,true) = corner c v (p.mass true) := by
  simp only [corner, dite_eq_left (show p.mass true ∈ Set.Icc (0:ℝ) 1 from ⟨point_nonneg p _,point_le_one p _⟩)]
  exact congrArg (fun t => (c.couple t (bern v)).mass (true,true)) (as_bern p)

theorem slice {X : Type} (v : Interval) (p : Law X) (f : X → Bool) :
    corner c v (expect p (test f)) = expect (c.couple p (bern v)) (test (fun z => f z.1 && z.2)) := by
  rw [← push_test,← as_corner]
  have h := c.natural f id p (bern v)
  rw [image_id] at h
  exact (congrArg (fun t : Law (Bool × Bool) => t.mass (true,true)) h.symm).trans (push_joint_test _ f id)

private def first : Three → Bool | .first => true | _ => false
private def second : Three → Bool | .second => true | _ => false
private def either (a : Three) := first a || second a

theorem corner_add (v : Interval) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x+y ≤ 1) :
    corner c v (x+y) = corner c v x + corner c v y := by
  let m := three x y hx hy h
  have a : expect m (test first) = x := by simp [m,expect_three,test,first]
  have b : expect m (test second) = y := by simp [m,expect_three,test,second]
  have d : expect m (test either) = x+y := by simp [m,expect_three,test,either,first,second]
  rw [← a,← b]
  calc
    corner c v (_ + _) = corner c v (expect m (test either)) := by rw [a,b,d]
    _ = _ := slice c v m either
    _ = expect (c.couple m (bern v)) (fun z =>
        test (fun z : Three × Bool => first z.1 && z.2) z + test (fun z : Three × Bool => second z.1 && z.2) z) := by
      apply expect_congr; rintro ⟨i,j⟩; cases i <;> cases j <;> simp [test,either,first,second]
    _ = _ := (expect_add _ _ _).trans (congrArg₂ (· + ·) (slice c v m first).symm (slice c v m second).symm)

theorem corner_one (v : Interval) : corner c v 1 = v.val := by
  let p := bern v
  let f : Bool → Bool := fun _ => true
  have one : expect p (test f) = 1 := expect_one p
  rw [← one,slice]
  change expect (c.couple p (bern v)) (test (fun z => true && z.2)) = v.val
  have h := c.snd p (bern v)
  have e := push_test (c.couple p (bern v)) Prod.snd
  exact (expect_congr _ (fun z => by cases z.2 <;> rfl)).trans (e.symm.trans
    ((congrArg (fun t : Law Bool => t.mass true) h).trans (bern_true v)))

theorem corner_value (v : Interval) (x : Interval) : corner c v x.val = x.val * v.val := by
  rw [IntervalAdditivity.linear (corner c v) _ (corner_add c v) x.val x.property.1 x.property.2, corner_one]
  intro a ha hb
  simp only [corner,dite_eq_left (show a ∈ Set.Icc (0:ℝ) 1 from ⟨ha,hb⟩)]
  exact point_nonneg _ _

/-- Singleton indicators recover each actual joint point, even for input types with infinitely many raw elements. -/
theorem pointwise {X Y : Type} (p : Law X) (q : Law Y) (x : X) (y : Y) :
    (c.couple p q).mass (x,y) = p.mass x * q.mass y := by
  classical
  let f := fun z => decide (z = x)
  let g := fun z => decide (z = y)
  let px : Interval := ⟨p.mass x,point_nonneg _ _,point_le_one _ _⟩
  let qy : Interval := ⟨q.mass y,point_nonneg _ _,point_le_one _ _⟩
  have hp : image f p = bern px := bool_determined _ _ ((push_test p f).trans (point_as_test p x))
  have hq : image g q = bern qy := bool_determined _ _ ((push_test q g).trans (point_as_test q y))
  have nt := c.natural f g p q
  rw [hp,hq] at nt
  calc
    _ = expect (c.couple p q) (test (fun z => f z.1 && g z.2)) := by
      rw [← point_as_test (c.couple p q) (x,y)]
      apply expect_congr; rintro ⟨i,j⟩; by_cases hi : i = x <;> by_cases hj : j = y <;> simp [test,f,g,hi,hj]
    _ = _ := (push_joint_test (c.couple p q) f g).symm
    _ = (c.couple (bern px) (bern qy)).mass (true,true) := congrArg (fun t : Law (Bool × Bool) => t.mass (true,true)) nt
    _ = corner c qy px.val := (as_corner c qy (bern px))
    _ = _ := corner_value c qy px

section Universes

variable (rule : Choice.{u})

/-- Pull the rule back to the small test sets by lifting both carriers. -/
def lower : Choice.{0} where
  couple p q := image (Prod.map ULift.down ULift.down) (rule.couple (image ULift.up p) (image ULift.up q))
  fst p q := by
    rw [image_comp]
    change image (ULift.down ∘ Prod.fst) _ = _
    rw [← image_comp,rule.fst,image_comp]; exact image_id p
  snd p q := by
    rw [image_comp]
    change image (ULift.down ∘ Prod.snd) _ = _
    rw [← image_comp,rule.snd,image_comp]; exact image_id q
  natural {X Y X' Y'} f g p q := by
    let upf : ULift.{u} X → ULift.{u} X' := fun x => ⟨f x.down⟩
    let upg : ULift.{u} Y → ULift.{u} Y' := fun y => ⟨g y.down⟩
    rw [image_comp]
    change image ((Prod.map ULift.down ULift.down) ∘ (Prod.map upf upg)) _ = _
    rw [← image_comp,rule.natural, image_comp, image_comp, image_comp, image_comp]
    rfl

theorem large_test {X Y : Type u} (p : Law X) (q : Law Y) (f : X → Bool) (g : Y → Bool) :
    image (Prod.map f g) (rule.couple p q) = (lower rule).couple (image f p) (image g q) := by
  change _ = image (Prod.map ULift.down ULift.down) (rule.couple (image ULift.up (image f p)) (image ULift.up (image g q)))
  rw [image_comp,image_comp,← rule.natural,image_comp]
  rfl

/-- Classification on arbitrary sets in one fixed universe, compared using lifted singleton indicators. -/
theorem independence {X Y : Type u} (p : Law X) (q : Law Y) (x : X) (y : Y) :
    (rule.couple p q).mass (x,y) = p.mass x * q.mass y := by
  classical
  let f := fun z => decide (z = x)
  let g := fun z => decide (z = y)
  calc
    _ = expect (rule.couple p q) (test (fun z => f z.1 && g z.2)) := by
      rw [← point_as_test (rule.couple p q) (x,y)]
      apply expect_congr; rintro ⟨i,j⟩; by_cases hi : i = x <;> by_cases hj : j = y <;> simp [test,f,g,hi,hj]
    _ = _ := (push_joint_test _ f g).symm
    _ = ((lower rule).couple (image f p) (image g q)).mass (true,true) :=
      congrArg (fun t : Law (Bool × Bool) => t.mass _) (large_test rule p q f g)
    _ = _ := pointwise (lower rule) _ _ _ _
    _ = _ := congrArg₂ (· * ·) ((push_test p f).trans (point_as_test p x)) ((push_test q g).trans (point_as_test q y))

end Universes

theorem diagonal_forbidden {X : Type u} (rule : Choice.{u}) (p : Law X) {x y : X}
    (hx : 0 < p.mass x) (hy : 0 < p.mass y) (hne : x ≠ y) : rule.couple p p ≠ image (fun z => (z,z)) p := by
  intro eq
  have h := congrArg (fun t : Law (X × X) => t.mass (x,y)) eq
  rw [independence] at h
  have zero := Finsupp.mapDomain_of_notMem_range (f := fun z : X => (z,z)) p.mass (x,y) (by
    rintro ⟨z,e⟩; exact hne ((congrArg Prod.fst e).symm.trans (congrArg Prod.snd e)))
  exact (mul_pos hx hy).ne' (h.trans zero)

end ContextualComposition.NaturalMarginalCouplings
