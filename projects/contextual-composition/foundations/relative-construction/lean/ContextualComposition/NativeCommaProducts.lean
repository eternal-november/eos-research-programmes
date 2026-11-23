module
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Product cones in the native comma hom from independent grade products, a base pullback, and an extension-cartesian lift. -/

@[expose] public section
namespace ContextualComposition.NativeCommaProducts
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

universe uK vK uL vL uC vC w
variable {K : Type uK} {L : Type uL} {C : Type uC} [Category.{vK} K] [Category.{vL} L] [Category.{vC} C]
variable {e : K ⥤ C} {d : L ⥤ C} {I : Type w} (D : I → Comma e d)

structure Grades where
  ctx : Fan (fun i => (D i).left)
  ctxLim : IsLimit ctx
  con : Fan (fun i => (D i).right)
  conLim : IsLimit con
  base : Fan (fun i => d.obj (D i).right)
  baseLim : IsLimit base

variable {D} (G : Grades D)

def Grades.contextBody : e.obj G.ctx.pt ⟶ G.base.pt :=
  Fan.IsLimit.lift G.baseLim (fun i => e.map (G.ctx.proj i) ≫ (D i).hom)

def Grades.contentComparison : d.obj G.con.pt ⟶ G.base.pt :=
  Fan.IsLimit.lift G.baseLim (fun i => d.map (G.con.proj i))

/-- A chosen context lift, displayed with the pullback square on its actual extension object. -/
structure Lift where
  grade : K
  leg : grade ⟶ G.ctx.pt
  body : e.obj grade ⟶ d.obj G.con.pt
  square : IsPullback (e.map leg) body G.contextBody G.contentComparison
  cartesian : e.IsStronglyCartesian (e.map leg) leg

/-- Install a chosen cartesian lift of the first pullback projection, with an isomorphism of the actual extension to the chosen pullback object. -/
noncomputable def ofPullback [HasPullback G.contextBody G.contentComparison] (P : K) (c : P ⟶ G.ctx.pt)
    (i : e.obj P ≅ pullback G.contextBody G.contentComparison)
    (hc : i.hom ≫ pullback.fst _ _ = e.map c) (cart : e.IsStronglyCartesian (e.map c) c) : Lift G where
  grade := P
  leg := c
  body := i.hom ≫ pullback.snd _ _
  cartesian := cart
  square := IsPullback.of_iso_pullback ⟨by rw [← hc,Category.assoc,Category.assoc,pullback.condition]⟩ i hc rfl

variable {G} (U : Lift G)

def object : Comma e d := ⟨U.grade,G.con.pt,U.body⟩

def projection (i : I) : object U ⟶ D i where
  left := U.leg ≫ G.ctx.proj i
  right := G.con.proj i
  w := by
    change e.map (U.leg ≫ G.ctx.proj i) ≫ (D i).hom = U.body ≫ d.map (G.con.proj i)
    have h := congrArg (fun k => k ≫ G.base.proj i) U.square.w
    simpa only [Functor.map_comp, Category.assoc, Grades.contextBody, Grades.contentComparison,
      Fan.IsLimit.fac] using h

def productFan : Fan D := Fan.mk (object U) (projection U)

private def ctxMap (s : Fan D) : s.pt.left ⟶ G.ctx.pt :=
  Fan.IsLimit.lift G.ctxLim (fun i => (s.proj i).left)
private def conMap (s : Fan D) : s.pt.right ⟶ G.con.pt :=
  Fan.IsLimit.lift G.conLim (fun i => (s.proj i).right)

private theorem baseComm (s : Fan D) : e.map (ctxMap (G:=G) s) ≫ G.contextBody =
    (s.pt.hom ≫ d.map (conMap (G:=G) s)) ≫ G.contentComparison := by
  apply Fan.IsLimit.hom_ext G.baseLim
  intro i
  simp only [Category.assoc,Grades.contextBody,Grades.contentComparison,Fan.IsLimit.fac]
  rw [← e.map_comp_assoc, ← d.map_comp]
  simp only [ctxMap, conMap, Fan.IsLimit.fac, CommaMorphism.w]

/-- The extension arrow is determined by the base pullback; the native left leg is recovered by cartesian universality. -/
theorem uniqueLift (s : Fan D) : ∃! m : s.pt ⟶ object U, ∀ i, m ≫ projection U i = s.proj i := by
  let r := ctxMap (G:=G) s
  let t := conMap (G:=G) s
  let k := U.square.lift (e.map r) (s.pt.hom ≫ d.map t) (baseComm s)
  have k₁ : k ≫ e.map U.leg = e.map r := U.square.lift_fst _ _ _
  have k₂ : k ≫ U.body = s.pt.hom ≫ d.map t := U.square.lift_snd _ _ _
  let := U.cartesian
  obtain ⟨l,⟨over,fac⟩,uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property e (e.map U.leg) U.leg k (e.map r) k₁.symm r
  let := over
  have lk : e.map l = k := (IsHomLift.eq_of_isHomLift e k l).symm
  let m : s.pt ⟶ object U := ⟨l,t,by change e.map l ≫ U.body = _; rw [lk]; exact k₂⟩
  refine ⟨m,?_,?_⟩
  · intro i
    apply Comma.hom_ext
    · change l ≫ U.leg ≫ G.ctx.proj i = _
      rw [← Category.assoc,fac]
      exact Fan.IsLimit.fac _ _ _
    · exact Fan.IsLimit.fac G.conLim _ _
  · intro n hn
    have nl : n.left ≫ U.leg = r := by
      apply Fan.IsLimit.hom_ext G.ctxLim
      intro i
      rw [Category.assoc]
      exact (congrArg CommaMorphism.left (hn i)).trans (Fan.IsLimit.fac G.ctxLim (fun j => (s.proj j).left) i).symm
    have nr : n.right = t := by
      apply Fan.IsLimit.hom_ext G.conLim
      intro i
      exact (congrArg CommaMorphism.right (hn i)).trans (Fan.IsLimit.fac G.conLim (fun j => (s.proj j).right) i).symm
    have nk : e.map n.left = k := by
      apply U.square.hom_ext
      · rw [← e.map_comp,nl,k₁]
      · exact n.w.trans ((congrArg (fun j => s.pt.hom ≫ d.map j) nr).trans k₂.symm)
    apply Comma.hom_ext _ _ _ nr
    exact uniq _ ⟨nk ▸ (inferInstance : e.IsHomLift (e.map n.left) n.left),nl⟩

noncomputable def productLimit : IsLimit (productFan U) :=
  Fan.IsLimit.mk _ (fun s => (uniqueLift U s).exists.choose)
    (fun s i => (uniqueLift U s).exists.choose_spec i)
    (fun s _ h => (uniqueLift U s).unique h (uniqueLift U s).exists.choose_spec)

end ContextualComposition.NativeCommaProducts
