module
public import ContextualComposition.NativeCommaProducts

/-! Pure-input preservation of native products using the Beck–Chevalley square at the chosen extension lift. -/

@[expose] public section
namespace ContextualComposition.NativeCommaReindex
open CategoryTheory CategoryTheory.Limits NativeCommaProducts
set_option backward.isDefEq.respectTransparency false

universe uK vK uK' vK' uL vL uC vC w
variable {K : Type uK} {K' : Type uK'} {L : Type uL} {C : Type uC}
variable [Category.{vK} K] [Category.{vK'} K'] [Category.{vL} L] [Category.{vC} C]
variable {e : K ⥤ C} {e' : K' ⥤ C} {d : L ⥤ C} (a : K ⥤ K') (r : a ⋙ e' ⟶ e)

def input : Comma e d ⥤ Comma e' d where
  obj X := ⟨a.obj X.left,X.right,r.app X.left ≫ X.hom⟩
  map {X Y} f := {
    left := a.map f.left
    right := f.right
    w := by
      have nat : e'.map (a.map f.left) ≫ r.app Y.left = r.app X.left ≫ e.map f.left := r.naturality _
      rw [← Category.assoc,nat,Category.assoc,f.w,Category.assoc] }

variable {I : Type w} {D : I → Comma e d} {G : Grades D}

def mappedContextFan := Fan.mk (a.obj G.ctx.pt) (fun i => a.map (G.ctx.proj i))

variable (U : Lift G) (pres : IsLimit (mappedContextFan (G:=G) a))

def grades : Grades (fun i => (input a r).obj (D i)) where
  ctx := mappedContextFan (G:=G) a
  ctxLim := pres
  con := G.con
  conLim := G.conLim
  base := G.base
  baseLim := G.baseLim

theorem mapped_body : (grades a r pres).contextBody = r.app G.ctx.pt ≫ G.contextBody := by
  apply Fan.IsLimit.hom_ext G.baseLim
  intro i
  change Fan.IsLimit.lift G.baseLim _ ≫ _ = (r.app G.ctx.pt ≫ G.contextBody) ≫ _
  rw [Fan.IsLimit.fac,Category.assoc]
  change e'.map (a.map (G.ctx.proj i)) ≫ r.app _ ≫ (D i).hom = _
  rw [Grades.contextBody,Fan.IsLimit.fac]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ (D i).hom) (r.naturality (G.ctx.proj i))).trans (Category.assoc _ _ _))

variable (cart : e'.IsStronglyCartesian (e'.map (a.map U.leg)) (a.map U.leg))
variable (bc : IsPullback (e'.map (a.map U.leg)) (r.app U.grade) (r.app G.ctx.pt) (e.map U.leg))

def transportedLift : Lift (grades a r pres) where
  grade := a.obj U.grade
  leg := a.map U.leg
  body := r.app U.grade ≫ U.body
  cartesian := cart
  square := by
    rw [mapped_body]
    exact bc.paste_vert U.square

/-- The image of the actual native product cone satisfies the full native universal property. -/
noncomputable def mappedProduct :
    IsLimit (Fan.mk ((input a r).obj (object U)) (fun i => (input a r).map (projection U i))) := by
  let V := transportedLift a r U pres cart bc
  have legs : (fun i => (input a r).map (projection U i)) = projection V := by
    funext i
    apply Comma.hom_ext
    · exact a.map_comp _ _
    · rfl
  rw [legs]
  exact productLimit V

end ContextualComposition.NativeCommaReindex
