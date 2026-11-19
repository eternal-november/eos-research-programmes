module
public import ContextualComposition.EndpointInterpretation
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadUnit
open CategoryTheory CategoryTheory.Functor Opposite PackedFree
universe b w u v
set_option backward.isDefEq.respectTransparency false
section Inclusion
variable {K J : Type*} [Category* K] [Category* J]
theorem inclPre (F : J ⥤ Cat.{v,u}) (r : K ⥤ J) (i : K) :
    Grothendieck.ι (r ⋙ F) i ⋙ Grothendieck.pre F r = Grothendieck.ι F (r.obj i) := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    apply Grothendieck.ext _ _ (r.map_id _)
    simp [Grothendieck.ι,eqToHom_trans_assoc]
variable {B : Type b} [Category.{w} B] (Y : Bᵒᵖ ⥤ Cat.{v,u})
abbrev atGrade (e : K ⥤ B) (i : K) := (Grothendieck.ι (diagram Y e) (op i)).rightOp
theorem inclRestrict (e : K ⥤ B) (d : J ⥤ B) (r : K ⥤ J) (l : r ⋙ d ⟶ e) (i : K) :
    atGrade Y e i ⋙ restrict Y e d r l = (Y.map (l.app i).op).toFunctor ⋙ atGrade Y d (r.obj i) := by
  have m := EvalPayload.inclMapEq (restrictionCell Y e d r l) (op i)
  have h := inclPre (diagram Y d) r.op (op i)
  exact congrArg Functor.rightOp ((congrArg (· ⋙ Grothendieck.pre _ r.op) m).trans
    (congrArg (((restrictionCell Y e d r l).app (op i)).toFunctor ⋙ ·) h))
theorem inclPayload {Z : Bᵒᵖ ⥤ Cat.{v,u}} (t : Y ⟶ Z) (e : K ⥤ B) (i : K) :
    atGrade Y e i ⋙ ChainPayload.fibreMap t e = (t.app (op (e.obj i))).toFunctor ⋙ atGrade Z e i :=
  congrArg Functor.rightOp (EvalPayload.inclMapEq (ChainPayload.cell t e) (op i))
theorem collapsed (e : K ⥤ B) {i j : K} (h : i = j) {A : B} (p : e.obj i ⟶ A) (q : e.obj j ⟶ A)
    (comm : p = e.map (eqToHom h) ≫ q) :
    (Y.map p.op).toFunctor ⋙ atGrade Y e i = (Y.map q.op).toFunctor ⋙ atGrade Y e j := by
  subst j
  simp only [eqToHom_refl,Functor.map_id,Category.id_comp] at comm
  rw [comm]
end Inclusion
variable {B : Type b} [Category.{w} B] (P : Endpoints.{b,w,u,max u v} B)
/-- Native chosen unit grade, discharge and its two strict base-change laws. -/
structure Data where
  grade : ∀ A : B, P.grades.obj (op A)
  discharge : ∀ A : B, (P.extend A).obj (grade A) ⟶ A
  reindex : ∀ {A D : B} (f : D ⟶ A), (P.grades.map f.op).toFunctor.obj (grade A) = grade D
  square : ∀ {A D : B} (f : D ⟶ A),
    (P.lift f).app (grade A) ≫ discharge A = (P.extend D).map (eqToHom (reindex f)) ≫ discharge D ≫ f
variable {P} (d : Data P) (S : P.Split) (Y : Bᵒᵖ ⥤ Cat.{max u v,u})
abbrev atBase (A : B) := (Y.map (d.discharge A).op).toFunctor ⋙ atGrade Y (P.extend A) (d.grade A)
theorem reindexed {A D : B} (f : D ⟶ A) :
    (Y.map f.op).toFunctor ⋙ atBase d Y D = atBase d Y A ⋙ P.baseRestrict Y f := by
  have h := collapsed Y (P.extend D) (d.reindex f) ((P.lift f).app (d.grade A) ≫ d.discharge A) (d.discharge D ≫ f) (d.square f)
  rw [op_comp,Y.map_comp,op_comp,Y.map_comp] at h
  exact h.symm.trans (congrArg ((Y.map (d.discharge A).op).toFunctor ⋙ ·) (inclRestrict Y _ _ _ (P.lift f) (d.grade A)).symm)
def onPresheaf : Y ⟶ (step S).obj Y where
  app A := (atBase d Y A.unop).toCatHom
  naturality _ _ f := congrArg Functor.toCatHom (reindexed d Y f.unop)
theorem payloadSquare {Z : Bᵒᵖ ⥤ Cat.{max u v,u}} (t : Y ⟶ Z) (A : B) :
    (t.app (op A)).toFunctor ⋙ atBase d Z A = atBase d Y A ⋙ ChainPayload.fibreMap t (P.extend A) := by
  have e := congrArg Cat.Hom.toFunctor (t.naturality (d.discharge A).op)
  exact (congrArg (· ⋙ atGrade Z (P.extend A) (d.grade A)) e.symm).trans
    (congrArg ((Y.map (d.discharge A).op).toFunctor ⋙ ·) (inclPayload Y t (P.extend A) (d.grade A)).symm)
def unit : 𝟭 _ ⟶ step S where
  app := onPresheaf d S
  naturality _ _ t := by apply NatTrans.ext; funext A; exact congrArg Functor.toCatHom (payloadSquare d _ t A.unop)
theorem unitObj (A : B) (y : Y.obj (op A)) :
    (((unit d S).app Y).app (op A)).toFunctor.obj y = pair Y _ (d.grade A) ((Y.map (d.discharge A).op).toFunctor.obj y) := rfl
theorem unitGrade (A : B) {x y : Y.obj (op A)} (f : x ⟶ y) :
    gradeMap ((((unit d S).app Y).app (op A)).toFunctor.map f) = 𝟙 (d.grade A) := rfl
theorem unitPayload (A : B) {x y : Y.obj (op A)} (f : x ⟶ y) :
    HEq (payloadMap ((((unit d S).app Y).app (op A)).toFunctor.map f)) ((Y.map (d.discharge A).op).toFunctor.map f) := by
  change HEq ((eqToHom _ ≫ ((Y.map (d.discharge A).op).toFunctor.map f).op).unop) _
  rw [unop_comp]
  have aux {a c z : Y.obj (op ((P.extend A).obj (d.grade A)))} (k : a ⟶ c) (h : op z = op c) :
      HEq (k ≫ (eqToHom h).unop) k := by cases unop_injective h; simp
  exact aux _ _
end ContextualComposition.GrothendieckStep.ContextadUnit
