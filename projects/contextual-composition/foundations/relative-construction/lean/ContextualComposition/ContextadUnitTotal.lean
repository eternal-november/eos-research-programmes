module
public import ContextualComposition.ContextadPayloadModification
public import ContextualComposition.ContextadInsideCharts
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadUnitTotal
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue NativeCleavage
open ContextadRoutes ContextadLawTransport ContextadNativeLaws TelescopeSquares WordTrace
set_option backward.isDefEq.respectTransparency false
universe u v
theorem alignedHEq {C : Type*} [Category* C] {a b a' b' : C} {f : a ⟶ b} {g : a' ⟶ b'} (e : Aligned f g) : HEq f g := by
    obtain ⟨rfl,rfl,h⟩ := e; simp at h; cases h; rfl
section Generic
variable {B K : Type*} [Category* B] [Category* K] (Y : Bᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ B)
theorem pureTotal {x y : Total Y e} (f : x ⟶ y) (g : Pure (gradeMap f)) (p : Pure (payloadMap f)) : Pure f := by
  obtain ⟨⟨⟨a⟩,⟨x⟩⟩⟩ := x
  obtain ⟨⟨⟨b⟩,⟨y⟩⟩⟩ := y
  obtain ⟨h,hg⟩ := g
  change a = b at h; subst b
  have tg : (Y.map (e.map (gradeMap f)).op).toFunctor.obj y = y := by
    rw [hg]; simp; exact Functor.congr_obj (congrArg Cat.Hom.toFunctor (Y.map_id _)) y
  obtain he := p.choose.trans tg
  change x = y at he; subst y
  exact ⟨rfl,WeightedCells.pureArrowEq Y e hg p (WeightedCells.totalPureId Y e _)⟩
theorem pureAlign {x y x' y' : Total Y e} (hx : x=x') (hy : y=y')
    (f : x ⟶ y) (g : x' ⟶ y') (a : Aligned (gradeMap f) (gradeMap g)) (p : Pure (payloadMap f)) (q : Pure (payloadMap g)) :
    Aligned f g := by subst x'; subst y'; exact NativeCube.ofEq (WeightedCells.pureArrowEq Y e a.eq p q)
end Generic
section Uniqueness
variable {B : Type*} [Category* B] (G H : Bᵒᵖ ⥤ Cat.{v,u})
variable (F J : Total G (𝟭 B) ⥤ Total H (𝟭 B)) (f : F ⋙ proj H = proj G) (j : J ⋙ proj H = proj G)
variable (h : ∀ A, incl G A ⋙ F = incl G A ⋙ J)
variable (pf : ∀ (z : Total G (𝟭 B)) {k : B} (a : k ⟶ grade _ _ z), Pure (payloadMap (F.map (pullLift G (𝟭 B) z a))))
variable (pj : ∀ (z : Total G (𝟭 B)) {k : B} (a : k ⟶ grade _ _ z), Pure (payloadMap (J.map (pullLift G (𝟭 B) z a))))
include f j h pf pj in
theorem normalUnique : F = J := by
  have obj (x : Total G (𝟭 B)) : F.obj x = J.obj x :=
    Functor.congr_obj (h (grade _ _ x)) (payload _ _ x)
  apply Edge.functor_ext
  intro z
  let m := pullLift G (𝟭 B) z.dst (gradeMap z.hom)
  let k := (incl G (grade _ _ z.src)).map (payloadMap z.hom)
  have u : k ≫ m = z.hom := ContextadCartesian.factorTotal G (𝟭 B) z.hom
  have j₁ : Aligned (F.map k) (J.map k) := NativeCube.functorAlign (h _) (payloadMap z.hom)
  have j₂ : Aligned (F.map m) (J.map m) := pureAlign H (𝟭 B) (obj _) (obj _) _ _
    ((NativeCube.functorAlign f m).trans (NativeCube.functorAlign j m).symm) (pf _ _) (pj _ _)
  exact Edge.eq_of (obj _) (obj _) (alignedHEq ((NativeCube.ofEq ((congrArg F.map u.symm).trans (F.map_comp k m))).trans
    ((j₁.comp j₂).trans (NativeCube.ofEq ((J.map_comp k m).symm.trans (congrArg J.map u))))))
end Uniqueness
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem pureOne (z : E (PackedFree.pow S Y 1))
    (h : Pure (payloadMap (one S Y z).1.hom)) (j : Pure (payloadMap (one S Y z).2.hom)) :
    Pure (payloadMap z.hom) := by
  apply pureTotal Y (P.extend (grade _ _ z.src))
  · exact h
  · let x := payload _ _ z.src
    let y := payload _ _ z.dst
    let a := gradeMap z.hom
    let q := squareEquiv Y S a (.cons (grade _ _ x) (.nil _)) (.cons (grade _ _ y) (.nil _)) (payload _ _ x) (payload _ _ y)
    have b := compared_tail Y S (q.symm (payloadMap z.hom))
    change payloadMap (q (q.symm (payloadMap z.hom))) = _ at b
    have t : Pure (payloadMap (q (q.symm (payloadMap z.hom)))) := b ▸ pureComp j ⟨_,rfl⟩
    exact (congrArg (fun k => FibreValue.Pure (payloadMap k)) (q.apply_symm_apply (payloadMap z.hom))).mp t
variable (d : ContextadUnit.Data P)
theorem eraseUnit : global Y (insert S d) = raw Y (insert S d) ⋙ BlockEvaluation.global S Y 1 := by
  have e : (BlockEvaluation.global S Y 0).strictInv = 𝟭 _ :=
    (Functor.id_comp _).symm.trans (BlockEvaluation.global S Y 0).asIsomorphism.unit_eq.symm
  exact (congrArg (· ⋙ (raw Y (insert S d) ⋙ BlockEvaluation.global S Y 1)) e).trans (Functor.id_comp _)
theorem pureUnit (z : Total Y (𝟭 B)) {k : B} (a : k ⟶ grade _ _ z) :
    Pure (payloadMap (((raw Y (insert S d) ⋙ BlockEvaluation.global S Y 1)).map (pullLift Y (𝟭 B) z a))) := by
  let k' : E Y := ⟨_,_,pullLift Y (𝟭 B) z a⟩
  let w := Edge.map (raw Y (insert S d)) k'
  let v := Edge.map (BlockEvaluation.global S Y 1) w
  have s := NativeTrace.read_global S Y 1 w
  change ([(one S Y v).1],(one S Y v).2) = ([Edge.map gradeProjection w], Edge.map (NativeTrace.leaf Y _) w) at s
  have h := List.cons.inj (congrArg Prod.fst s)
  apply pureOne Y v
  · rw [h.1]
    exact ⟨(d.reindex a).symm,rfl⟩
  · rw [congrArg Prod.snd s]
    change Pure (payloadMap ((restrict Y _ _ (unitGrade d) (discharge S d)).map k'.hom))
    rw [restrict_payload]
    exact pureComp (pureMap _ (pureId _)) ⟨_,rfl⟩
theorem totalUnit : global Y (insert S d) = ChainPayload.fibreMap (ContextadUnit.onPresheaf d S Y) (𝟭 B) := by
  apply normalUnique Y (PackedFree.pow S Y 1) _ _ (over Y (insert S d)) rfl
  · intro A
    exact (evalIncl Y (insert S d) A).symm.trans ((congrArg (· ⋙ incl (PackedFree.pow S Y 1) A) (evalUnit d Y A)).trans
      (ContextadPayloadModification.inclSquare (ContextadUnit.onPresheaf d S Y) A).symm)
  · intro z k a
    rw [eraseUnit]; exact pureUnit Y d z a
  · intro z k a
    exact ContextadPayloadModification.purePayload (ContextadUnit.onPresheaf d S Y) _ _ (pureId _)
theorem congrAction {B K : Type*} [Category* B] [Category* K] {G H : Bᵒᵖ ⥤ Cat}
    (e : K ⥤ B) {F J : Total G (𝟭 B) ⥤ Total H (𝟭 B)} (h j) (x : F = J) :
    ContextadWeakAction.action e F h = ContextadWeakAction.action e J j := by subst J; rfl
theorem insideEta (A : B) : evaluate Y (inside 1 (insert S d)) A =
    ChainPayload.fibreMap (ContextadUnit.onPresheaf d S Y) (P.extend A) := by
  refine (ContextadWeakAction.insideUnit Y d A).trans ?_
  exact (congrAction (P.extend A) _ rfl (totalUnit Y d)).trans
    (ContextadWeakAction.onStrict (P.extend A) (ContextadUnit.onPresheaf d S Y))
end ContextualComposition.GrothendieckStep.ContextadUnitTotal
