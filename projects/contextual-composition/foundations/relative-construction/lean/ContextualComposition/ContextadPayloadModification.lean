module
public import ContextualComposition.ContextadModification
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadPayloadModification
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks ContextadRoutes ContextadLawTransport FibreValue
set_option backward.isDefEq.respectTransparency false
universe u v
section Raw
variable {B K L : Type*} [Category* B] [Category* K] [Category* L]
variable {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (t : Y ⟶ Z)
variable (e : K ⥤ B) (d : L ⥤ B) {r s : K ⥤ L} {l : r ⋙ d ⟶ e} {m : s ⋙ d ⟶ e}
variable (i : r ≅ s) (h : whiskerRight i.hom d ≫ m = l)
theorem pureCast {x y : Total Z d} (k : x = y) : Pure (payloadMap (eqToHom k)) := by
  subst y; exact WeightedCells.totalPureId Z d _
theorem purePayload {x y : Total Y d} (f : x ⟶ y) (p : Pure (payloadMap f)) :
    Pure (payloadMap ((ChainPayload.fibreMap t d).map f)) := by
  have hl := ChainPayload.fibreMap_payload t d f
  have hr := pureMap (t.app (op (d.obj (grade Y d x)))).toFunctor p
  obtain ⟨a,b,eqn⟩ := hl
  exact pureCancel (eqn ▸ pureComp ⟨_,rfl⟩ hr) ⟨_,rfl⟩
theorem castGrade (d' : r ⋙ d ⟶ e) (x : Total Y e) :
    gradeMap (eqToHom (Functor.congr_obj (ChainPayload.base_square t e d r d') x)) = 𝟙 _ := by
  change (gradeProjection (Y := Z) (e := d)).map (eqToHom _) = _
  rw [eqToHom_map]; rfl
/-- Payload interchange, including the two type-correcting boundary transports.
Proved by uniqueness on grade and pure payload, not an imposed mixed diagram. -/
theorem rawSquare :
    whiskerRight (WeightedCells.weightIso Y e d i h).hom (ChainPayload.fibreMap t d) ≫
      eqToHom (ChainPayload.base_square t e d s m) =
    eqToHom (ChainPayload.base_square t e d r l) ≫
      whiskerLeft (ChainPayload.fibreMap t e) (WeightedCells.weightIso Z e d i h).hom := by
  ext x : 2
  simp only [NatTrans.comp_app,whiskerRight_app,whiskerLeft_app,eqToHom_app]
  apply WeightedCells.pureArrowEq Z d
  · rw [grade_comp, grade_comp,castGrade,castGrade,Category.comp_id,Category.id_comp]
    change gradeMap ((WeightedCells.weightIso Y e d i h).hom.app x) = _
    rw [WeightedCells.weightGrade,WeightedCells.weightGrade]; rfl
  · exact WeightedCells.totalPureComp Z d (purePayload t d _ (WeightedCells.weightPayloadPure Y e d i h x)) (pureCast d _)
  · exact WeightedCells.totalPureComp Z d (pureCast d _) (WeightedCells.weightPayloadPure Z e d i h _)
end Raw
end ContextualComposition.GrothendieckStep.ContextadPayloadModification

namespace ContextualComposition.GrothendieckStep.ContextadPayloadModification
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks ContextadRoutes ContextadLawTransport FibreValue TelescopeSquares
set_option backward.isDefEq.respectTransparency false
universe u v
section General
variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
theorem invChange (E : C ⥤ D) (E' : C' ⥤ D') [E.IsIso] [E'.IsIso]
    (t : C ⥤ C') (u : D ⥤ D') (e : t ⋙ E' = E ⋙ u) :
    E.strictInv ⋙ t = u ⋙ E'.strictInv := by
  apply E'.asIsomorphism.comp_functor_injective
  exact (congrArg (E.strictInv ⋙ ·) e).trans
    ((congrArg (· ⋙ u) E.asIsomorphism.counit_eq).trans
      (congrArg (u ⋙ ·) E'.asIsomorphism.counit_eq).symm)
theorem appChange {F G : C ⥤ D} (a : F ⟶ G) {x y : C} (h : x = y) :
    Aligned (a.app x) (a.app y) := by subst y; exact Aligned.refl _
theorem reflectAlign (F : C ⥤ D) [F.Faithful] (inj : Function.Injective F.obj)
    {x y x' y' : C} (a : x ⟶ y) (b : x' ⟶ y') (h : Aligned (F.map a) (F.map b)) : Aligned a b := by
  obtain rfl := inj h.src; obtain rfl := inj h.dst
  exact NativeCube.ofEq (F.map_injective h.eq)
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {Y Z : PackedCuts.Psh.{u,max u v,u,v} B} (t : Y ⟶ Z)
abbrev totalT (n : Nat) := ChainPayload.fibreMap (ChainPayload.layerMap t S n) (𝟭 B)
abbrev nativeT (n : Nat) := ChainPayload.fibreMap t (power S n).dest
theorem chartSquare : (n : Nat) → nativeT (S := S) t n ⋙ BlockEvaluation.global S Z n = BlockEvaluation.global S Y n ⋙ totalT t n
  | 0 => rfl
  | n+1 => EvalPayload.nativeSquare t S n
variable {i j : Nat} {r s : Map S i j} (c : Cell r s)
theorem rawAligned (x : Total Y (power S i).dest) :
    Aligned ((nativeT (S := S) t j).map ((rawCell Y c).hom.app x)) ((rawCell Z c).hom.app ((nativeT (S := S) t i).obj x)) :=
  ⟨Functor.congr_obj (ChainPayload.base_square t _ _ r.grade r.leg) x,
    Functor.congr_obj (ChainPayload.base_square t _ _ s.grade s.leg) x,
    by simpa only [rawCell,nativeT,raw,NatTrans.comp_app,whiskerRight_app,whiskerLeft_app,eqToHom_app] using NatTrans.congr_app (rawSquare t _ _ c.grade c.endpoint) x⟩
theorem totalAligned (x : Total (PackedFree.pow S Y i) (𝟭 B)) :
    Aligned ((totalT (S := S) t j).map ((globalCell Y c).hom.app x))
      ((globalCell Z c).hom.app ((totalT (S := S) t i).obj x)) := by
  let w := (BlockEvaluation.global S Y i).strictInv.obj x
  let z := (rawCell Y c).hom.app w
  let e := invChange (BlockEvaluation.global S Y i) (BlockEvaluation.global S Z i)
    (nativeT (S := S) t i) (totalT (S := S) t i) (chartSquare (S := S) t i)
  exact (NativeCube.functorAlign (chartSquare (S := S) t j).symm z).trans
    (((rawAligned t c w).map (BlockEvaluation.global S Z j)).trans
      ((appChange (rawCell Z c).hom (Functor.congr_obj e x)).map (BlockEvaluation.global S Z j)))
theorem includeCell (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B) (x : (PackedFree.pow S Y i).obj (op A)) :
    Aligned ((incl (PackedFree.pow S Y j) A).map ((evalCell Y c A).hom.app x))
      ((globalCell Y c).hom.app ((incl (PackedFree.pow S Y i) A).obj x)) := by
  let H := PackedFree.pow S Y j
  let n := (onFiber (global Y r) (global Y s) (over Y r) (over Y s) (globalCell Y c) (globalVertical Y c) A).hom.app ((embed _ A).obj x)
  have e := (NativeCube.functorAlign (value_embed H A) n).map Fiber.fiberInclusion
  exact e.trans (ContextadModification.fibreAligned _ _ _ _ (globalCell Y c) (globalVertical Y c) A _)
theorem inclSquare {G H : Bᵒᵖ ⥤ Cat.{max u v,u}} (t : G ⟶ H) (A : B) :
    incl G A ⋙ ChainPayload.fibreMap t (𝟭 B) = (t.app (op A)).toFunctor ⋙ incl H A :=
  congrArg Functor.rightOp (EvalPayload.inclMapEq (ChainPayload.cell t (𝟭 B)) (op A))
theorem evalAligned (A : B) (x : (PackedFree.pow S Y i).obj (op A)) :
    Aligned (((ChainPayload.layerMap t S j).app (op A)).toFunctor.map ((evalCell Y c A).hom.app x))
      ((evalCell Z c A).hom.app (((ChainPayload.layerMap t S i).app (op A)).toFunctor.obj x)) := by
  let H := PackedFree.pow S Z j
  let I := incl H A
  let _ : I.Faithful := (inferInstance : (embed H A ⋙ Fiber.fiberInclusion).Faithful)
  have inj : Function.Injective I.obj := by
    intro a b h
    exact congrArg (value H A).obj (show (embed H A).obj a = (embed H A).obj b from Subtype.ext h)
  apply reflectAlign I inj
  exact (NativeCube.functorAlign (inclSquare (ChainPayload.layerMap t S j) A).symm _).trans
    (((includeCell c Y A x).map (totalT (S := S) t j)).trans
    ((totalAligned t c _).trans ((appChange (globalCell Z c).hom (Functor.congr_obj (inclSquare (ChainPayload.layerMap t S i) A) x)).trans
    (includeCell c Z A _).symm)))
end ContextualComposition.GrothendieckStep.ContextadPayloadModification
