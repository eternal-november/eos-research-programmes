module
public import ContextualComposition.ContextadHorizontalLaws
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadHorizontalLaws
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadNativeLaws ContextadLawTransport
open ContextadModification TelescopeSquares
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
section General
variable {n : Nat} {f g : Map S n 1}
noncomputable def modPaste (p : Path f g) (u : gradeCart f) (v : gradeCart g) :
    Pseudofunctor.StrongTrans.Modification (nativeStrong Y f u) (nativeStrong Y g v) where
  app A := (paste Y A.as.unop p).toCatHom₂
  naturality {A D} a := by
    simp only [paste_eq]
    exact (nativeModification Y (composite p) u v).naturality a
theorem modApp (A : LocallyDiscrete Bᵒᵖ) (p : Path f g) (u : gradeCart f) (v : gradeCart g) :
    (modPaste Y p u v).app A = (paste Y A.as.unop p).toCatHom₂ := rfl
theorem modMore {h : Map S n 1} (c : Cell f g) (p : Path g h) (u : gradeCart f) (v : gradeCart g) (w : gradeCart h) :
    modPaste Y (.more c p) u w = (nativeModification Y c u v).vcomp (modPaste Y p v w) := by
  apply Pseudofunctor.StrongTrans.Modification.ext; rfl
theorem modTransport (p q : Path f g) (u : gradeCart f) (v : gradeCart g)
    (h : ∀ x, (composite p).grade.hom.app x = (composite q).grade.hom.app x) :
    modPaste Y p u v = modPaste Y q u v := by
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext A; rw [modApp,modApp,transport Y A.as.unop p q h]
variable {Z : PackedCuts.Psh.{u,max u v,u,v} B} (t : Y ⟶ Z) (A : B)
theorem strictPayload (p : Path f g) (x : (PackedFree.pow S Y n).obj (op A)) :
    Aligned (((ChainPayload.layerMap t S 1).app (op A)).toFunctor.map ((paste Y A p).app x))
      ((paste Z A p).app (((ChainPayload.layerMap t S n).app (op A)).toFunctor.obj x)) := by
  rw [paste_eq,paste_eq]; exact ContextadPayloadModification.evalAligned t (composite p) A x
end General
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
theorem compCart {i j k} (r : Map S i j) (s : Map S j k) (p : gradeCart r) (q : gradeCart s) :
    gradeCart (comp r s) := fun f h => q _ (p f h)
theorem suffIdCart : gradeCart (suffix (identity (S := S) 1)) :=
  appendCart (identity 1) (nativeChoice (S := S) 1) (fun _ h => h)
theorem triEndCart : gradeCart (triRight d m c).dst := compCart (suffix (identity 1)) (tensor m) suffIdCart m.cart
theorem triStartCart : gradeCart (triRight d m c).src := presIso (triRight d m c).cell.grade (triEndCart d m c)
theorem pentStartCart : gradeCart (pent1 d m c).src :=
  fun _ hz => m.cart _ (appendCart (comp (firstTwo m) (tensor m)) (nativeChoice 3) (assocCart m) _ hz)
theorem triangleModification (t : TriangleSeams d m c)
    (h : ∀ x, (composite (triLong d m c t)).grade.hom.app x = (composite (triShort d m c)).grade.hom.app x) :
    modPaste Y (triLong d m c t) (triStartCart d m c) (presIso (composite (triShort d m c)).grade.symm (triStartCart d m c)) =
    modPaste Y (triShort d m c) (triStartCart d m c) (presIso (composite (triShort d m c)).grade.symm (triStartCart d m c)) :=
  modTransport Y _ _ _ _ h
theorem pentagonModification (p : PentagonSeams d m c)
    (h : ∀ x, (composite (pentLong d m c p)).grade.hom.app x = (composite (pentShort d m c p)).grade.hom.app x) :
    modPaste Y (pentLong d m c p) (pentStartCart d m c) (presIso (composite (pentLong d m c p)).grade.symm (pentStartCart d m c)) =
    modPaste Y (pentShort d m c p) (pentStartCart d m c) (presIso (composite (pentLong d m c p)).grade.symm (pentStartCart d m c)) :=
  modTransport Y _ _ _ _ h
end ContextualComposition.GrothendieckStep.ContextadHorizontalLaws
