module
public import ContextualComposition.TelescopeGradeModification

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeGradeChange
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open ContextadAmbientPayload AmbientBlockCells CoproductSpan CoproductSpan.All
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

section Square
variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
variable {P : C ⥤ D} {Q : E ⥤ F} {S S' : C ⥤ E} {T T' : D ⥤ F}

/-- A pair of directed transformations commutes with two isomorphism squares on the same horizontal boundaries. -/
abbrev SquareNaturality (i : P ⋙ T ≅ S ⋙ Q) (j : P ⋙ T' ≅ S' ⋙ Q) (s : S ⟶ S') (t : T ⟶ T') : Prop :=
  whiskerLeft P t ≫ j.hom = i.hom ≫ whiskerRight s Q

private theorem square_app {i : P ⋙ T ≅ S ⋙ Q} {j : P ⋙ T' ≅ S' ⋙ Q} {s : S ⟶ S'} {t : T ⟶ T'}
    (h : SquareNaturality i j s t) (x : C) :
    t.app (P.obj x) ≫ j.hom.app x = i.hom.app x ≫ Q.map (s.app x) :=
  NatTrans.congr_app h x

variable (L : C ≌ D) (M : E ≌ F)
variable {i : L.functor ⋙ T ≅ S ⋙ M.functor} {j : L.functor ⋙ T' ≅ S' ⋙ M.functor} {s : S ⟶ S'} {t : T ⟶ T'}

/-- Passing a square across both horizontal equivalences preserves modification naturality. -/
theorem inverseSquare_naturality (h : SquareNaturality i j s t) :
    SquareNaturality (SumChange.inverseSquare L M i) (SumChange.inverseSquare L M j) t s := by
  have hi (y : C) : M.functor.map (s.app y) ≫ j.inv.app y = i.inv.app y ≫ t.app (L.functor.obj y) := by
    calc
      _ = i.inv.app y ≫ (i.hom.app y ≫ M.functor.map (s.app y)) ≫ j.inv.app y := by simp
      _ = _ := by rw [← square_app h y]; simp
  apply NatTrans.ext
  funext x
  simp [SumChange.inverseSquare,Category.assoc]
  let y := L.inverse.obj x
  have hu : s.app y ≫ M.unitIso.hom.app (S'.obj y) = M.unitIso.hom.app (S.obj y) ≫ M.inverse.map (M.functor.map (s.app y)) := M.unitIso.hom.naturality _
  have hm := congrArg M.inverse.map (hi y)
  simp only [Functor.map_comp] at hm
  rw [← Category.assoc,hu,Category.assoc]
  apply congrArg (M.unitIso.hom.app (S.obj y) ≫ ·)
  simpa only [Category.assoc] using congrArg (· ≫ M.inverse.map (T'.map (L.counitIso.hom.app x))) hm
end Square

section Paste
variable {C D E F G H : Type*} [Category* C] [Category* D] [Category* E] [Category* F] [Category* G] [Category* H]
variable {P : C ⥤ D} {P' : D ⥤ E} {Q : F ⥤ G} {Q' : G ⥤ H}
variable {S S' : C ⥤ F} {T T' : D ⥤ G} {V V' : E ⥤ H}
variable {i : P ⋙ T ≅ S ⋙ Q} {i' : P ⋙ T' ≅ S' ⋙ Q} {j : P' ⋙ V ≅ T ⋙ Q'} {j' : P' ⋙ V' ≅ T' ⋙ Q'}
variable {s : S ⟶ S'} {t : T ⟶ T'} {v : V ⟶ V'}

/-- Two adjacent modification squares paste along the shared directed transformation. -/
theorem pasteIso_naturality (hi : SquareNaturality i i' s t) (hj : SquareNaturality j j' t v) :
    SquareNaturality (SpanPayload.pasteIso i j) (SpanPayload.pasteIso i' j') s v := by
  apply NatTrans.ext
  funext x
  have left := congrArg Q'.map (square_app hi x)
  simp only [Functor.map_comp] at left
  have right := square_app hj (P.obj x)
  simp [SpanPayload.pasteIso,Category.assoc]
  rw [← Category.assoc,right,Category.assoc,left]
end Paste

section Lengths
universe u v
variable {B : Type u} [Category.{v} B] {Q : Endpoints.{u,v,u,v} B} (R : Q.Split) (A : B)
variable {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'}
variable (m : StrongTrans.Modification a b)
variable (U V : ∀ n, (Iterates.layer Q R Y n).obj (op A) ⥤ (Iterates.layer Q R Z n).obj (op A))
variable (i : ∀ n, (component R Y A n).functor ⋙ U n ≅ atEndpoint a (leg (src R) (dst R) A n) ⋙ (component R Z A n).functor)
variable (j : ∀ n, (component R Y A n).functor ⋙ V n ≅ atEndpoint b (leg (src R) (dst R) A n) ⋙ (component R Z A n).functor)
variable (v : ∀ n, U n ⟶ V n)

/-- Naturality of every component comparison implies naturality of the actual assembled evaluation comparison. -/
theorem evaluation_modification_of_components
    (h : ∀ n, SquareNaturality (i n) (j n) (endpointCell (leg (src R) (dst R) A n) m) (v n)) :
    SquareNaturality (evaluation_of_components a R A U i) (evaluation_of_components b R A V j)
      (endpointCell (wholeLeg (src R) (dst R) A) m) (Sigma.natTrans.sigma v) := by
  apply pasteIso_naturality (t := taggedModification m (leg (src R) (dst R) A))
  · apply inverseSquare_naturality
    exact compare_modification m (src R) (dst R) A
  · apply NatTrans.ext
    funext ⟨n,x⟩
    exact congrArg Sigma.SigmaHom.mk (square_app (h n) x)
end Lengths

end ContextualComposition.GrothendieckStep.TelescopeGradeChange
