module
public import ContextualComposition.StrictTelCells

/-! Restricting and extending the compatible 2-cells in the strict
telescope comparison of Kamiya 2.9 and 2.20. -/

@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelCells

open CategoryTheory CategoryTheory.Limits SpanApex NativeBlocks
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictTelOperations StrictTelMapLaws StrictTelNested StrictTelCartesian

universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

variable {B : Type b} [Category.{max b w} B]
variable {U V W U' V' : Span (B := B)}

variable {P Q : Endpoints.{b,max b w,b,max b w} B} (S : P.Split) (T : Q.Split)
variable {F G : Over (power S 1) (power T 1)} (s : Cell F G) (M : Ops (power S 1)) (N : Ops (power T 1))

/-- The two sides are whiskering the *same* directed primitive transformation
on the literal evaluation functors. Strict map equations identify their
sources and targets; HEq suppresses only the corresponding equality casts. -/
def AlgebraCell (A : Over (whole S) (power S 1)) (D : Over (whole T) (power T 1)) :=
  ∀ x, HEq (s.nat.app (A.functor.obj x)) (D.functor.map ((telescopeCell S T s).nat.app x))

private theorem app_iff {X Y : Type*} [Category* X] [Category* Y] {F F' G G' : X ⥤ Y}
    (a : F ⟶ G) (b : F' ⟶ G') (f : F = F') (g : G = G') :
    (∀ x, HEq (a.app x) (b.app x)) ↔ a = eqToHom f ≫ b ≫ eqToHom g.symm := by
  subst F'; subst G'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id,heq_eq_eq]
  exact ⟨fun h => NatTrans.ext (funext h),fun h x => congrArg (fun t => NatTrans.app t x) h⟩

theorem algebraCell_eq (A : Over (whole S) (power S 1)) (D : Over (whole T) (power T 1))
    (hf : AlgebraMap S T F A D) (hg : AlgebraMap S T G A D) :
    AlgebraCell S T s A D ↔ Functor.whiskerLeft A.functor s.nat =
      eqToHom hf ≫ Functor.whiskerRight (telescopeCell S T s).nat D.functor ≫ eqToHom hg.symm :=
  app_iff (Functor.whiskerLeft A.functor s.nat) (Functor.whiskerRight (telescopeCell S T s).nat D.functor) hf hg

theorem restriction (A : Over (whole S) (power S 1)) (D : Over (whole T) (power T 1)) (h : AlgebraCell S T s A D) :
    UnitCell S T s (readOperations S A) (readOperations T D) ∧
    TensorCell S T s (readOperations S A) (readOperations T D) := by
  constructor
  · intro x
    have z := h ⟨0,x⟩
    refine z.trans ?_
    exact heq_of_eq (D.functor.map_id ⟨0,x⟩)
  · intro x
    let z := (concatenate S 1 1).functor.obj x
    have e := Functor.congr_obj (StrictTelMap.glue_cut S 1) x
    change (cutLast S 1).functor.obj z = x at e
    let L := (concatenate T 1 1).functor ⋙ incl T 2 ⋙ D.functor
    have rem {a b : (Pair (power S 1) (power S 1)).apex} (eq : a = b) :
        HEq (L.map ((bothCell s s).nat.app a)) (L.map ((bothCell s s).nat.app b)) := by cases eq; rfl
    refine (h ⟨2,z⟩).trans ?_
    exact rem e

theorem arbitrary_iff (A : StrictTelAlgebra.Algebra S) (D : StrictTelAlgebra.Algebra T)
    (hf : AlgebraMap S T F A.action D.action) (hg : AlgebraMap S T G A.action D.action) :
    AlgebraCell S T s A.action D.action ↔
      UnitCell S T s (readOperations S A.action) (readOperations T D.action) ∧
      TensorCell S T s (readOperations S A.action) (readOperations T D.action) := by
  let m := StrictTelAlgebra.read S A
  let n := StrictTelAlgebra.read T D
  have eqA : StrictTelFold.eval S m.operations = A.action := congrArg StrictTelAlgebra.Algebra.action (StrictTelAlgebra.writeRead S A)
  have eqD : StrictTelFold.eval T n.operations = D.action := congrArg StrictTelAlgebra.Algebra.action (StrictTelAlgebra.writeRead T D)
  refine ⟨restriction S T s A.action D.action, ?_⟩
  rintro ⟨u,mu⟩
  have h : AlgebraCell S T s (StrictTelFold.eval S m.operations) (StrictTelFold.eval T n.operations) := by
    rintro ⟨k,x⟩
    exact all_of_unit_tensor S T s m.operations n.operations (map_read S T F _ _ hf) (map_read S T G _ _ hg) u mu k x
  exact (congrArg₂ (AlgebraCell S T s) eqA eqD).mp h

/-- The hom-fibre bijection retains the whole underlying transformation. -/
def cellEquiv (A : StrictTelAlgebra.Algebra S) (D : StrictTelAlgebra.Algebra T)
    (hf : AlgebraMap S T F A.action D.action) (hg : AlgebraMap S T G A.action D.action) :
    {t : Cell F G // AlgebraCell S T t A.action D.action} ≃
    {t : Cell F G // UnitCell S T t (readOperations S A.action) (readOperations T D.action) ∧
      TensorCell S T t (readOperations S A.action) (readOperations T D.action)} :=
  Equiv.subtypeEquivRight fun t => arbitrary_iff S T t A D hf hg

end ContextualComposition.GrothendieckStep.StrictTelCells
