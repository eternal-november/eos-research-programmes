import ContextualComposition.ContextadHorizontalModification
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep
open ContextadLawTransport ContextadCellPasting ContextadHorizontalLaws ContextadRoutes
namespace IndependentSeams
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {n : Nat} {a b c : Map S n 1}
def reverse (w : Cell a b) : Cell b a where
  grade := w.grade.symm
  source x := pureInverse (w.grade.app x) (w.source x)
  endpoint := by
    apply NatTrans.ext; funext x
    have h := NatTrans.congr_app w.endpoint x
    change (NativeBlocks.power S 1).dest.map (w.grade.hom.app x) ≫ b.leg.app x = a.leg.app x at h
    change (NativeBlocks.power S 1).dest.map (w.grade.inv.app x) ≫ a.leg.app x = b.leg.app x
    rw [← h,← Category.assoc,← Functor.map_comp,w.grade.inv_hom_id_app,Functor.map_id,Category.id_comp]
def finish (pfx : Cell a b) (other : Cell a c) : Cell b c := thenCell (reverse pfx) other
theorem finish_closes (pfx : Cell a b) (other : Cell a c) (x) :
    pfx.grade.hom.app x ≫ (finish pfx other).grade.hom.app x = other.grade.hom.app x := by
  change pfx.grade.hom.app x ≫ pfx.grade.inv.app x ≫ other.grade.hom.app x = _
  simp
-- In fact the grade test determines exactly one finish cell once the rest is pinned.
theorem finish_iff (pfx : Cell a b) (other : Cell a c) (j : Cell b c) :
    (∀ x, pfx.grade.hom.app x ≫ j.grade.hom.app x = other.grade.hom.app x) ↔
      j = finish pfx other := by
  constructor
  · intro h
    apply sameCell
    intro x
    apply (cancel_epi (pfx.grade.hom.app x)).mp
    exact (h x).trans (finish_closes pfx other x).symm
  · rintro rfl
    exact finish_closes pfx other
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : ContextadNativeLaws.Constraints d m)
-- Only the first two triangle seams are given. Choose the third *from the desired law*.
noncomputable def triangleFit (s : Cell (triRight d m C).src (triSwitch d m C).src)
    (j : Seam (triSwitch d m C) (triLeft d m C)) : TriangleSeams d m C :=
  ⟨s,j,finish (thenCell s (thenCell (triSwitch d m C).cell (thenCell j (triLeft d m C).cell)))
    (triRight d m C).cell⟩
theorem triangleFit_eq (s : Cell (triRight d m C).src (triSwitch d m C).src)
    (j : Seam (triSwitch d m C) (triLeft d m C)) (x : (NativeBlocks.power S 2).apex) :
    (composite (triLong d m C (triangleFit d m C s j))).grade.hom.app x =
    (composite (triShort d m C)).grade.hom.app x := by
  have w := finish_closes (thenCell s (thenCell (triSwitch d m C).cell (thenCell j (triLeft d m C).cell))) (triRight d m C).cell x
  simpa only [triLong,triShort,triangleFit,composite,thenCell,Iso.trans_hom,NatTrans.comp_app,Category.assoc] using w
-- Four pentagon seams given; choose the fifth *from the desired law*.
noncomputable def pentagonFit (s : Cell (pent1 d m C).src (pent4 d m C).src)
    (j : Seam (pent1 d m C) (pent2 d m C)) (k : Seam (pent2 d m C) (pent3 d m C))
    (l : Seam (pent4 d m C) (pent5 d m C)) : PentagonSeams d m C :=
  ⟨s,j,k,l, finish (thenCell s (thenCell (pent4 d m C).cell (thenCell l (pent5 d m C).cell)))
      (thenCell (pent1 d m C).cell (thenCell j (thenCell (pent2 d m C).cell (thenCell k (pent3 d m C).cell))))⟩
theorem pentagonFit_eq (s : Cell (pent1 d m C).src (pent4 d m C).src)
    (j : Seam (pent1 d m C) (pent2 d m C)) (k : Seam (pent2 d m C) (pent3 d m C))
    (l : Seam (pent4 d m C) (pent5 d m C)) (x : (NativeBlocks.power S 4).apex) :
    (composite (pentShort d m C (pentagonFit d m C s j k l))).grade.hom.app x =
    (composite (pentLong d m C (pentagonFit d m C s j k l))).grade.hom.app x := by
  have w := finish_closes (thenCell s (thenCell (pent4 d m C).cell (thenCell l (pent5 d m C).cell)))
    (thenCell (pent1 d m C).cell (thenCell j (thenCell (pent2 d m C).cell (thenCell k (pent3 d m C).cell)))) x
  simpa only [pentLong,pentShort,pentagonFit,composite,thenCell,Iso.trans_hom,NatTrans.comp_app,Category.assoc] using w
end IndependentSeams
