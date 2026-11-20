module
public import ContextualComposition.AmbientNativeModification
public import ContextualComposition.ContextadCoherentDetection
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientScheduleRealization
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadLawTransport ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadCellPasting ContextadHorizontalLaws ContextadSchedule ContextadNativeLaws AmbientNativeModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {i j : Nat} {r s t : ContextadRoutes.Map S i j}
theorem comp {c : Cell r s} {e : Cell s t} (p : gradeCart r) (q : gradeCart s) (h : gradeCart t) :
    modification (thenCell c e) p h = (modification c p q).vcomp (modification e q h) := by
  apply StrongTrans.Modification.ext; funext X
  apply extRaw S; intro x
  change Aligned (atRaw S (cmp _ p h X).hom x) (atRaw S ((cmp c p q X).hom ≫ (cmp e q h X).hom) x)
  rw [compAt]
  apply (cmpAt (thenCell c e) p h x).trans
  exact (NativeCube.ofEq (NatTrans.congr_app (rawComp (underlying X) c e) x)).trans ((cmpAt c p q x).comp (cmpAt e q h x)).symm
variable {n : Nat} {f g : ContextadRoutes.Map S n 1}
noncomputable def realize {f g : ContextadRoutes.Map S n 1} : (l : Path f g) → (p : gradeCart f) → (q : gradeCart g) →
    StrongTrans.Modification (AmbientPseudonaturality.operation S f p) (AmbientPseudonaturality.operation S g q)
  | .one c, p,q => modification c p q
  | .more c l,p,q => (modification c p (presIso c.grade.symm p)).vcomp (realize l (presIso c.grade.symm p) q)
theorem realize_eq {f g : ContextadRoutes.Map S n 1} : (l : Path f g) → (p : gradeCart f) → (q : gradeCart g) → realize l p q = modification (composite l) p q
  | .one _,_,_ => rfl
  | .more c l,p,q => by
    unfold realize composite
    rw [realize_eq l]
    exact (comp p (presIso c.grade.symm p) q).symm
theorem transport (a b : Path f g) (p : gradeCart f) (q : gradeCart g)
    (h : ∀ x, (composite a).grade.hom.app x = (composite b).grade.hom.app x) :
    realize a p q = realize b p q := by rw [realize_eq,realize_eq,sameCell _ _ h]
theorem reflect {a b : Cell r s} (p : gradeCart r) (q : gradeCart s)
    (h : modification a p q = modification b p q) : a = b := by
  let X : Obj.{u,v} B := ContextadScheduleDetection.observer B
  have eqGrade : ∀ x, a.grade.hom.app x = b.grade.hom.app x := by
    intro x
    let w : Raw S X i := pair (underlying X) (power S i).dest x ((power S i).dest.obj x)
    have e : (cmp a p q X).hom = (cmp b p q X).hom := congrArg (fun t => t.app X) h
    have k := ((cmpAt a p q w).symm.trans ((NativeCube.ofEq (congrArg (fun t => atRaw S t w) e)).trans (cmpAt b p q w))).eq
    exact (ContextadCellWhisker.readGrade a X w).symm.trans ((congrArg gradeMap k).trans (ContextadCellWhisker.readGrade b X w))
  have e : a.grade = b.grade := Iso.ext (NatTrans.ext (funext eqGrade))
  cases a; cases b; cases e; rfl
theorem faithfulPaths (a b : Path f g) (p : gradeCart f) (q : gradeCart g) :
    realize a p q = realize b p q ↔ ∀ x, (composite a).grade.hom.app x = (composite b).grade.hom.app x := by
  refine ⟨fun k => ?_,transport a b p q⟩
  rw [realize_eq,realize_eq] at k
  rw [reflect p q k]
  exact fun _ => rfl
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
theorem triangle (h : TriangleLaw d m c) :
    realize (triLong d m c (canonicalTriangle d m c)) (triStartCart d m c) (presIso (composite (triShort d m c)).grade.symm (triStartCart d m c)) =
    realize (triShort d m c) (triStartCart d m c) (presIso (composite (triShort d m c)).grade.symm (triStartCart d m c)) := transport _ _ _ _ h
theorem pentagon (h : PentagonLaw d m c) :
    realize (pentLong d m c (canonicalPentagon d m c)) (pentStartCart d m c) (presIso (composite (pentLong d m c (canonicalPentagon d m c))).grade.symm (pentStartCart d m c)) =
    realize (pentShort d m c (canonicalPentagon d m c)) (pentStartCart d m c) (presIso (composite (pentLong d m c (canonicalPentagon d m c))).grade.symm (pentStartCart d m c)) := transport _ _ _ _ h
end ContextualComposition.GrothendieckStep.AmbientScheduleRealization
