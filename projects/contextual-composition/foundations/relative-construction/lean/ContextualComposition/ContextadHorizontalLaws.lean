module
public import ContextualComposition.ContextadInsideCells
public import ContextualComposition.ContextadStandardLaws
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadHorizontalLaws
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadNativeLaws ContextadLawTransport
open ContextadCellPasting ContextadCellWhisker ContextadAppendCells ContextadInsideCells
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
structure Edge (n : Nat) where
  src : Map S n 1
  dst : Map S n 1
  cell : Cell src dst
def edge {n : Nat} {f g : Map S n 1} (c : Cell f g) : Edge (S := S) n := ⟨f,g,c⟩
/- Adjacent edges may use different cuts and different orders of contraction.
A seam is native data on the grade apices, including the outgoing endpoint triangle,
not any assertion about an evaluated base or payload functor. -/
abbrev Seam {n : Nat} (e f : Edge (S := S) n) := Cell e.dst f.src
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
noncomputable def triSwitch : Edge (S := S) 2 := edge (before c.assoc (inside 1 (leftUnit d)))
noncomputable def triLeft : Edge (S := S) 2 := edge (after (insideCell 1 c.left) (tensor m))
noncomputable def triRight : Edge (S := S) 2 := edge (after (suffixCell c.right) (tensor m))
noncomputable def pent1 : Edge (S := S) 4 := edge (after (suffixCell c.assoc) (tensor m))
noncomputable def pent2 : Edge (S := S) 4 := edge (before c.assoc (inside 1 (firstTwo m)))
noncomputable def pent3 : Edge (S := S) 4 := edge (after (insideCell 1 c.assoc) (tensor m))
noncomputable def pent4 : Edge (S := S) 4 := edge (before c.assoc (suffix (firstTwo m)))
noncomputable def pent5 : Edge (S := S) 4 := edge (before c.assoc (inside 2 (tensor m)))
/- No uniqueness or canonicity of these seams is asserted; when an application
obtains a seam from route equality it may take the identity cell after transport. -/
structure TriangleLink {n} (right switch left : Edge (S := S) n) where
  start : Cell right.src switch.src
  middle : Seam switch left
  finish : Cell left.dst right.dst
structure PentagonLink {n} (a b c d e : Edge (S := S) n) where
  start : Cell a.src d.src
  oneTwo : Seam a b
  twoThree : Seam b c
  fourFive : Seam d e
  finish : Cell e.dst c.dst
abbrev TriangleSeams := TriangleLink (triRight d m c) (triSwitch d m c) (triLeft d m c)
abbrev PentagonSeams := PentagonLink (pent1 d m c) (pent2 d m c) (pent3 d m c) (pent4 d m c) (pent5 d m c)
section Paths
variable {n : Nat}
inductive Path : Map S n 1 → Map S n 1 → Type (max u v)
  | one {f g} : Cell f g → Path f g
  | more {f g h} : Cell f g → Path g h → Path f h
def composite {f g : Map S n 1} : Path f g → Cell f g
  | .one c => c
  | .more c p => thenCell c (composite p)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
noncomputable def paste {f g : Map S n 1} : Path f g → (evaluate Y f A ⟶ evaluate Y g A)
  | .one c => (evalCell Y c A).hom
  | .more c p => (evalCell Y c A).hom ≫ paste p
theorem paste_eq {f g : Map S n 1} : (p : Path f g) → paste Y A p = (evalCell Y (composite p) A).hom
  | .one _ => rfl
  | .more c p => (congrArg ((evalCell Y c A).hom ≫ ·) (paste_eq p)).trans (evaluatedComp Y _ _ A).symm
theorem sameCell {f g : Map S n 1} (a b : Cell f g) (h : ∀ x, a.grade.hom.app x = b.grade.hom.app x) : a = b := by
  have t : a.grade = b.grade := Iso.ext (NatTrans.ext (funext h))
  cases a; cases b; cases t; rfl
theorem transport {f g : Map S n 1} (p q : Path f g) (h : ∀ x, (composite p).grade.hom.app x = (composite q).grade.hom.app x) :
    paste Y A p = paste Y A q :=
  (paste_eq Y A p).trans ((congrArg (fun c => (evalCell Y c A).hom) (sameCell _ _ h)).trans (paste_eq Y A q).symm)
end Paths
variable (t : TriangleSeams d m c) (p : PentagonSeams d m c)
noncomputable def triLong : Path (triRight d m c).src (triRight d m c).dst :=
  .more t.start (.more (triSwitch d m c).cell (.more t.middle (.more (triLeft d m c).cell (.one t.finish))))
noncomputable def triShort : Path (triRight d m c).src (triRight d m c).dst := .one (triRight d m c).cell
noncomputable def pentLong : Path (pent1 d m c).src (pent3 d m c).dst :=
  .more (pent1 d m c).cell (.more p.oneTwo (.more (pent2 d m c).cell (.more p.twoThree (.one (pent3 d m c).cell))))
noncomputable def pentShort : Path (pent1 d m c).src (pent3 d m c).dst :=
  .more p.start (.more (pent4 d m c).cell (.more p.fourFive (.more (pent5 d m c).cell (.one p.finish))))
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
theorem triangle (h : ∀ x, (composite (triLong d m c t)).grade.hom.app x = (composite (triShort d m c)).grade.hom.app x) :
    paste Y A (triLong d m c t) = paste Y A (triShort d m c) := transport Y A _ _ h
theorem pentagon (h : ∀ x, (composite (pentLong d m c p)).grade.hom.app x = (composite (pentShort d m c p)).grade.hom.app x) :
    paste Y A (pentLong d m c p) = paste Y A (pentShort d m c p) := transport Y A _ _ h
end ContextualComposition.GrothendieckStep.ContextadHorizontalLaws
