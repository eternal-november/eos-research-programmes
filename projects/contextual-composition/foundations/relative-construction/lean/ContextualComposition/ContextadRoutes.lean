module
public import ContextualComposition.WeightedCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadRoutes
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex
set_option backward.isDefEq.respectTransparency false
universe u v
section Natural
variable {C D : Type*} [Category* C] [Category* D]
variable (F : C ⥤ Cat.{v,u}) {G H : D ⥤ C} (a : G ⟶ H)
set_option backward.defeqAttrib.useBackward true in
def preCell : Grothendieck.pre F G ⟶ Grothendieck.map (whiskerRight a F) ⋙ Grothendieck.pre F H where
  app x := Grothendieck.toTransport ((Grothendieck.pre F G).obj x) (a.app x.base)
  naturality x y f := by
    fapply Grothendieck.ext
    · exact a.naturality f.base
    · simp
end Natural
section Maps
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
structure Operation (U V : Span (B := B)) where
  grade : U.apex ⥤ V.apex
  over : grade ⋙ V.source = U.source
  leg : grade ⋙ V.dest ⟶ U.dest
abbrev Map (i j : Nat) := Operation (power S i) (power S j)
variable {S}
def identity (i : Nat) : Map S i i := ⟨𝟭 _,rfl,𝟙 _⟩
def comp {i j k : Nat} (f : Map S i j) (g : Map S j k) : Map S i k :=
  ⟨f.grade ⋙ g.grade,(congrArg (f.grade ⋙ ·) g.over).trans f.over,pasteLift _ _ _ _ _ f.leg g.leg⟩
def tensor (m : ContextadTotal.Native S) : Map S 2 1 := ⟨m.grade,m.over,m.delta⟩
/-- Prefix a block, leaving its grade functor unchanged. The source leg of the
interior operation is strict; its endpoint leg is only a transformation. -/
noncomputable def inside (k : Nat) {i j : Nat} (f : Map S i j) : Map S (k+i) (k+j) := by
  let c := blocks S k i
  let d := blocks S k j
  have glue : c.first ⋙ (power S k).dest = (c.rest ⋙ f.grade) ⋙ (power S j).source :=
    c.glue.trans (congrArg (c.rest ⋙ ·) f.over.symm)
  let g := d.assemble c.first (c.rest ⋙ f.grade) glue
  exact ⟨g,(congrArg (g ⋙ ·) d.source.symm).trans ((congrArg (· ⋙ _) (d.first_assemble ..)).trans c.source),
    eqToHom ((congrArg (g ⋙ ·) d.dest.symm).trans (congrArg (· ⋙ (power S j).dest) (d.rest_assemble c.first (c.rest ⋙ f.grade) glue))) ≫
      whiskerLeft c.rest f.leg ≫ eqToHom c.dest⟩
/-- The suffix grade is pulled along the (possibly noninvertible) endpoint leg.
The raw comparison is the cartesian arrow in the category of primitive grades. -/
def suffixRaw {U V : Span (B := B)} (r : U.apex ⥤ V.apex) (l : r ⋙ V.dest ⟶ U.dest) :
    restrict P.grades U.dest V.dest r l ⋙ second P V.dest ⟶ second P U.dest :=
  NatTrans.op (preCell (P.grades ⋙ Cat.opFunctor) (NatTrans.op l))
def appendMap {U V : Span (B := B)} (f : Operation U V) : Operation (append P S U) (append P S V) :=
  ⟨restrict P.grades _ _ f.grade f.leg,congrArg (gradeProjection (Y := P.grades) (e := U.dest) ⋙ ·) f.over,
    whiskerRight (suffixRaw (P := P) (U := U) (V := V) f.grade f.leg) (right P S)⟩
noncomputable def suffix {i j : Nat} (f : Map S i j) : Map S (i+1) (j+1) := by
  change Operation (power S (i+1)) (power S (j+1))
  rw [succ_power S i,succ_power S j]
  exact appendMap f
end Maps
end ContextualComposition.GrothendieckStep.ContextadRoutes
