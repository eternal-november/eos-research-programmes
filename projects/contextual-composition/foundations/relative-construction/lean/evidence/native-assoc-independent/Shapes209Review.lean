import ContextualComposition.NativeTriple
open CategoryTheory Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeBlocks.Nested NativeAssoc
namespace Shapes209
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
-- No quotient of all shapes by total length: these two different counts have different recursion.
def blocksIn : (n : Nat) → (Three.level S n).apex → Nat
  | 0,_ => 0
  | 1,q => q.1
  | n+2,q => blocksIn (n+1) q.fst + q.snd.1
theorem binaryCount (x : Rows.pairs S) : ((Rows.binary S).obj x).1 = x.fst.1+x.snd.1 := by
  rcases x with ⟨⟨a,p⟩,⟨b,q⟩,h⟩
  exact Rows.cat_len S ⟨a,Rows.fst S (a,b)⟩ b (Rows.snd S (a,b)) (Strict.commute _ _)
theorem outsideCount : (n : Nat) → (x : (Three.level S n).apex) → ((Three.outside S n).functor.obj x).1 = blocksIn S n x
  | 0,_ => rfl
  | 1,_ => rfl
  | n+2,x => by
    let I : Over (Three.rows S) (Three.rows S) := ⟨𝟭 _,rfl,rfl⟩
    let q := (Three.mapProduct (Three.outside S (n+1)) I).functor.obj x
    exact (binaryCount S q).trans (congrArg (·+x.snd.1) (outsideCount (n+1) x.fst))
example (x : Three.strings3 S) : ((Three.mergeRows S).obj x).1 = blocksIn S x.1 x.2 := outsideCount S x.1 x.2
example (x : Three.strings3 S) : ((Three.mapRows S).obj x).1 = x.1 := rfl
-- Empty three-level words, singleton empty row, and singleton row consisting of an empty block differ but flatten alike.
def y0 (b : B) : Three.strings3 S := ⟨0,b⟩
def y1 (b : B) : Three.strings3 S := ⟨1,⟨0,b⟩⟩
def y2 (b : B) : Three.strings3 S := ⟨1,⟨1,⟨0,b⟩⟩⟩
theorem no01 (b : B) (f : y0 S b ⟶ y1 S b) : False := by cases f
theorem no12 (b : B) (f : y1 S b ⟶ y2 S b) : False := by rcases f with ⟨f⟩; cases f
noncomputable abbrev E := Three.mergeRows S ⋙ flatten S
example (b : B) : (E S).obj (y0 S b) = (E S).obj (y1 S b) := rfl
example (b : B) : (E S).obj (y1 S b) = (E S).obj (y2 S b) := rfl
example (b : B) : ¬(E S).Full := by
  intro h; let _ := h
  exact no12 S b ((E S).preimage (X := y1 S b) (Y := y2 S b) (𝟙 _))
end Shapes209
