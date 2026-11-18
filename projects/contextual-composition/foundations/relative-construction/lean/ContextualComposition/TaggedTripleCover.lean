module
public import ContextualComposition.WholeEvaluator
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedTripleCover
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked TripleBoundary
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev target := Total Y (L (whole S) (whole S) (whole S)).dest
abbrev spanTag (n m k : Nat) := NativeAssoc.Three.mapProduct (NativeAssoc.Three.mapProduct (tag (power S) n) (tag (power S) m)) (tag (power S) k)
abbrev incl (n m k : Nat) := Lift.total (spanTag S n m k) Y
theorem covers (x : target S Y) : ∃ (n m k : Nat) (a : TripleTrace.input S Y n m k), (incl S Y n m k).obj a = x := by
  rcases x with ⟨⟨⟨⟨⟨n,a⟩,⟨m,b⟩,h⟩,⟨k,c⟩,j⟩,t⟩⟩
  exact ⟨n,m,k,pair Y _ ⟨⟨a,b,h⟩,c,j⟩ t.unop,rfl⟩
theorem detect {D : Type*} [Category* D] {F G : target S Y ⥤ D} (f g : F ⟶ G)
    (h : ∀ n m k, whiskerLeft (incl S Y n m k) f = whiskerLeft (incl S Y n m k) g) : f = g := by
  ext x
  obtain ⟨n,m,k,a,rfl⟩ := covers S Y x
  exact NatTrans.congr_app (h n m k) a
end ContextualComposition.GrothendieckStep.TaggedTripleCover
