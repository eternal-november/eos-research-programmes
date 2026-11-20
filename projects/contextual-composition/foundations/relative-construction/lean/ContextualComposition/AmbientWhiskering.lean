module
public import ContextualComposition.AmbientCellTrace
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientWhiskering
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells AmbientRoundTrip AmbientCellFunctor AmbientCellTrace AmbientBlockIteration WordTrace NativeBlocks
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
section Generic
variable {B : Type u} [Category.{v} B] {Y Z W : Bᵒᵖ ⥤ Cat.{v,u}}
variable {a a' : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} {b b' : StrongTrans Z.toPseudofunctor' W.toPseudofunctor'}
abbrev Mod {Q R : Bᵒᵖ ⥤ Cat.{v,u}} (f g : StrongTrans Q.toPseudofunctor' R.toPseudofunctor') := StrongTrans.Hom f g
def ev {Q R : Bᵒᵖ ⥤ Cat.{v,u}} {f g : StrongTrans Q.toPseudofunctor' R.toPseudofunctor'} (i : Mod f g) (x : Total Q (𝟭 B)) := edge ((totalCell i.as).app x)
theorem frame {a₁ a₂ b₁ b₂ : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} (p : a₁ = a₂) (q : b₂ = b₁) (i : Mod a₂ b₂) (x) :
    ev (eqToHom p ≫ i ≫ eqToHom q) x = ev i x := by subst a₂; subst b₂; simp
theorem evLeft (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (t : Mod b b') (x) :
    ev (StrongTrans.whiskerLeft a t) x = ev t ((totalStrong a).obj x) := by
  unfold ev
  rw [totalApp,totalApp]; rfl
theorem evRight (t : Mod a a') (b : StrongTrans Z.toPseudofunctor' W.toPseudofunctor') (x) :
    ev (StrongTrans.whiskerRight t b) x = Edge.map (totalStrong b) (ev t x) := by
  unfold ev
  rw [totalApp,totalApp]
  exact same (NativeCube.functorAlign (strongIncl b _) _)
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Y Z W : PackedCuts.Psh.{u,max u v,u,v} B}
variable {a a' : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} {b b' : StrongTrans Z.toPseudofunctor' W.toPseudofunctor'}
noncomputable abbrev mapCell (n : Nat) (t : Mod a a') : Mod (blockStrong (S := S) a n) (blockStrong (S := S) a' n) := ⟨blockMod S t.as n⟩
theorem evMap (n : Nat) (t : Mod a a') (x) :
    WordTrace.read S Z n (ev (mapCell S n t) x) = (grades S n x,ev t (last S n x)) := trace S t.as n x
theorem objTrace (n : Nat) (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (x) :
    (grades S n ((blockTotal S a n).obj x),last S n ((blockTotal S a n).obj x)) =
    (grades S n x,(totalStrong a).obj (last S n x)) := by
  let F := blockTotal S a n
  have h := blockTrace S a n (idEdge x)
  rw [show Edge.map F (idEdge x) = idEdge (F.obj x) from same (NativeCube.ofEq (F.map_id x))] at h
  exact congrArg (fun z => (z.1,z.2.src)) h
theorem mapLeft (n : Nat) (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') (t : Mod b b') :
    mapCell S n (StrongTrans.whiskerLeft a t) = eqToHom (blockComp S a b n) ≫ StrongTrans.whiskerLeft (blockStrong (S := S) a n) (mapCell S n t) ≫ eqToHom (blockComp S a b' n).symm := by
  apply StrongTrans.Hom.ext; apply cellExt; intro x
  change ev _ x = ev _ x
  rw [frame,evLeft,encodedBlock]
  apply read_injective S _ n
  rw [evMap,evMap,evLeft]
  exact (congrArg (fun z => (z.1,ev t z.2)) (objTrace S n a x)).symm
theorem mapRight (n : Nat) (t : Mod a a') (b : StrongTrans Z.toPseudofunctor' W.toPseudofunctor') :
    mapCell S n (StrongTrans.whiskerRight t b) = eqToHom (blockComp S a b n) ≫ StrongTrans.whiskerRight (mapCell S n t) (blockStrong (S := S) b n) ≫ eqToHom (blockComp S a' b n).symm := by
  apply StrongTrans.Hom.ext; apply cellExt; intro x
  change ev _ x = ev _ x
  rw [frame,evRight,encodedBlock]
  apply read_injective S _ n
  rw [evMap,evRight,blockTrace,evMap]
end ContextualComposition.GrothendieckStep.AmbientWhiskering
