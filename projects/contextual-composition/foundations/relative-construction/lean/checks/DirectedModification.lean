import ContextualComposition.AmbientComparisonRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open ContextualComposition.GrothendieckStep NativeBlocks SpanApex FibreValue
open ContextadAmbientPayload AmbientBicategory AmbientCoordinates AmbientRoundTrip
open scoped CategoryTheory.Pseudofunctor.StrongTrans
namespace DirectedModification
noncomputable section
set_option backward.isDefEq.respectTransparency false
def V : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of Nat)
theorem thin (a b : Nat) (f g : a ⟶ b) : f = g := Subsingleton.elim _ _
def constF (n : Nat) : StrongTrans V.toPseudofunctor' V.toPseudofunctor' :=
  ContextadStrong.assemble (G := V) (H := V) (fun _ => (Functor.const Nat).obj n)
    (fun _ => Iso.refl _) (fun _ _ => thin _ _ _ _) (fun _ _ _ => thin _ _ _ _)
def up : StrongTrans.Modification (constF 0) (constF 1) where
  app _ := { app := fun _ => homOfLE (Nat.zero_le 1) : (Functor.const Nat).obj 0 ⟶ (Functor.const Nat).obj 1 }.toCatHom₂
  naturality _ := by apply Cat.Hom₂.ext; ext; exact thin _ _ _ _
def P : Endpoints.{0,0,0,0} Nat where
  grades := V
  extend A := (Functor.const Nat).obj A
  lift f := { app := fun _ => f }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
abbrev X : Obj.{0,0} Nat := V
abbrev f (n : Nat) : X ⟶ X := Bicategory.InducedBicategory.mkHom (constF n)
abbrev lifted : AmbientBicategory.map S 1 (f 0) ⟶ AmbientBicategory.map S 1 (f 1) := AmbientBicategory.cell S 1 (Bicategory.InducedBicategory.mkHom₂ ⟨up⟩)
def x : Raw S X 1 := pair _ _ (pair _ _ (2:Nat) (3:Nat)) (4:Nat)
theorem noReverse (n : Nat) (w : Raw S X n) :
    ¬ Nonempty (AmbientBicategory.map S n (f 1) ⟶ AmbientBicategory.map S n (f 0)) := by
  rintro ⟨m⟩
  let h := atRaw S m w
  let e := (power S n).dest
  let L := NativeTrace.leaf V e
  have hi (k : Nat) : encode S (AmbientBicategory.map S n (f k)) ⋙ L = L ⋙ totalStrong (constF k) :=
    (congrArg (· ⋙ L) (mapEncode S (f k) n)).trans (ContextadWeakAction.actionLeaf e (totalStrong (constF k)) (strongOver _))
  let k := eqToHom (Functor.congr_obj (hi 1) w).symm ≫ L.map h ≫ eqToHom (Functor.congr_obj (hi 0) w)
  have b : (1:Nat) ≤ 0 := leOfHom (payloadMap k)
  exact (by decide : ¬ (1:Nat) ≤ 0) b
example : ¬ IsIso lifted := by intro h; exact noReverse 1 x ⟨inv lifted⟩
end
end DirectedModification
