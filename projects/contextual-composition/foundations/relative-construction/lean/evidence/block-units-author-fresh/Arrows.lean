import ContextualComposition.BlockUnits
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep BlockUnits NativePacked
namespace Arrows213
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
-- Both endpoint squares preserve the distinguishability of arbitrary arrows,
-- including noninvertible ones. The equivalence used here evaluates a single word.
theorem faithful (s : Side) {x y : single S Y A} {f g : x ⟶ y}
    (h : (staged S Y A s).map f = (staged S Y A s).map g) : f = g := by
  let Q := isoWhiskerLeft (J S Y A s) (BlockCompositor.multiplicationSquare S Y A) ≪≫ eqToIso (nativeContract S Y A s)
  have p := Q.hom.naturality f
  have q := Q.hom.naturality g
  change (PackedCuts.mu S Y A).map ((staged S Y A s).map _) ≫ _ = _ at p q
  rw [h] at p
  exact (evaluation S Y A).map_injective ((cancel_epi (Q.hom.app x)).mp (p.symm.trans q))
theorem isoReflect (s : Side) {x y : single S Y A} (f : x ⟶ y) (i : IsIso ((staged S Y A s).map f)) : IsIso f := by
  let Q := isoWhiskerLeft (J S Y A s) (BlockCompositor.multiplicationSquare S Y A) ≪≫ eqToIso (nativeContract S Y A s)
  have p := (NatIso.isIso_map_iff Q f).mp ((PackedCuts.mu S Y A).map_isIso ((staged S Y A s).map f))
  exact isIso_of_reflects_iso f (evaluation S Y A)
end Arrows213

namespace Overlap213
open NativeBlocks
inductive B | star
instance : Category B where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of B)
  extend _ := 𝟭 _
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
inductive G | x
instance : Category G where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp := by intros; apply List.nil_append
  comp_id := by intros; apply List.append_nil
  assoc := by intros; apply List.append_assoc
abbrev Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of G)
abbrev A := B.star
def e : single S Y A := pair Y _ ⟨⟨0,A⟩,rfl⟩ G.x
def ar (k : List Nat) : e ⟶ e := arrow (𝟙 _) k
theorem ne : ar [1] ≫ ar [2] ≠ ar [2] ≫ ar [1] := fun h =>
  (by decide : [1,2] ≠ [2,1]) (congrArg (fun f : e ⟶ e => payloadMap f) h)
theorem noniso : ¬ IsIso (ar [1]) := by
  intro h
  let g := inv (ar [1])
  have p := congrArg (fun f : e ⟶ e => payloadMap f) (IsIso.hom_inv_id (ar [1]))
  rw [payload_comp] at p
  change [1] ++ ((show List Nat from payloadMap g) ++ []) = [] at p
  cases p
example (s : Side) : (staged S Y A s).map (ar [1] ≫ ar [2]) ≠ (staged S Y A s).map (ar [2] ≫ ar [1]) :=
  fun h => ne (Arrows213.faithful S Y A s h)
example (s : Side) : ¬ IsIso ((staged S Y A s).map (ar [1])) := fun h => noniso (Arrows213.isoReflect S Y A s _ h)
example (s : Side) : (staged S Y A s).map (ar [1]) ≫ (stagedUnit S Y A s).hom.app e =
    (stagedUnit S Y A s).hom.app e ≫ (target S Y A s).map (ar [1]) := (stagedUnit S Y A s).hom.naturality _
end Overlap213
