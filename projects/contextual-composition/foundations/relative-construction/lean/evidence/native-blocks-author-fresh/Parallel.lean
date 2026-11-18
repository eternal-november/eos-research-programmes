import ContextualComposition.NativeBlocks
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks SpanApex
namespace Parallel
inductive G | pt
instance : Category G where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp := by intros; apply List.nil_append
  comp_id := by intros; apply List.append_nil
  assoc := by intros; apply List.append_assoc
abbrev B := Discrete Unit
def base : B := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of G)
  extend _ := (Functor.const _).obj base
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def p : (power S 1).apex := pair P.grades (𝟭 B) base G.pt
def endo (l : List Nat) : p ⟶ p := arrow (𝟙 base) l
def x : part S (1,1) := ⟨p,p,rfl⟩
def edge (l r : List Nat) : x ⟶ x := ⟨⟨endo l,endo r,Subsingleton.elim _ _⟩⟩
def label {x y : Apex P} (f : x ⟶ y) : List Nat := payloadMap f
theorem label_align {x y x' y' : Apex P} {f : x ⟶ y} {g : x' ⟶ y'}
    (h : TelescopeSquares.Aligned f g) : label f = label g := by
  obtain ⟨hx,hy,h⟩ := h
  subst x'; subst y'; simpa using congrArg label (show f = g from by simpa using h)
noncomputable abbrev j := (blocks S 1 1).joinFunctor
abbrev first : (power S 2).apex ⥤ (power S 1).apex := gradeProjection
abbrev last : (power S 2).apex ⥤ (power S 1).apex := second P (power S 1).dest
theorem firstMap : j ⋙ first = Strict.fst _ _ := (blocks S 1 1).join_first
theorem lastMap : j ⋙ last = Strict.snd _ _ := by
  have e : (blocks S 1 1).rest = last := Cut.nextRest_grade S (emptyCut S (power S 1))
  exact (congrArg (j ⋙ ·) e.symm).trans (blocks S 1 1).join_rest
def f := edge [1,2] [8]
def g := edge [5] [9,3]
example : label (first.map (j.map (f ≫ g))) = [1,2,5] := label_align (NativeCube.functorAlign firstMap (f ≫ g))
example : label (last.map (j.map (f ≫ g))) = [8,9,3] := label_align (NativeCube.functorAlign lastMap (f ≫ g))
example : label (last.map (j.map (g ≫ f))) = [9,3,8] := label_align (NativeCube.functorAlign lastMap (g ≫ f))
example : j.map (f ≫ g) ≠ j.map (g ≫ f) := by
  intro h
  have l := congrArg (fun u => label (last.map u)) h
  have a : label (last.map (j.map (f ≫ g))) = [8,9,3] := label_align (NativeCube.functorAlign lastMap (f ≫ g))
  have b : label (last.map (j.map (g ≫ f))) = [9,3,8] := label_align (NativeCube.functorAlign lastMap (g ≫ f))
  exact (by decide : [8,9,3] ≠ [9,3,8]) (a.symm.trans (l.trans b))
end Parallel
