import ContextualComposition.NativeTriple
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeAssoc
namespace Grading209
set_option backward.isDefEq.respectTransparency false
abbrev B := Discrete Unit
def b : B := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of (Discrete Nat))
  extend _ := (Functor.const _).obj b
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def prim (n : Nat) : (power S 1).apex := pair P.grades (𝟭 B) b (Discrete.mk n)
def blockTwo : tel S := ⟨2,pair P.grades _ (prim 4) (Discrete.mk 7)⟩
def blockOne : tel S := ⟨1,prim 9⟩
def emp : tel S := ⟨0,b⟩
def row0 : strings S := ⟨0,b⟩
def row1 : strings S := ⟨1,blockTwo⟩
def row2 : strings S := ⟨2,⟨emp,blockOne,rfl⟩⟩
def x : Three.strings3 S := ⟨3,⟨⟨row0,row1,rfl⟩,row2,rfl⟩⟩
noncomputable abbrev M := Three.mergeRows S
noncomputable abbrev I := Three.mapRows S
-- Both routes have 3 intermediate blocks, 3 primitive grades, and identical endpoints.
example : (M.obj x).1 = (I.obj x).1 := rfl
def shape : (word S 3).apex → List Nat := fun w => [w.fst.fst.1,w.fst.snd.1,w.snd.1]
example : shape (M.obj x).2 = [2,0,1] := rfl
example : shape (I.obj x).2 = [0,2,1] := rfl
theorem constantTag {u v : tel S} (f : u ⟶ v) : u.1 = v.1 := by cases f; rfl
theorem rigid {x y : (word S 3).apex} (h : x ⟶ y) : shape x = shape y := by
  exact congrArg₂ List.cons (constantTag h.hom.fst.hom.fst)
    (congrArg₂ List.cons (constantTag h.hom.fst.hom.snd) (congrArg (fun n => [n]) (constantTag h.hom.snd)))
theorem noArc (f : M.obj x ⟶ I.obj x) : False := by
  have t := (outer S 3).map_surjective (X := (M.obj x).2) (Y := (I.obj x).2) f
  obtain ⟨g,_⟩ := t
  exact (by decide : [2,0,1] ≠ [0,2,1]) (rigid g)
-- Not even a natural transformation in this direction, despite final functor equality.
example (h : M ⟶ I) : False := noArc (h.app x)
example : M ⋙ flatten S = I ⋙ flatten S := Three.flatten_assoc S
example : ((M ⋙ flatten S).obj x).1 = 3 := rfl
-- Only the terminal payload distinguishes these arrows: base, grade, entire nesting are fixed.
inductive H | pt
instance : Category H where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp := by intros; apply List.nil_append
  comp_id := by intros; apply List.append_nil
  assoc := by intros; apply List.append_assoc
def Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of H)
def p := pair Y (Three.dest S) x H.pt
def t (l : List Nat) : p ⟶ p := arrow (𝟙 x) l
def val {Z : Type*} [Category* Z] (e : Z ⥤ B) : Total Y e ⥤ H where
  obj y := payload Y e y
  map f := payloadMap f
  map_id _ := rfl
  map_comp f g := (payload_comp f g).trans (congrArg (fun l : List Nat => (show List Nat from payloadMap f) ++ l) (List.append_nil (payloadMap g)))
theorem wval {K L : Type*} [Category* K] [Category* L] (r : K ⥤ L) (d : L ⥤ B)
    {e : K ⥤ B} (h : r ⋙ d = e) {u v : Total Y e} (f : u ⟶ v) :
    (show List Nat from (val d).map ((SpanPayload.totalMap Y r d h).map f)) = (show List Nat from (val e).map f) := by
  subst e; rfl
noncomputable abbrev A := Three.weightedOuter S Y ⋙ BlockCartesian.All.weighted S Y
noncomputable abbrev C := Three.weightedInner S Y ⋙ BlockCartesian.All.weighted S Y
theorem ar {u v : Total Y (Three.dest S)} (f : u ⟶ v) :
    (show List Nat from (val (rightLeg S)).map (A.map f)) = (show List Nat from (val _).map f) :=
  (wval (flatten S) (rightLeg S) (flatten_dest S) ((Three.weightedOuter S Y).map f)).trans
    (wval M (Rows.dest S) (Three.merge_dest S) f)
theorem cr {u v : Total Y (Three.dest S)} (f : u ⟶ v) :
    (show List Nat from (val (rightLeg S)).map (C.map f)) = (show List Nat from (val _).map f) :=
  (wval (flatten S) (rightLeg S) (flatten_dest S) ((Three.weightedInner S Y).map f)).trans
    (wval I (Rows.dest S) (Three.map_dest S) f)
def f := t [3,1]
def g := t [4,8]
example : gradeMap (f ≫ g) = gradeMap (g ≫ f) := rfl
example : (show List Nat from (val _).map (A.map (f ≫ g))) = [3,1,4,8] := by rw [ar,(val _).map_comp]; rfl
example : (show List Nat from (val _).map (C.map (g ≫ f))) = [4,8,3,1] := by rw [cr,(val _).map_comp]; rfl
example : TelescopeSquares.Aligned (A.map (f ≫ g)) (C.map (f ≫ g)) := NativeCube.functorAlign (Three.weighted_assoc S Y) _
end Grading209
