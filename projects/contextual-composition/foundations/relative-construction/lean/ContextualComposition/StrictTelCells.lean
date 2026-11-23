module
public import ContextualComposition.StrictTelCategories

/-! Actual transformations of strict span maps. Both feet of each
component are identity transports on the common base object. -/

@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelCells

open CategoryTheory CategoryTheory.Limits SpanApex NativeBlocks
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictTelOperations StrictTelMapLaws StrictTelNested StrictTelCartesian

universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

variable {B : Type b} [Category.{max b w} B]
variable {U V W U' V' : Span (B := B)}

structure Cell (F G : Over U V) where
  nat : F.functor ⟶ G.functor
  src : ∀ x, V.source.map (nat.app x) =
    eqToHom ((Functor.congr_obj F.source x).trans (Functor.congr_obj G.source x).symm)
  dst : ∀ x, V.dest.map (nat.app x) =
    eqToHom ((Functor.congr_obj F.dest x).trans (Functor.congr_obj G.dest x).symm)

variable {F G : Over U V}

def identity (F : Over U V) : Cell F F where
  nat := 𝟙 _
  src _ := by simp
  dst _ := by simp

def vcomp {H : Over U V} (s : Cell F G) (t : Cell G H) : Cell F H where
  nat := s.nat ≫ t.nat
  src _ := by simp [s.src,t.src]
  dst _ := by simp [s.dst,t.dst]

def beforeCell (J : Over W U) (s : Cell F G) : Cell (comp J F) (comp J G) where
  nat := Functor.whiskerLeft J.functor s.nat
  src _ := s.src _
  dst _ := s.dst _

def afterCell (s : Cell F G) (J : Over V W) : Cell (comp F J) (comp G J) where
  nat := Functor.whiskerRight s.nat J.functor
  src x := by
    change (J.functor ⋙ W.source).map _ = _
    rw [Functor.congr_hom J.source (s.nat.app x), s.src]
    simp
  dst x := by
    change (J.functor ⋙ W.dest).map _ = _
    rw [Functor.congr_hom J.dest (s.nat.app x), s.dst]
    simp

def bothCell {F' G' : Over U' V'} (s : Cell F G) (t : Cell F' G') : Cell (both F F') (both G G') where
  nat := {
    app x := ⟨⟨s.nat.app x.fst,t.nat.app x.snd,by
      rw [s.dst,t.src]; simp [Strict.ambient]⟩⟩
    naturality _ _ f := InducedCategory.hom_ext (CategoricalPullback.hom_ext
      (s.nat.naturality f.hom.fst) (t.nat.naturality f.hom.snd)) }
  src _ := s.src _
  dst _ := t.dst _

variable {P Q : Endpoints.{b,max b w,b,max b w} B}
variable (S : P.Split) (T : Q.Split)
variable {F G : Over (power S 1) (power T 1)} (s : Cell F G)

/-- Coordinatewise action on a chain, using the literal pullback matching
for each adjacent endpoint. -/
noncomputable def powerCell : (n : Nat) → Cell (StrictTelMap.powerMap S T F n) (StrictTelMap.powerMap S T G n)
  | 0 => identity _
  | 1 => s
  | n+2 => afterCell (beforeCell (cutLast S (n+1)) (bothCell (powerCell (n+1)) s)) (concatenate T (n+1) 1)

noncomputable def telescopeNat : (StrictTelMap.map S T F).functor ⟶ (StrictTelMap.map S T G).functor where
  app := fun ⟨n,x⟩ => (incl T n).map ((powerCell S T s n).nat.app x)
  naturality := by
    rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    exact ((incl T n).map_comp _ _).symm.trans
      ((congrArg ((incl T n).map) ((powerCell S T s n).nat.naturality f)).trans ((incl T n).map_comp _ _))

noncomputable def telescopeCell : Cell (StrictTelMap.map S T F) (StrictTelMap.map S T G) where
  nat := telescopeNat S T s
  src := by
    rintro ⟨n,x⟩
    change (power T n).source.map ((powerCell S T s n).nat.app x) = _
    exact (powerCell S T s n).src x
  dst := by
    rintro ⟨n,x⟩
    change (power T n).dest.map ((powerCell S T s n).nat.app x) = _
    exact (powerCell S T s n).dst x

theorem sameMap {X Y : Type*} [Category* X] [Category* Y]
    {F G : X ⥤ Y} (e : F = G) {x y : X} (f : x ⟶ y) : HEq (F.map f) (G.map f) := by cases e; rfl

theorem prefix_cell (n : Nat) (x : (power S (n+2)).apex) :
    HEq ((NativeAssoc.front T (n+1)).map ((powerCell S T s (n+2)).nat.app x))
      ((powerCell S T s (n+1)).nat.app ((NativeAssoc.front S (n+1)).obj x)) :=
  sameMap (StrictTelMap.glue_prefix T (n+1))
    ((bothCell (powerCell S T s (n+1)) s).nat.app ((cutLast S (n+1)).functor.obj x))

theorem suffix_cell (n : Nat) (x : (power S (n+2)).apex) :
    HEq ((NativeAssoc.last T (n+1)).map ((powerCell S T s (n+2)).nat.app x))
      (s.nat.app ((NativeAssoc.last S (n+1)).obj x)) :=
  sameMap (StrictTelMap.glue_suffix T (n+1))
    ((bothCell (powerCell S T s (n+1)) s).nat.app ((cutLast S (n+1)).functor.obj x))

private theorem mapHEq {X Y : Type*} [Category* X] [Category* Y] (R : X ⥤ Y)
    {x x' y y' : X} (hx : x = x') (hy : y = y') {f : x ⟶ y} {g : x' ⟶ y'} (h : HEq f g) :
    HEq (R.map f) (R.map g) := by subst x'; subst y'; cases eq_of_heq h; rfl

private theorem matchObj {x y : (Pair U V).apex} (h : x.fst = y.fst) (k : x.snd = y.snd) : x = y := by
  cases x; cases y; congr

private theorem matchHom {x x' y y' : (Pair U V).apex} (hx : x = x') (hy : y = y')
    {f : x ⟶ y} {g : x' ⟶ y'} (l : HEq f.hom.fst g.hom.fst) (r : HEq f.hom.snd g.hom.snd) : HEq f g := by
  subst x'; subst y'
  exact heq_of_eq (InducedCategory.hom_ext (CategoricalPullback.hom_ext (eq_of_heq l) (eq_of_heq r)))

variable (M : Ops (power S 1)) (N : Ops (power T 1))

def UnitCell := ∀ x, HEq (s.nat.app (M.unit.functor.obj x)) (𝟙 (N.unit.functor.obj x))

def TensorCell := ∀ x, HEq (s.nat.app (M.tensor.functor.obj x)) (N.tensor.functor.map ((bothCell s s).nat.app x))

def At (n : Nat) := ∀ x, HEq (s.nat.app ((StrictTelFold.comb S M n).functor.obj x))
  ((StrictTelFold.comb T N n).functor.map ((powerCell S T s n).nat.app x))

private theorem object_match (F : Over (power S 1) (power T 1)) (hf : Multiplicative F (M := M) (N := N))
    (k : Nat) (x : (power S (k+2)).apex) :
    (both F F).functor.obj ((cutLast S (k+1)).functor.obj x |> fun z =>
      (both (StrictTelFold.comb S M (k+1)) (StrictSpanAlgebra.id _)).functor.obj z) =
    (both (StrictTelFold.comb T N (k+1)) (StrictSpanAlgebra.id _)).functor.obj
      ((cutLast T (k+1)).functor.obj ((StrictTelMap.powerMap S T F (k+2)).functor.obj x)) := by
  apply matchObj
  · exact (Functor.congr_obj (comb_natural S T F M N hf (k+1)) ((NativeAssoc.front S (k+1)).obj x)).trans
      (congrArg (StrictTelFold.comb T N (k+1)).functor.obj (Functor.congr_obj (StrictTelMap.map_succ_prefix S T F k) x).symm)
  · exact (Functor.congr_obj (StrictTelMap.map_succ_suffix S T F k) x).symm

/-- Unit and binary compatibility of a directed transformation of strictly
operation-preserving span maps extend to every finite dependent chain. -/
theorem all_of_unit_tensor (hf : Multiplicative F (M := M) (N := N)) (hg : Multiplicative G (M := M) (N := N))
    (h₀ : UnitCell S T s M N) (h₂ : TensorCell S T s M N) (n : Nat) : At S T s M N n := by
  induction n with
  | zero => exact fun x => (h₀ x).trans (heq_of_eq (N.unit.functor.map_id _).symm)
  | succ k ih =>
    cases k with
    | zero => exact fun _ => HEq.rfl
    | succ k =>
      intro x
      let xx := (cutLast S (k+1)).functor.obj x
      let z := (both (StrictTelFold.comb S M (k+1)) (StrictSpanAlgebra.id _)).functor.obj xx
      have epF := object_match S T M N F hf k x
      have epG := object_match S T M N G hg k x
      refine (h₂ z).trans (mapHEq N.tensor.functor epF epG (matchHom epF epG ?_ ?_))
      · have h := ih xx.fst
        refine h.trans (mapHEq (StrictTelFold.comb T N (k+1)).functor
          (Functor.congr_obj (StrictTelMap.map_succ_prefix S T F k) x).symm
          (Functor.congr_obj (StrictTelMap.map_succ_prefix S T G k) x).symm
          (prefix_cell S T s k x).symm)
      · exact (suffix_cell S T s k x).symm

end ContextualComposition.GrothendieckStep.StrictTelCells
