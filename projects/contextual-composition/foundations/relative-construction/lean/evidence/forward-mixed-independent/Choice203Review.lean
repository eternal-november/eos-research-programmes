import ContextualComposition.ForwardMixed
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeCleavage
namespace Independent203
inductive G | one
instance : Category G where
  Hom _ _ := Int
  id _ := 0
  comp f g := f + g
  id_comp := by intros; apply Int.zero_add
  comp_id := by intros; apply Int.add_zero
  assoc := by intros; apply Int.add_assoc
inductive B | pt
instance : Category B where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
def p : G ⥤ B := (Functor.const _).obj B.pt
def k (t : Bool) : Int := if t then 7 else 2
def C (t : Bool) : Cleavage p := by
  intro A y a
  cases A
  refine ⟨y, rfl, (k t : Int), rfl, ?_⟩
  intro z g a _
  change Int at g
  change Unit at a
  cases a
  change ∃! h : Int, _ ∧ h + k t = g
  refine ⟨g - k t, ⟨rfl, by omega⟩, ?_⟩
  rintro h ⟨_,hh⟩
  omega
def Y : Bᵒᵖ ⥤ Cat.{0,1} := (Functor.const _).obj (Cat.of Type)
def xy : Total Y p := pair _ _ G.one Bool
example : gradeMap ((extendChoice Y p p (C false) B.pt xy (𝟙 _)).lift) = (2:Int) := rfl
example : gradeMap ((extendChoice Y p p (C true) B.pt xy (𝟙 _)).lift) = (7:Int) := rfl
def Dbl : Type ⥤ Type where
  obj X := Bool × X
  map f := TypeCat.ofHom (fun p => (p.1, f p.2))
  map_id _ := rfl
  map_comp _ _ := rfl
def T : Y ⟶ Y where
  app _ := Dbl.toCatHom
  naturality _ _ _ := rfl
abbrev P (_ : Bool) := p
def z (t : Bool) : (SpanPull.partProj P P Y t).Fiber B.pt := ⟨xy,rfl⟩
#check ForwardMixed.strictCell P P C T (𝟙 B.pt) false (z false)
#check ForwardMixed.strictCell P P C T (𝟙 B.pt) true (z true)
example (t : Bool) : (SpanPull.totalTag P Y t).map (Reindex.lift (SpanPull.partChoice P P C Y t) (𝟙 B.pt) (z t)) =
    Reindex.lift (SpanPull.weightedChoice P P C Y) (𝟙 B.pt) ((SpanPull.strictTag P P Y B.pt t).obj (z t)) :=
  SpanPull.lift_tag P P C Y _ t (z t)
example (t : Bool) : gradeMap (Reindex.lift (SpanPull.partChoice P P C Y t) (𝟙 B.pt) (z t)) = k t := rfl
example (t : Bool) : gradeMap
    (Reindex.lift (SpanPull.weightedChoice P P C Y) (𝟙 B.pt) ((SpanPull.strictTag P P Y B.pt t).obj (z t))) =
    (Sigma.incl (C := fun _ : Bool => G) t).map (show G.one ⟶ G.one from k t) := rfl
end Independent203
