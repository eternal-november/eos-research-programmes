import ContextualComposition.BlockCartesian
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeCleavage BlockCartesian
namespace ChoiceTest
set_option backward.isDefEq.respectTransparency false
inductive G | one
instance : Category G where
  Hom _ _ := Int
  id _ := 0
  comp f g := f+g
  id_comp := by intros; apply Int.zero_add
  comp_id := by intros; apply Int.add_zero
  assoc := by intros; apply Int.add_assoc
abbrev B := Discrete Unit
def pt : B := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of G)
  extend _ := (Functor.const _).obj pt
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
abbrev p := (power S 1).source
def delta (k : Int) (x : (power S 1).apex) : x ⟶ x := arrow (𝟙 _) k
def cellRead : (power S 1).apex ⥤ G where
  obj x := payload P.grades (𝟭 B) x
  map h := payloadMap h
  map_id _ := rfl
  map_comp a b := (payload_comp a b).trans (congrArg (fun l : Int => (show Int from payloadMap a) + l) (Int.add_zero (payloadMap b)))
theorem delta_add (x : (power S 1).apex) (k l : Int) : delta k x ≫ delta l x = delta (k+l) x := by
  apply (homEquiv _ _).injective
  exact Sigma.ext (by apply Subsingleton.elim) (heq_of_eq (cellRead.map_comp (delta k x) (delta l x)))
instance deltaIso (k : Int) (x : (power S 1).apex) : IsIso (delta k x) := by
  refine ⟨delta (-k) x,?_,?_⟩
  · rw [delta_add,show k + -k = 0 by omega]; rfl
  · rw [delta_add,show -k + k = 0 by omega]; rfl
def chosen (k : Int) : Cleavage p := fun A y a => by
  have e : p.obj y = A := Subsingleton.elim _ _
  let : p.IsStronglyCartesian (p.map (delta k y)) (delta k y) := inferInstance
  exact ⟨y,e,delta k y,Subsingleton.elim _ _,Change.ofStrong _ this⟩
def choices (k : Int) : (n : Nat) → Cleavage (power S n).source
  | 0 => baseChoice
  | 1 => chosen k
  | n+2 => SpanPull.All.parts S (n+2)
def telChoice (k : Int) : Cleavage (leftLeg S) := SpanPull.choice _ (choices k)
def x : (power S 1).apex := pair _ _ pt G.one
def z : (All.source S).Fiber pt := ⟨⟨1,⟨1,x⟩⟩,rfl⟩
def L := All.nestedChoice S (telChoice 2)
def J := telChoice 7
noncomputable abbrev face := All.sourceFace S L J (𝟙 pt)
abbrev f (k : Int) : (⟨1,x⟩ : tel S) ⟶ ⟨1,x⟩ := (incl S 1).map (delta k x)
example : (flatten S).map (Reindex.lift L (𝟙 pt) z) = f 2 := rfl
def obs : (leftLeg S).Fiber pt := ⟨⟨1,x⟩,rfl⟩
noncomputable abbrev F := SpanPayload.fibreFunctor (flatten S) (leftLeg S) (flatten_source S) pt
theorem obsEq : F.obj z = obs :=
  Subtype.ext (Functor.congr_obj (SpanPayload.fibre_diagram (flatten S) (leftLeg S) (flatten_source S) pt) z)
def partRead : (n : Nat) → (power S n).apex ⥤ G
  | 1 => cellRead
  | _ => (Functor.const _).obj G.one
def readGrade : tel S ⥤ G := Sigma.desc partRead
def val {x y : G} (f : x ⟶ y) : Int := f
theorem val_align {x y x' y' : G} {f : x ⟶ y} {g : x' ⟶ y'} (h : TelescopeSquares.Aligned f g) :
    val f = val g := by obtain ⟨hx,hy,h⟩ := h; subst x'; subst y'; exact congrArg val (by simpa using h : f = g)
example : val (readGrade.map (Reindex.lift J (𝟙 pt) (F.obj z))) = 7 := by rw [obsEq]; rfl
-- Identifying these two separately selected restrictions strictly would force -5 = 0.
example : val (readGrade.map (face.sq.hom.app z).val) = -5 := by
  have h := val_align ((face.fac z).map readGrade)
  rw [readGrade.map_comp] at h
  change val (readGrade.map (face.sq.hom.app z).val) + val (readGrade.map (Reindex.lift J (𝟙 pt) (F.obj z))) = 2 at h
  rw [obsEq] at h
  change val (readGrade.map (face.sq.hom.app z).val) + 7 = 2 at h
  omega
end ChoiceTest
