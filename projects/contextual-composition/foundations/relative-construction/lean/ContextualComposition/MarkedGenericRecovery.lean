module
public import ContextualComposition.NativeCleavage
public import Mathlib.CategoryTheory.IsoCat

/-! Marked generic squares of an extension with both endpoints varying.
For context the projection is the source and the extension is the target;
for content they exchange places, keeping the native grade arrow forward. -/

@[expose] public section
namespace ContextualComposition.MarkedGenericRecovery
open CategoryTheory GrothendieckStep
universe u v w z
variable {X : Type u} [Category.{v} X] {B : Type w} [Category.{z} B]

structure Generic (src dst : X ⥤ B) where
  grade : X

variable (src dst : X ⥤ B)

structure Square (x y : Generic src dst) where
  left : src.obj x.grade ⟶ src.obj y.grade
  right : dst.obj x.grade ⟶ dst.obj y.grade
  native : x.grade ⟶ y.grade
  source_eq : src.map native = left
  body_eq : (𝟙 (dst.obj x.grade)) ≫ right = dst.map native ≫ 𝟙 (dst.obj y.grade)

theorem right_eq {x y : Generic src dst} (s : Square src dst x y) : s.right = dst.map s.native := by
  simpa using s.body_eq

def nativeSquare {x y : Generic src dst} (f : x.grade ⟶ y.grade) : Square src dst x y :=
  ⟨src.map f,dst.map f,f,rfl,by simp⟩

@[ext] theorem square_ext {x y : Generic src dst} {f g : Square src dst x y} (h : f.native = g.native) : f = g := by
  cases f with
  | mk l r f h₁ h₂ =>
    cases g with
    | mk l' r' g h₁' h₂' =>
      change f = g at h
      subst g
      simp only [Category.id_comp,Category.comp_id] at h₂ h₂'
      subst l; subst l'; subst r; subst r'; rfl

instance : Category (Generic src dst) where
  Hom := Square src dst
  id _ := nativeSquare src dst (𝟙 _)
  comp f g := ⟨f.left ≫ g.left,f.right ≫ g.right,f.native ≫ g.native,
    by rw [src.map_comp,f.source_eq,g.source_eq],by simp [right_eq src dst f,right_eq src dst g]⟩
  id_comp _ := square_ext _ _ (Category.id_comp _)
  comp_id _ := square_ext _ _ (Category.comp_id _)
  assoc _ _ _ := square_ext _ _ (Category.assoc ..)

def read : Generic src dst ⥤ X where
  obj x := x.grade
  map f := f.native

def mark : X ⥤ Generic src dst where
  obj x := ⟨x⟩
  map f := nativeSquare src dst f
  map_id _ := square_ext _ _ rfl
  map_comp _ _ := square_ext _ _ rfl

def iso : IsoCat (Generic src dst) X where
  functor := read src dst
  inverse := mark src dst
  unit_eq := by
    symm
    apply Functor.hext
    · intro x; cases x; rfl
    · intro x y f; exact heq_of_eq (square_ext src dst (f := nativeSquare src dst f.native) (g := f) rfl)
  counit_eq := rfl

def leftProjection : Generic src dst ⥤ B where
  obj x := src.obj x.grade
  map f := f.left
  map_id _ := src.map_id _
  map_comp _ _ := rfl

def rightProjection : Generic src dst ⥤ B where
  obj x := dst.obj x.grade
  map f := f.right
  map_id _ := dst.map_id _
  map_comp _ _ := rfl

theorem recover_left : mark src dst ⋙ leftProjection src dst = src := rfl
theorem recover_right : mark src dst ⋙ rightProjection src dst = dst := rfl

theorem cartesian_iff {x y : Generic src dst} (f : x ⟶ y) :
    NativeCleavage.Cartesian (leftProjection src dst) f ↔ NativeCleavage.Cartesian src f.native := by
  constructor
  · intro h z g a eq
    obtain ⟨k,⟨hk,kg⟩,uk⟩ := h ⟨z⟩ (nativeSquare src dst g) a (by simpa [leftProjection,nativeSquare,f.source_eq] using eq)
    refine ⟨k.native,⟨k.source_eq.trans hk,congrArg Square.native kg⟩,?_⟩
    rintro t ⟨ht,tg⟩
    exact congrArg Square.native (uk (nativeSquare src dst t) ⟨ht,square_ext _ _ tg⟩)
  · intro h z g a eq
    obtain ⟨k,⟨hk,kg⟩,uk⟩ := h z.grade g.native a (by simpa [leftProjection,f.source_eq,g.source_eq] using eq)
    refine ⟨nativeSquare src dst k,⟨hk,square_ext _ _ kg⟩,?_⟩
    rintro t ⟨ht,tg⟩
    exact square_ext _ _ (uk t.native ⟨t.source_eq.trans ht,congrArg Square.native tg⟩)

/-- Mark the specified cartesian lifts, including their exact chosen
sources. A cleavage is additional data on the already recovered category. -/
def markCleavage (cleavage : NativeCleavage.Cleavage src) : NativeCleavage.Cleavage (leftProjection src dst) :=
  fun A y a =>
    let t := cleavage A y.grade a
    ⟨⟨t.obj⟩,t.source,nativeSquare src dst t.lift,t.over,(cartesian_iff src dst _).mpr t.cart⟩

theorem chosenLift (cleavage : NativeCleavage.Cleavage src) (A : B) (y : Generic src dst)
    (a : A ⟶ src.obj y.grade) :
    ((markCleavage src dst cleavage A y a).obj.grade = (cleavage A y.grade a).obj) ∧
    ((markCleavage src dst cleavage A y a).lift.native = (cleavage A y.grade a).lift) := ⟨rfl,rfl⟩

def Opcartesian {K : Type*} [Category* K] (p : K ⥤ B) {x y : K} (f : x ⟶ y) :=
  ∀ (z : K) (g : x ⟶ z) (a : p.obj y ⟶ p.obj z), p.map g = p.map f ≫ a →
    ∃! l : y ⟶ z, p.map l = a ∧ f ≫ l = g

theorem opcartesian_iff {x y : Generic src dst} (f : x ⟶ y) :
    Opcartesian (rightProjection src dst) f ↔ Opcartesian dst f.native := by
  constructor
  · intro h z g a eq
    obtain ⟨k,⟨hk,kg⟩,uk⟩ := h ⟨z⟩ (nativeSquare src dst g) a (by
      change dst.map g = f.right ≫ a
      rw [right_eq]; exact eq)
    refine ⟨k.native,⟨(right_eq src dst k).symm.trans hk,congrArg Square.native kg⟩,?_⟩
    rintro t ⟨ht,tg⟩
    exact congrArg Square.native (uk (nativeSquare src dst t) ⟨ht,square_ext _ _ tg⟩)
  · intro h z g a eq
    obtain ⟨k,⟨hk,kg⟩,uk⟩ := h z.grade g.native a (by
      change g.right = f.right ≫ a at eq
      rwa [right_eq src dst g,right_eq src dst f] at eq)
    refine ⟨nativeSquare src dst k,⟨hk,square_ext _ _ kg⟩,?_⟩
    rintro t ⟨ht,tg⟩
    exact square_ext _ _ (uk t.native ⟨(right_eq src dst t).symm.trans ht,congrArg Square.native tg⟩)

section Covariant
variable (L : B ⥤ Cat.{v,u}) (D : Grothendieck L ⥤ B)
abbrev CovMarked := Generic D (Grothendieck.forget L)

/-- For content, the native grade is covariant over the right endpoint;
the left endpoint is forced by its extension. -/
def contentSquare (x y : CovMarked L D) : (x ⟶ y) ≃
    Σ v : x.grade.base ⟶ y.grade.base, (L.map v).toFunctor.obj x.grade.fiber ⟶ y.grade.fiber where
  toFun f := ⟨f.native.base,f.native.fiber⟩
  invFun f := nativeSquare D (Grothendieck.forget L) ⟨f.1,f.2⟩
  left_inv _ := square_ext _ _ rfl
  right_inv _ := rfl

theorem content_endpoints {x y : CovMarked L D} (t : x ⟶ y) :
    t.left = D.map t.native ∧ t.right = (contentSquare L D x y t).1 :=
  ⟨t.source_eq.symm,right_eq _ _ t⟩
end Covariant

section Indexed
variable (P : Endpoints.{w,z,u,v} B) (S : P.Split)
abbrev Src := SpanApex.left P
abbrev Dst := SpanApex.right P S
abbrev Marked := Generic (Src P) (Dst P S)

/-- The varying generic square is exactly a base arrow u and a native
grade arrow into its reindexed target. The second endpoint is determined. -/
def indexedSquare (x y : Marked P S) : (x ⟶ y) ≃
    Σ u : grade P.grades (𝟭 B) x.grade ⟶ grade P.grades (𝟭 B) y.grade,
      payload P.grades (𝟭 B) x.grade ⟶ (P.grades.map u.op).toFunctor.obj (payload P.grades (𝟭 B) y.grade) :=
  (show (x ⟶ y) ≃ (x.grade ⟶ y.grade) from
    ⟨Square.native,nativeSquare _ _,fun _ => square_ext _ _ rfl,fun _ => rfl⟩).trans (homEquiv _ _)

theorem indexed_endpoint {x y : Marked P S} (s : x ⟶ y) :
    s.right = (Dst P S).map (arrow (indexedSquare P S x y s).1 (indexedSquare P S x y s).2) :=
  right_eq _ _ s

end Indexed
end ContextualComposition.MarkedGenericRecovery
