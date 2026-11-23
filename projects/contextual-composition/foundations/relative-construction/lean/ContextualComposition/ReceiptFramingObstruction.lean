module
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! The two-inclusion boundary for retained global receipts. Every candidate framed context and body is allowed by the contradiction. Only its native projection to the whole receipt grade is used. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.ReceiptFramingObstruction
open CategoryTheory Limits
set_option backward.isDefEq.respectTransparency false

universe u v w v' w'
variable (T : Type u ⥤ Type u)
abbrev One := PUnit.{u+1}
abbrev Two := ULift.{u} Bool
def inc (b : Bool) : One.{u} ⟶ Two.{u} := TypeCat.ofHom fun _ => ⟨b⟩
def discard : Two.{u} ⟶ One.{u} := TypeCat.ofHom fun _ => ⟨⟩
def label {X : Type u} (x : X) : Over X := Over.mk (TypeCat.ofHom (fun _ : One.{u} => x))

theorem label_eq {X : Type u} {x y : X} (i : label x ≅ label y) : x = y :=
  (congrArg (fun (k : One.{u} ⟶ X) => k PUnit.unit) (Over.w i.hom)).symm

variable (η : 𝟭 (Type u) ⟶ T)

theorem distinct_units (pb : IsPullback (η.app Two) discard (T.map discard) (η.app One)) :
    η.app Two (ULift.up false) ≠ η.app Two (ULift.up true) := by
  intro h
  have eq : inc false = inc true := by
    apply pb.hom_ext
    · apply ConcreteCategory.hom_ext; intro x; exact h
    · rfl
  exact Bool.noConfusion (congrArg (fun (k : One ⟶ Two) => (k PUnit.unit).down) eq)

def extension (B : Type u) : Over (T.obj B) ⥤ Type u where
  obj R := Sum B R.left
  map f := TypeCat.ofHom (Sum.map id f.left)
  map_id X := by apply ConcreteCategory.hom_ext; rintro (x|r) <;> rfl
  map_comp f g := by apply ConcreteCategory.hom_ext; rintro (x|r) <;> rfl

variable {K : Type w} {K' : Type w'} [Category.{v} K] [Category.{v'} K']
variable {A B : Type u}
abbrev Mixed (e : K ⥤ Type u) (B : Type u) := Comma e (extension T B)

/-- The pure input changes the context and precomposes the body, retaining the whole receipt grade. -/
def pre {e : K ⥤ Type u} {e' : K' ⥤ Type u} (r : K ⥤ K') (a : r ⋙ e' ⟶ e) :
    Mixed T e B ⥤ Mixed T e' B where
  obj X := ⟨r.obj X.left,X.right,a.app X.left ≫ X.hom⟩
  map {X Y} f := ⟨r.map f.left,f.right,by
    have h : e'.map (r.map f.left) ≫ a.app Y.left = a.app X.left ≫ e.map f.left := a.naturality _
    rw [← Category.assoc,h,Category.assoc,f.w,Category.assoc]⟩

/-- The pure output relabels the retained receipts along T v, keeping their actual elements and grade maps. -/
def post (e : K ⥤ Type u) (b : A ⟶ B) : Mixed T e A ⥤ Mixed T e B where
  obj X := ⟨X.left,(Over.map (T.map b)).obj X.right,X.hom ≫ TypeCat.ofHom (Sum.map b id)⟩
  map {X Y} f := ⟨f.left,(Over.map (T.map b)).map f.right,by
    apply ConcreteCategory.hom_ext
    intro x
    have h := congrArg (fun (k : e.obj X.left ⟶ (extension T A).obj Y.right) => k x) f.w
    change Y.hom (e.map f.left x) = Sum.map id f.right.left (X.hom x) at h
    change Sum.map b id (Y.hom (e.map f.left x)) = Sum.map id f.right.left (Sum.map b id (X.hom x))
    rw [h]
    cases X.hom x <;> rfl⟩

def singleReceipt (e : K ⥤ Type u) (P : K) : Mixed T e One :=
  ⟨P,label (η.app One PUnit.unit), TypeCat.ofHom (fun _ => Sum.inr PUnit.unit)⟩

def postLabel (e : K ⥤ Type u) (P : K) (b : Bool) :
    ((post T e (inc b)).obj (singleReceipt T η e P)).right ≅ label (η.app Two (ULift.up b)) :=
  Over.isoMk (Iso.refl _) (by
    apply ConcreteCategory.hom_ext
    intro _
    exact congrArg (fun (k : One ⟶ T.obj Two) => k PUnit.unit) (η.naturality (inc b)))

/-- Even the two cells forced by the frame inclusions cannot both exist, for any proposed framed arrow. -/
theorem two_inclusions (pb : IsPullback (η.app Two) discard (T.map discard) (η.app One))
    {e : K ⥤ Type u} {e' : K' ⥤ Type u} (P : K) (r : Bool → K' ⥤ K)
    (a : ∀ b, r b ⋙ e ⟶ e') (G : Mixed T e' Two) :
    ¬ Nonempty (∀ b, (pre T (r b) (a b)).obj G ≅ (post T e (inc b)).obj (singleReceipt T η e P)) := by
  rintro ⟨cmp⟩
  let t (b : Bool) : G.right ≅ label (η.app Two (ULift.up b)) :=
    (Comma.snd e (extension T Two)).mapIso (cmp b) ≪≫ postLabel T η e P b
  exact distinct_units T η pb (label_eq ((t false).symm ≪≫ t true))

/-- Unit-frame recovery and just the two invertible parameter comparisons already contradict the retained grade. The functors here are expressed at the canonical pure unit interface identifications. -/
theorem frame_obstruction (pb : IsPullback (η.app Two) discard (T.map discard) (η.app One))
    {e : K ⥤ Type u} {e' : K' ⥤ Type u} (P : K) (r : Bool → K' ⥤ K) (a : ∀ b, r b ⋙ e ⟶ e')
    (oneFrame : Mixed T e One ⥤ Mixed T e One) (twoFrame : Mixed T e One ⥤ Mixed T e' Two)
    (unitFrame : oneFrame ≅ 𝟭 _) :
    ¬ Nonempty (∀ b, twoFrame ⋙ pre T (r b) (a b) ≅ oneFrame ⋙ post T e (inc b)) := by
  rintro ⟨parameter⟩
  let F := singleReceipt T η e P
  apply two_inclusions T η pb P r a (twoFrame.obj F)
  exact ⟨fun b => (parameter b).app F ≪≫ (post T e (inc b)).mapIso (unitFrame.app F)⟩

/-- Transport a candidate back through equivalences of the three hom categories. Compatibility with each of the two pure input/output routes is essential. -/
noncomputable def transport_candidate {I C₁ C₂ D C₁' C₂' D' : Type*}
    [Category* C₁] [Category* C₂] [Category* D] [Category* C₁'] [Category* C₂'] [Category* D']
    (E : C₁ ≌ C₁') (K : C₂ ≌ C₂') (L : D ≌ D') (u : I → C₂ ⥤ D) (v : I → C₁ ⥤ D)
    (u' : I → C₂' ⥤ D') (v' : I → C₁' ⥤ D')
    (input : ∀ i, K.functor ⋙ u' i ≅ u i ⋙ L.functor) (output : ∀ i, E.functor ⋙ v' i ≅ v i ⋙ L.functor)
    (x : C₁) (g : C₂') (h : ∀ i, (u' i).obj g ≅ (v' i).obj (E.functor.obj x)) :
    ∀ i, (u i).obj (K.inverse.obj g) ≅ (v i).obj x := fun i =>
  L.functor.preimageIso (((input i).app _).symm ≪≫ (u' i).mapIso (K.counitIso.app g) ≪≫ h i ≪≫ (output i).app x)

end ContextualComposition.ReceiptFramingObstruction
