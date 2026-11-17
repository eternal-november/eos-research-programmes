module
public import ContextualComposition.GrothendieckCoherence
public import Mathlib.CategoryTheory.Sigma.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep.Iterates
open CategoryTheory Opposite
universe u v b w
variable {B : Type b} [Category.{w} B] (P : Endpoints.{b,w,u,v} B) (S : P.Split)
variable (Y : Bᵒᵖ ⥤ Cat.{v,u})
/-- Fixed-length right-hand iterates of the split extension, indexed by length outside the presheaf. -/
def layer : Nat → Bᵒᵖ ⥤ Cat.{v,u}
  | 0 => Y
  | n+1 => P.extensionPresheaf (layer n) S

/-- A full recursive decoding: each native grade arrow reindexes the *whole*
target tail before the next grade arrow (or final payload arrow) is selected. -/
def Code : (n : Nat) → (A : B) → (layer P S Y n).obj (op A) →
    (layer P S Y n).obj (op A) → Type (max u v)
  | 0, _, x, y => ULift (x ⟶ y)
  | n+1, A, x, y => Σ k : grade _ (P.extend A) x ⟶ grade _ (P.extend A) y,
      Code n ((P.extend A).obj (grade _ _ x)) (payload _ _ x)
        (((layer P S Y n).map ((P.extend A).map k).op).toFunctor.obj (payload _ _ y))

def decode : (n : Nat) → (A : B) → (x y : (layer P S Y n).obj (op A)) →
    (x ⟶ y) ≃ Code P S Y n A x y
  | 0, _, _, _ => Equiv.ulift.symm
  | n+1, _, x, y => (homEquiv x y).trans (Equiv.sigmaCongrRight fun _ => decode n _ _ _)

abbrev Packed (A : Bᵒᵖ) := Σ n, (layer P S Y n).obj A

def packedMap {A D : Bᵒᵖ} (u : A ⟶ D) : Packed P S Y A ⥤ Packed P S Y D :=
  Sigma.Functor.sigma fun n => ((layer P S Y n).map u).toFunctor

private theorem sigma_id {C : Nat → Type u} [∀ n, Category.{v} (C n)] :
    Sigma.Functor.sigma (fun n => 𝟭 (C n)) = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]
    exact (Category.comp_id _).symm


private theorem sigma_comp {C D E : Nat → Type u} [∀ n, Category.{v} (C n)]
    [∀ n, Category.{v} (D n)] [∀ n, Category.{v} (E n)]
    (F : ∀ n, C n ⥤ D n) (G : ∀ n, D n ⥤ E n) :
    Sigma.Functor.sigma (fun n => F n ⋙ G n) = Sigma.Functor.sigma F ⋙ Sigma.Functor.sigma G := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]
    exact (Category.comp_id _).symm


theorem packedMap_id (A : Bᵒᵖ) : packedMap P S Y (𝟙 A) = 𝟭 _ := by
  unfold packedMap
  simp only [Functor.map_id, Cat.Hom.id_toFunctor]
  exact sigma_id

theorem packedMap_comp {A D E : Bᵒᵖ} (u : A ⟶ D) (v : D ⟶ E) :
    packedMap P S Y (u ≫ v) = packedMap P S Y u ⋙ packedMap P S Y v := by
  unfold packedMap
  simp only [Functor.map_comp, Cat.Hom.comp_toFunctor]
  apply sigma_comp

def packedPresheaf : Bᵒᵖ ⥤ Cat where
  obj A := Cat.of (Packed P S Y A)
  map u := (packedMap P S Y u).toCatHom
  map_id A := congrArg Functor.toCatHom (packedMap_id P S Y A)
  map_comp u v := congrArg Functor.toCatHom (packedMap_comp P S Y u v)

theorem length_preserved {A : Bᵒᵖ} {x y : Packed P S Y A} (f : x ⟶ y) : x.1 = y.1 := by
  cases f; rfl

def inclusion (n : Nat) (A : Bᵒᵖ) : (layer P S Y n).obj A ⥤ Packed P S Y A := Sigma.incl (C := fun i => ((layer P S Y i).obj A : Type u)) n

theorem inclusion_naturality (n : Nat) {A D : Bᵒᵖ} (f : A ⟶ D) :
    inclusion P S Y n A ⋙ packedMap P S Y f =
      ((layer P S Y n).map f).toFunctor ⋙ inclusion P S Y n D := rfl

noncomputable def summandDecode (n : Nat) (A : B) (x y : (layer P S Y n).obj (op A)) :
    ((inclusion P S Y n _).obj x ⟶ (inclusion P S Y n _).obj y) ≃ Code P S Y n A x y :=
  let F := Sigma.incl (C := fun i => ((layer P S Y i).obj (op A) : Type u)) n
  (Equiv.ofBijective (F.map (X := x) (Y := y)) ⟨F.map_injective, F.map_surjective⟩).symm.trans (decode P S Y n A x y)

theorem successor_payload {A D : B} (u : D ⟶ A) (n : Nat)
    {x y : (layer P S Y (n+1)).obj (op A)} (f : x ⟶ y) :
    payloadMap (((layer P S Y (n+1)).map u.op).toFunctor.map f) =
      ((layer P S Y n).map ((P.lift u).app (grade _ _ x)).op).toFunctor.map (payloadMap f) ≫
        eqToHom (endpoint_square _ _ _ _ (P.lift u) (gradeMap f) (payload _ _ y)) :=
  restrict_payload _ _ _ _ _ f

namespace Witness
open Families
abbrev depth (n : Nat) := layer endpoints splitEndpoints presheaf n
def source : (depth 2).obj (op Bool) :=
  pair _ _ smallGrade (pair _ _ (fun _ => Unit) (fun _ => Unit))
def target : (depth 2).obj (op Bool) :=
  pair _ _ wideGrade (pair _ _ (fun z => if (show Bool from z.2) = true then Bool else Empty)
    (fun z => if (show Bool from z.1.2) = true then Bool else Empty))

def testArrow : source ⟶ target :=
  arrow (x := source) (y := target) widen
    (arrow (x := payload _ _ source)
      (y := ((depth 1).map ((sumFunctor Bool).map widen).op).toFunctor.obj (payload _ _ target))
      (fun _ => TypeCat.ofHom (fun _ => true))
      (fun z => TypeCat.ofHom (fun _ => z.1.1)))

theorem head_test (b : Bool) :
    (gradeMap (((depth 2).map (selectPoint b).op).toFunctor.map testArrow) ()).hom () = true := rfl

theorem middle_test (b : Bool) :
    (gradeMap (payloadMap (((depth 2).map (selectPoint b).op).toFunctor.map testArrow))
      ⟨(),()⟩).hom () = true := rfl

theorem leaf_test (b : Bool) :
    (payloadMap (payloadMap (((depth 2).map (selectPoint b).op).toFunctor.map testArrow))
      ⟨⟨(),()⟩,()⟩).hom () = b := rfl
end Witness
end ContextualComposition.GrothendieckStep.Iterates
