module
public import ContextualComposition.OneSidedCommaRecovery
public import ContextualComposition.NativeFinitePush
public import Mathlib.CategoryTheory.Pi.Basic

/-! Application of the local one-sided criterion to native augmented
contexts, using the already proved uniqueness of augmented termination. -/

@[expose] public section
namespace ContextualComposition.AugmentedOneSidedRecovery
open CategoryTheory NativeFinitePush OneSidedCommaRecovery
universe u v w z
variable {V : Type u} (K : Coeff.{u,v} V) (P : Push K) (I : V)

structure Context (A : Type u) where
  family : A → Aug P I

instance (A : Type u) : Category (Context K P I A) where
  Hom R S := ∀ a, AugHom P (R.family a) (S.family a)
  id _ := fun _ => AugHom.ident _
  comp f g := fun a => (f a).comp (g a)
  id_comp f := funext fun a => AugHom.ident_comp (f a)
  comp_id f := funext fun a => AugHom.comp_ident (f a)
  assoc f g h := funext fun a => AugHom.comp_assoc (f a) (g a) (h a)

def extF (A : Type u) : Context K P I A ⥤ Type u where
  obj R := Σ a, Fin (R.family a).base.n
  map f := TypeCat.ofHom fun z => ⟨z.1,(f z.1).native.addr z.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev unit (A : Type u) : Context K P I A := ⟨fun _ => AugHom.unit I⟩

instance (A : Type u) : Subsingleton (unit K P I A ⟶ unit K P I A) where
  allEq f g := funext fun a => (AugHom.terminal (f a)).trans (AugHom.terminal (g a)).symm

def discharge (A : Type u) : (extF K P I A).obj (unit K P I A) ≅ A :=
  (show (Σ _ : A, Fin 1) ≃ A from
    ⟨Sigma.fst,fun a => ⟨a,0⟩,fun ⟨a,i⟩ => congrArg (Sigma.mk a) (Subsingleton.elim (0 : Fin 1) i),fun _ => rfl⟩).toIso

def pull {A A' : Type u} (u : A → A') : Context K P I A' ⥤ Context K P I A where
  obj R := ⟨R.family ∘ u⟩
  map f := fun a => f (u a)
  map_id _ := rfl
  map_comp _ _ := rfl

def extendEndpoint {A A' : Type u} (u : A → A') (R : Context K P I A') :
    (extF K P I A).obj ((pull K P I u).obj R) ⟶ (extF K P I A').obj R :=
  TypeCat.ofHom fun z => ⟨u z.1,z.2⟩

theorem unit_endpoint {A A' : Type u} (u : A → A') :
    extendEndpoint K P I u (unit K P I A') ≫ (discharge K P I A').hom =
      (discharge K P I A).hom ≫ TypeCat.ofHom u := rfl

variable {L : Type w} [Category.{z} L] (d : L ⥤ Type u)

def contentCells (A : Type u) (x y : StructuredArrow A d) :
    (x ⟶ y) ≃ ((content (extF K P I A) d (unit K P I A) (discharge K P I A)).obj x ⟶
      (content (extF K P I A) d (unit K P I A) (discharge K P I A)).obj y) :=
  contentHomEquiv _ _ _ _ x y

theorem context_full_iff {B : Type u} (U : L) (η : B ⟶ d.obj U) [Mono η] :
    (∀ A, (context (extF K P I A) d U η).Full) ↔ Subsingleton (U ⟶ U) :=
  full_at_all_sources_iff d (Context K P I) (extF K P I) (unit K P I PEmpty)
    ⟨fun z => z.1.elim⟩ U η

end ContextualComposition.AugmentedOneSidedRecovery
