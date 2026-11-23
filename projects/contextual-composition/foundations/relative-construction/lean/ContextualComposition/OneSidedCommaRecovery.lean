module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Group.Nat.TypeTags

/-! Local one-sided inclusions of the independent interaction criterion,
§7. The obstruction uses an empty extended source and tests the actual
forward endomorphism of the unit-content grade. -/

@[expose] public section
namespace ContextualComposition.OneSidedCommaRecovery
open CategoryTheory

universe u v w z k

variable {K : Type v} [Category.{w} K] {L : Type z} [Category.{k} L]
variable (e : K ⥤ Type u) (d : L ⥤ Type u)
variable {A B : Type u}

abbrev content (J : K) (unit : e.obj J ≅ A) : StructuredArrow A d ⥤ Comma e d where
  obj x := ⟨J,x.right,unit.hom ≫ x.hom⟩
  map f := ⟨𝟙 _,f.right,by simp [StructuredArrow.w f]⟩

abbrev context (U : L) (η : B ⟶ d.obj U) : CostructuredArrow e B ⥤ Comma e d where
  obj x := ⟨x.left,U,x.hom ≫ η⟩
  map f := ⟨f.left,𝟙 _,by simp [← Category.assoc, CostructuredArrow.w f]⟩

def contentHomEquiv (J : K) (unit : e.obj J ≅ A) [Subsingleton (J ⟶ J)] (x y : StructuredArrow A d) :
    (x ⟶ y) ≃ ((content e d J unit).obj x ⟶ (content e d J unit).obj y) where
  toFun f := (content e d J unit).map f
  invFun f := StructuredArrow.homMk f.right (by
    have eq : f.left = 𝟙 J := @Subsingleton.elim (J ⟶ J) _ _ _
    have h := f.w
    change e.map f.left ≫ unit.hom ≫ y.hom = (unit.hom ≫ x.hom) ≫ d.map f.right at h
    rw [eq,e.map_id,Category.id_comp,Category.assoc] at h
    exact ((cancel_epi unit.hom).mp h).symm)
  left_inv _ := StructuredArrow.hom_ext _ _ rfl
  right_inv f := Comma.hom_ext _ _ (Subsingleton.elim (𝟙 J) _) rfl

instance contentFull (J : K) (unit : e.obj J ≅ A) [Subsingleton (J ⟶ J)] : (content e d J unit).Full where
  map_surjective {x y} := (contentHomEquiv e d J unit x y).surjective

instance contentFaithful (J : K) (unit : e.obj J ≅ A) : (content e d J unit).Faithful where
  map_injective {x y} {_ _} h := StructuredArrow.hom_ext _ _
    (congrArg (fun m : (content e d J unit).obj x ⟶ (content e d J unit).obj y => m.right) h)

instance contextFaithful (U : L) (η : B ⟶ d.obj U) : (context e d U η).Faithful where
  map_injective {x y} {_ _} h := CostructuredArrow.hom_ext _ _
    (congrArg (fun m : (context e d U η).obj x ⟶ (context e d U η).obj y => m.left) h)

def contextHomEquiv (U : L) (η : B ⟶ d.obj U) [Mono η] [Subsingleton (U ⟶ U)] (x y : CostructuredArrow e B) :
    (x ⟶ y) ≃ ((context e d U η).obj x ⟶ (context e d U η).obj y) where
  toFun f := (context e d U η).map f
  invFun f := CostructuredArrow.homMk f.left (by
    have eq : f.right = 𝟙 U := @Subsingleton.elim (U ⟶ U) _ _ _
    have h := f.w
    change e.map f.left ≫ y.hom ≫ η = (x.hom ≫ η) ≫ d.map f.right at h
    rw [eq,d.map_id,Category.comp_id,← Category.assoc] at h
    exact (cancel_mono η).mp h)
  left_inv _ := CostructuredArrow.hom_ext _ _ rfl
  right_inv f := Comma.hom_ext _ _ rfl (Subsingleton.elim (𝟙 U) _)

instance contextFull (U : L) (η : B ⟶ d.obj U) [Mono η] [Subsingleton (U ⟶ U)] : (context e d U η).Full where
  map_surjective {x y} := (contextHomEquiv e d U η x y).surjective

/-- Empty extended sources provide a witness even for admitted projections
that are required to be surjective: the source manuscript takes the
identity on the empty interface. -/
def emptyBody (P : K) (empty : IsEmpty (e.obj P)) : CostructuredArrow e B :=
  CostructuredArrow.mk (TypeCat.ofHom fun a => (empty.false a).elim)

def emptyEnd (P : K) (empty : IsEmpty (e.obj P)) (U : L) (η : B ⟶ d.obj U) (β : U ⟶ U) :
    (context e d U η).obj (emptyBody e P empty) ⟶ (context e d U η).obj (emptyBody e P empty) where
  left := 𝟙 P
  right := β
  w := by ext a; exact (empty.false a).elim

theorem full_forces_unit_rigidity (P : K) (empty : IsEmpty (e.obj P)) (U : L) (η : B ⟶ d.obj U)
    (h : (context e d U η).Full) : Subsingleton (U ⟶ U) := by
  have allId (β : U ⟶ U) : 𝟙 U = β := by
    obtain ⟨f,hf⟩ := h.map_surjective (emptyEnd e d P empty U η β)
    exact congrArg CommaMorphism.right hf
  exact ⟨fun f g => (allId f).symm.trans (allId g)⟩

/-- A realization of the arity display which splits the mixed insertion into
the polynomial unit yields the monicity used in the local proof. -/
theorem injective_insertion {T : Type u} (U : L) (η : B ⟶ d.obj U) (ν : d.obj U ⟶ T)
    (unit : B ⟶ T) (insertion : η ≫ ν = unit) (hu : Function.Injective unit) : Function.Injective η := by
  intro x y h
  apply hu
  rw [← insertion]
  exact congrArg ν h

theorem full_iff (P : K) (empty : IsEmpty (e.obj P)) (U : L) (η : B ⟶ d.obj U) [Mono η] :
    (context e d U η).Full ↔ Subsingleton (U ⟶ U) :=
  ⟨full_forces_unit_rigidity e d P empty U η,fun h => let _ := h; contextFull e d U η⟩

theorem full_at_all_sources_iff (K : Type u → Type v) [∀ A, Category.{w} (K A)]
    (ext : ∀ A, K A ⥤ Type u) (P : K PEmpty) (empty : IsEmpty ((ext PEmpty).obj P))
    (U : L) (η : B ⟶ d.obj U) [Mono η] :
    (∀ A, (context (ext A) d U η).Full) ↔ Subsingleton (U ⟶ U) :=
  ⟨fun all => (full_iff _ _ P empty U η).mp (all PEmpty),fun h A => let _ := h; contextFull (ext A) d U η⟩

variable {K' : Type v} [Category.{w} K'] {L' : Type z} [Category.{k} L']
variable (e' : K' ⥤ Type u) (d' : L' ⥤ Type u)
variable (pull : K' ⥤ K) (push : L ⥤ L')

/-- Formula (endpoints) with its contravariant context and covariant
content grade maps. The two supplied extension arrows are the ones at the
specific source grade and target grade of this boundary. -/
structure EndpointSquare (x : Comma e d) (y : Comma e' d')
    (uExt : e.obj (pull.obj y.left) ⟶ e'.obj y.left) (vExt : d.obj x.right ⟶ d'.obj (push.obj x.right)) where
  left : x.left ⟶ pull.obj y.left
  right : push.obj x.right ⟶ y.right
  comm : e.map left ≫ uExt ≫ y.hom = x.hom ≫ vExt ≫ d'.map right

theorem left_unique (J : K) [Subsingleton (J ⟶ J)] {Y : K} (k : J ≅ Y) (α : J ⟶ Y) : α = k.hom := by
  have z : α ≫ k.inv = 𝟙 J := Subsingleton.elim _ _
  calc α = (α ≫ k.inv) ≫ k.hom := by simp
       _ = k.hom := by rw [z,Category.id_comp]

theorem right_unique (U : L') [Subsingleton (U ⟶ U)] {Y : L'} (k : Y ≅ U) (β : Y ⟶ U) : β = k.hom := by
  have z : k.inv ≫ β = 𝟙 U := Subsingleton.elim _ _
  calc β = k.hom ≫ (k.inv ≫ β) := by simp
       _ = k.hom := by rw [z,Category.comp_id]

variable {A' B' : Type u}

def contentEndpoint (J : K) (J' : K') [Subsingleton (J ⟶ J)]
    (j : e.obj J ≅ A) (j' : e'.obj J' ≅ A') (k : J ≅ pull.obj J') (u : A ⟶ A')
    (uExt : e.obj (pull.obj J') ⟶ e'.obj J') (hu : e.map k.hom ≫ uExt ≫ j'.hom = j.hom ≫ u)
    (x : StructuredArrow A d) (y : StructuredArrow A' d') (vExt : d.obj x.right ⟶ d'.obj (push.obj x.right)) :
    {β : push.obj x.right ⟶ y.right // u ≫ y.hom = x.hom ≫ vExt ≫ d'.map β} ≃
      EndpointSquare e d e' d' pull push ((content e d J j).obj x) ((content e' d' J' j').obj y) uExt vExt where
  toFun β := ⟨k.hom,β.val,by
    change e.map k.hom ≫ uExt ≫ j'.hom ≫ y.hom = (j.hom ≫ x.hom) ≫ _
    rw [reassoc_of% hu,Category.assoc]
    exact congrArg (j.hom ≫ ·) β.property⟩
  invFun s := ⟨s.right,by
    have h := s.comm
    change e.map s.left ≫ uExt ≫ j'.hom ≫ y.hom = (j.hom ≫ x.hom) ≫ _ at h
    rw [left_unique J k s.left,reassoc_of% hu,Category.assoc] at h
    exact (cancel_epi j.hom).mp h⟩
  left_inv _ := rfl
  right_inv s := by cases s with | mk l r _ => obtain rfl := left_unique J k l; rfl

def contextEndpoint (U : L) (U' : L') [Subsingleton (U' ⟶ U')]
    (η : B ⟶ d.obj U) (η' : B' ⟶ d'.obj U') [Mono η'] (k : push.obj U ≅ U') (v : B ⟶ B')
    (vExt : d.obj U ⟶ d'.obj (push.obj U)) (hv : η ≫ vExt ≫ d'.map k.hom = v ≫ η')
    (x : CostructuredArrow e B) (y : CostructuredArrow e' B')
    (uExt : e.obj (pull.obj y.left) ⟶ e'.obj y.left) :
    {α : x.left ⟶ pull.obj y.left // e.map α ≫ uExt ≫ y.hom = x.hom ≫ v} ≃
      EndpointSquare e d e' d' pull push ((context e d U η).obj x) ((context e' d' U' η').obj y) uExt vExt where
  toFun α := ⟨α.val,k.hom,by
    change e.map α.val ≫ uExt ≫ y.hom ≫ η' = (x.hom ≫ η) ≫ vExt ≫ d'.map k.hom
    rw [Category.assoc,hv]
    simpa only [Category.assoc] using congrArg (· ≫ η') α.property⟩
  invFun s := ⟨s.left,by
    apply (cancel_mono η').mp
    have h := s.comm
    change e.map s.left ≫ uExt ≫ y.hom ≫ η' = (x.hom ≫ η) ≫ vExt ≫ d'.map s.right at h
    rw [right_unique U' k s.right,Category.assoc,hv] at h
    simpa only [Category.assoc] using h⟩
  left_inv _ := rfl
  right_inv s := by cases s with | mk l r _ => obtain rfl := right_unique U' k r; rfl

/-- A concrete local test. The extension forgets every endomorphism of the
sole content grade, including the distinct zero and one additive marks. -/
theorem nontrivial_unit_not_full :
    let e₀ := (Functor.const (Discrete Unit)).obj (PEmpty : Type)
    let d₀ := (Functor.const (SingleObj (Multiplicative Nat))).obj Unit
    let U := SingleObj.star (Multiplicative Nat)
    ¬ (context e₀ d₀ U (𝟙 Unit)).Full := by
  intro e₀ d₀ U full
  have h := full_forces_unit_rigidity e₀ d₀ (Discrete.mk ()) (show IsEmpty PEmpty by infer_instance) U (𝟙 Unit) full
  have impossible := h.allEq (show U ⟶ U from Multiplicative.ofAdd (0 : Nat)) (show U ⟶ U from Multiplicative.ofAdd (1 : Nat))
  exact Nat.zero_ne_one impossible

end ContextualComposition.OneSidedCommaRecovery
