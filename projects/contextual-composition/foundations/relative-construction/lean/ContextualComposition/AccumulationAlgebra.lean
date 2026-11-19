module
public import ContextualComposition.NativePacked
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.Endofunctor.Algebra
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AccumulationAlgebra
open CategoryTheory CategoryTheory.Functor Opposite PackedFree
universe b w u v
set_option backward.isDefEq.respectTransparency false
section Packed
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split)
variable {Y Z : Bᵒᵖ ⥤ Cat.{max u v,u}}
abbrev eval (a : (step S).obj Z ⟶ Z) := fold S a (𝟙 Z)
theorem empty (a : (step S).obj Z ⟶ Z) : inc S Z 0 ≫ eval S a = 𝟙 Z := inc_fold S a _ 0
theorem singleton (a : (step S).obj Z ⟶ Z) : inc S Z 1 ≫ eval S a = a := by
  rw [eval,inc_fold]; change (step S).map (𝟙 _) ≫ a = a; rw [Functor.map_id,Category.id_comp]
theorem flatten (a : (step S).obj Z ⟶ Z) :
    (free S).map (eval S a) ≫ eval S a = join S Z ≫ eval S a := by
  apply hom_ext S a (hom_comp S (map_hom S _) (fold_hom S _ _)) (hom_comp S (fold_hom S _ _) (fold_hom S _ _))
  erw [← Category.assoc,inc_map,Category.assoc,empty,Category.comp_id]
theorem map_eval (a : (step S).obj Y ⟶ Y) (b : (step S).obj Z ⟶ Z) (h : Y ⟶ Z) (p : HomLaw S a b h) :
    eval S a ≫ h = (free S).map h ≫ eval S b := by
  apply hom_ext S b (hom_comp S (fold_hom S _ _) p) (hom_comp S (map_hom S _) (fold_hom S _ _))
  erw [← Category.assoc,empty,Category.id_comp]
theorem singleton_join : inc S ((free S).obj Z) 1 ≫ join S Z = cons S Z := singleton S (cons S Z)
theorem recovered (k : (free S).obj Z ⟶ Z) (h₀ : inc S Z 0 ≫ k = 𝟙 Z)
    (hμ : (free S).map k ≫ k = join S Z ≫ k) : eval S (inc S Z 1 ≫ k) = k := by
  have h : HomLaw S (cons S Z) (inc S Z 1 ≫ k) k := by
    unfold HomLaw
    rw [← singleton_join,Category.assoc,← hμ,← Category.assoc,inc_map,Category.assoc]
    rfl
  exact ((unique S _ k h).trans (congrArg (fold S _) h₀)).symm
/-- Actual Eilenberg--Moore algebra on the given carrier presheaf. -/
def algebra (a : (step S).obj Z ⟶ Z) : (monad S).Algebra where
  A := Z
  a := eval S a
  unit := empty S a
  assoc := (flatten S a).symm
abbrev restrict (K : (monad S).Algebra) : (step S).obj K.A ⟶ K.A := inc S K.A 1 ≫ K.a
theorem extend_restrict (K : (monad S).Algebra) : algebra S (restrict S K) = K := by
  obtain ⟨Z,k,h₀,hμ⟩ := K
  exact congrArg (fun (a : {t : (free S).obj Z ⟶ Z // inc S Z 0 ≫ t = 𝟙 Z ∧ join S Z ≫ t = (free S).map t ≫ t}) =>
    (⟨Z,a.val,a.property.1,a.property.2⟩ : (monad S).Algebra))
    (Subtype.ext (recovered S k h₀ hμ.symm) :
      (⟨_,empty S _,(flatten S _).symm⟩ : {t : (free S).obj Z ⟶ Z // inc S Z 0 ≫ t = 𝟙 Z ∧ join S Z ≫ t = (free S).map t ≫ t}) = ⟨k,h₀,hμ⟩)
theorem strictMap (a : (step S).obj Y ⟶ Y) (b : (step S).obj Z ⟶ Z) (h : Y ⟶ Z) :
    HomLaw S a b h ↔ (free S).map h ≫ eval S b = eval S a ≫ h := by
  refine ⟨fun p => (map_eval S a b h p).symm, fun p => ?_⟩
  have j := congrArg (inc S Y 1 ≫ ·) p
  erw [← Category.assoc,inc_map,Category.assoc,singleton,← Category.assoc,singleton] at j
  exact j.symm
def hom (a : (step S).obj Y ⟶ Y) (b : (step S).obj Z ⟶ Z) (h : Y ⟶ Z) (p : HomLaw S a b h) :
    algebra S a ⟶ algebra S b := ⟨h,(strictMap S a b h).mp p⟩
/-- The forward functor is the identity on carrier presheaves and their maps. -/
def extend : Endofunctor.Algebra (step S) ⥤ (monad S).Algebra where
  obj A := algebra S A.str
  map f := hom S _ _ f.f f.h.symm
def readOne : (monad S).Algebra ⥤ Endofunctor.Algebra (step S) where
  obj K := ⟨K.A,restrict S K⟩
  map {K L} f := ⟨f.f, by
    have h := congrArg (inc S K.A 1 ≫ ·) f.h
    erw [← Category.assoc,inc_map,Category.assoc,← Category.assoc (inc S K.A 1)] at h
    exact h⟩
def unitComponent (A : Endofunctor.Algebra (step S)) : A ≅ (readOne S).obj ((extend S).obj A) :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (step S).map (𝟙 _) ≫ (inc S A.a 1 ≫ eval S A.str) = A.str ≫ 𝟙 _
    rw [Functor.map_id,Category.id_comp,Category.comp_id,singleton])
def counitComponent (K : (monad S).Algebra) : (extend S).obj ((readOne S).obj K) ≅ K :=
  Monad.Algebra.isoMk (Iso.refl _) (by
    change (free S).map (𝟙 _) ≫ K.a = eval S (inc S K.A 1 ≫ K.a) ≫ 𝟙 _
    rw [Functor.map_id,Category.id_comp,Category.comp_id,recovered S K.a K.unit K.assoc.symm])
def unitIso : 𝟭 (Endofunctor.Algebra (step S)) ≅ extend S ⋙ readOne S :=
  NatIso.ofComponents (unitComponent S) (fun f => Endofunctor.Algebra.Hom.ext ((Category.comp_id f.f).trans (Category.id_comp f.f).symm))
def counitIso : readOne S ⋙ extend S ≅ 𝟭 ((monad S).Algebra) :=
  NatIso.ofComponents (counitComponent S) (fun f => Monad.Algebra.Hom.ext ((Category.comp_id f.f).trans (Category.id_comp f.f).symm))
theorem triangle (X : Endofunctor.Algebra (step S)) :
    (extend S).map ((unitIso S).hom.app X) ≫ (counitIso S).hom.app ((extend S).obj X) = 𝟙 _ := by
  apply Monad.Algebra.Hom.ext
  exact Category.id_comp (𝟙 X.a)
def equivalence : Endofunctor.Algebra (step S) ≌ (monad S).Algebra where
  functor := extend S
  inverse := readOne S
  unitIso := unitIso S
  counitIso := counitIso S
  functor_unitIso_comp := triangle S
/-- On the ordered nested summand (inner m, outer n) the common value is
the recursively accumulated (m+n)-layer. The domain still retains both cuts. -/
theorem ordered (a : (step S).obj Z ⟶ Z) (m n : Nat) :
    (ChainPayload.layerMap (inc S Z m) S n ≫ inc S ((free S).obj Z) n) ≫
      ((free S).map (eval S a) ≫ eval S a) =
    eqToHom (nested S Z m n) ≫ foldLayer S a (𝟙 Z) (m+n) := by
  rw [flatten,← Category.assoc,Category.assoc (ChainPayload.layerMap _ _ _),join_summand,Category.assoc]
  exact congrArg (_ ≫ ·) (inc_fold S a _ (m+n))
end Packed
section Native
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Z : Bᵒᵖ ⥤ Cat.{max u v,u}}
theorem atFlatten (a : (step S).obj Z ⟶ Z) (A : B) :
    (((free S).map (eval S a)).app (op A)).toFunctor ⋙ ((eval S a).app (op A)).toFunctor =
      NativePacked.multiplication S Z A ⋙ ((eval S a).app (op A)).toFunctor :=
  congrArg Cat.Hom.toFunctor (NatTrans.congr_app (flatten S a) (op A))
/-- Evaluate each inner string and accumulate the outer string, or apply
the actual weighted native flattening functor and then accumulate once. -/
noncomputable def nativeFlatten (a : (step S).obj Z ⟶ Z) (A : B) :=
  isoWhiskerLeft (NativePacked.compare S Z A).functor (eqToIso (atFlatten S a A)) ≪≫
    isoWhiskerRight (NativePacked.actualSquare S Z A) ((eval S a).app (op A)).toFunctor
end Native
end ContextualComposition.GrothendieckStep.AccumulationAlgebra
