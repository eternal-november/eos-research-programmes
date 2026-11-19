module
public import ContextualComposition.AccumulationAlgebra
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeInterpretation
open CategoryTheory CategoryTheory.Functor Opposite PackedFree
universe b w u v
set_option backward.isDefEq.respectTransparency false
section Packed
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split)
variable (M : Monad (Bᵒᵖ ⥤ Cat.{max u v,u})) (q : step S ⟶ M.toFunctor)
abbrev action (X : Bᵒᵖ ⥤ Cat.{max u v,u}) := q.app (M.obj X) ≫ M.μ.app X
theorem action_map {X Y : Bᵒᵖ ⥤ Cat.{max u v,u}} (h : X ⟶ Y) : HomLaw S (action S M q X) (action S M q Y) (M.map h) := by
  unfold HomLaw action
  rw [Category.assoc,← M.mu_naturality,← Category.assoc,← q.naturality,Category.assoc]
theorem action_mul (X : Bᵒᵖ ⥤ Cat.{max u v,u}) : HomLaw S (action S M q (M.obj X)) (action S M q X) (M.μ.app X) := by
  unfold HomLaw action
  rw [Category.assoc,← M.assoc,← Category.assoc,← q.naturality]
  rfl
abbrev interpret (X : Bᵒᵖ ⥤ Cat.{max u v,u}) := fold S (action S M q X) (M.η.app X)
theorem empty (X : Bᵒᵖ ⥤ Cat.{max u v,u}) : inc S X 0 ≫ interpret S M q X = M.η.app X := inc_fold S _ _ 0
theorem singleton (X : Bᵒᵖ ⥤ Cat.{max u v,u}) : inc S X 1 ≫ interpret S M q X = q.app X := by
  rw [interpret,inc_fold]
  change (step S).map (M.η.app X) ≫ q.app (M.obj X) ≫ M.μ.app X = _
  rw [← Category.assoc,q.naturality,Category.assoc,M.right_unit,Category.comp_id]
  rfl
theorem successor (X : Bᵒᵖ ⥤ Cat.{max u v,u}) (n : Nat) :
    inc S X (n+1) ≫ interpret S M q X =
      (step S).map (inc S X n ≫ interpret S M q X) ≫ q.app (M.obj X) ≫ M.μ.app X := by
  rw [interpret,inc_fold,inc_fold]; rfl
theorem two (X : Bᵒᵖ ⥤ Cat.{max u v,u}) :
    inc S X 2 ≫ interpret S M q X = (step S).map (q.app X) ≫ q.app (M.obj X) ≫ M.μ.app X := by
  rw [successor S M q X 1,singleton]
theorem natural {X Y : Bᵒᵖ ⥤ Cat.{max u v,u}} (h : X ⟶ Y) : (free S).map h ≫ interpret S M q Y = interpret S M q X ≫ M.map h := by
  apply hom_ext S (action S M q Y) (hom_comp S (map_hom S _) (fold_hom S _ _))
    (hom_comp S (fold_hom S _ _) (action_map S M q h))
  calc
    _ = ChainPayload.layerMap h S 0 ≫ M.η.app Y := by rw [← Category.assoc,inc_map,Category.assoc,empty]
    _ = M.η.app X ≫ M.map h := M.η.naturality h
    _ = _ := by rw [← Category.assoc,empty]
theorem multiplication (X : Bᵒᵖ ⥤ Cat.{max u v,u}) :
    join S X ≫ interpret S M q X =
      ((free S).map (interpret S M q X) ≫ interpret S M q (M.obj X)) ≫ M.μ.app X := by
  apply hom_ext S (action S M q X) (hom_comp S (fold_hom S _ _) (fold_hom S _ _))
    (hom_comp S (hom_comp S (map_hom S _) (fold_hom S _ _)) (action_mul S M q X))
  calc
    _ = interpret S M q X := by erw [← Category.assoc,zero_join,Category.id_comp]
    _ = _ := by
      erw [Category.assoc,← Category.assoc,inc_map,Category.assoc,← Category.assoc (inc S (M.obj X) 0),empty,M.left_unit,Category.comp_id]
      rfl
def extend : monad S ⟶ M where
  app := interpret S M q
  naturality _ _ h := natural S M q h
  app_η := empty S M q
  app_μ := multiplication S M q
abbrev read (f : monad S ⟶ M) := generator S ≫ f.toNatTrans
theorem read_extend : read S M (extend S M q) = q := by
  apply NatTrans.ext; funext X; exact singleton S M q X
theorem hom_of_monad (f : monad S ⟶ M) (X : Bᵒᵖ ⥤ Cat.{max u v,u}) :
    HomLaw S (cons S X) (action S M (read S M f) X) (f.app X) := by
  have h := congrArg (inc S ((free S).obj X) 1 ≫ ·) (f.app_μ X)
  change inc S ((free S).obj X) 1 ≫ join S X ≫ f.app X =
    inc S ((free S).obj X) 1 ≫ ((free S).map (f.app X) ≫ f.app (M.obj X)) ≫ M.μ.app X at h
  erw [← Category.assoc,AccumulationAlgebra.singleton_join,Category.assoc,← Category.assoc,inc_map,Category.assoc] at h
  exact h.trans (by simp only [action,read,NatTrans.comp_app,Category.assoc]; rfl)
theorem extend_read (f : monad S ⟶ M) : extend S M (read S M f) = f := by
  apply MonadHom.ext'; funext X
  exact ((unique S _ (f.app X) (hom_of_monad S M f X)).trans (congrArg (fold S _) (f.app_η X))).symm
def universal : (monad S ⟶ M) ≃ (step S ⟶ M.toFunctor) where
  toFun := read S M
  invFun := extend S M
  left_inv := extend_read S M
  right_inv := read_extend S M
theorem extend_post {N : CategoryTheory.Monad (Bᵒᵖ ⥤ Cat.{max u v,u})} (h : M ⟶ N) :
    extend S M q ≫ h = extend S N (q ≫ h.toNatTrans) := by
  apply (universal S N).injective
  change generator S ≫ (extend S M q ≫ h).toNatTrans = read S N (extend S N (q ≫ h.toNatTrans))
  rw [read_extend,MonadHom.comp_toNatTrans,← Category.assoc]
  exact congrArg (· ≫ h.toNatTrans) (read_extend S M q)
theorem on_generator : extend S (monad S) (generator S) = 𝟙 _ := by
  have e : read S (monad S) (𝟙 _) = generator S := Category.comp_id _
  exact (congrArg (extend S (monad S)) e.symm).trans (extend_read S _ (𝟙 _))
end Packed
section Native
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (M : CategoryTheory.Monad (Bᵒᵖ ⥤ Cat.{max u v,u})) (q : step S ⟶ M.toFunctor)
variable (Y : Bᵒᵖ ⥤ Cat.{max u v,u}) (A : B)
abbrev nestedRoute := ((((free S).map (interpret S M q Y) ≫ interpret S M q (M.obj Y)) ≫ M.μ.app Y).app (op A)).toFunctor
theorem packedSquare : nestedRoute S M q Y A =
    NativePacked.multiplication S Y A ⋙ ((interpret S M q Y).app (op A)).toFunctor :=
  congrArg Cat.Hom.toFunctor (NatTrans.congr_app (multiplication S M q Y).symm (op A))
noncomputable def nativeSquare :=
  isoWhiskerLeft (NativePacked.compare S Y A).functor (eqToIso (packedSquare S M q Y A)) ≪≫
    isoWhiskerRight (NativePacked.actualSquare S Y A) ((interpret S M q Y).app (op A)).toFunctor
end Native
end ContextualComposition.GrothendieckStep.TelescopeInterpretation
