module
public import ContextualComposition.PackedFree
public import ContextualComposition.PayloadLaws
public import ContextualComposition.BlockCartesian
public import Mathlib.CategoryTheory.IsoCat
@[expose] public section
namespace ContextualComposition.GrothendieckStep.PackedCuts
open CategoryTheory CategoryTheory.Functor Opposite PackedFree
universe b w u v
variable {B : Type b} [Category.{w} B]
set_option linter.checkUnivs false in
abbrev Psh (B : Type b) [Category.{w} B] := Bᵒᵖ ⥤ Cat.{max u v,u}
variable (F : Nat → Psh.{b,w,u,v} B)
def sum : Psh.{b,w,u,v} B where
  obj a := Cat.of (Σ m, (F m).obj a)
  map f := (ZeroPower.Sum.map (fun m => ((F m).map f).toFunctor)).toCatHom
  map_id A := by
    apply congrArg Functor.toCatHom
    apply sigma_ext; intro m
    exact congrArg (· ⋙ Sigma.incl (C := fun t => ((F t).obj A : Type u)) m) (congrArg Cat.Hom.toFunctor ((F m).map_id A))
  map_comp {a d c} f g := by
    apply congrArg Functor.toCatHom
    apply sigma_ext; intro m
    exact congrArg (· ⋙ Sigma.incl (C := fun t => ((F t).obj c : Type u)) m) (congrArg Cat.Hom.toFunctor ((F m).map_comp f g))
def inj (m : Nat) : F m ⟶ sum F where
  app a := (Sigma.incl (C := fun m => ((F m).obj a : Type u)) m).toCatHom
  naturality _ _ _ := rfl
def gather {W : Psh.{b,w,u,v} B} (f : ∀ m, F m ⟶ W) : sum F ⟶ W where
  app a := (Sigma.desc fun m => ((f m).app a).toFunctor).toCatHom
  naturality A D a := by apply congrArg Functor.toCatHom; apply sigma_ext; intro m; exact congrArg Cat.Hom.toFunctor ((f m).naturality a)
theorem inj_gather {W : Psh.{b,w,u,v} B} (f : ∀ m, F m ⟶ W) (m : Nat) : inj F m ≫ gather F f = f m := by apply NatTrans.ext; rfl
theorem ext_sum {W : Psh.{b,w,u,v} B} {f g : sum F ⟶ W} (h : ∀ m, inj F m ≫ f = inj F m ≫ g) : f = g := by
  apply NatTrans.ext; funext a; apply congrArg Functor.toCatHom; exact sigma_ext fun m => congrArg Cat.Hom.toFunctor (NatTrans.congr_app (h m) a)

section Distribution
variable {K : Type*} [Category* K] (e : K ⥤ B)
abbrev totalGather : (Σ m, Total (F m) e) ⥤ Total (sum F) e := Sigma.desc fun m => ChainPayload.fibreMap (inj F m) e
def splitObj (x : Total (sum F) e) : Σ m, Total (F m) e :=
  ⟨(payload _ e x).1,pair _ e (grade _ e x) (payload _ e x).2⟩
def splitHom {x y : Σ m, Total (F m) e} (f : (totalGather F e).obj x ⟶ (totalGather F e).obj y) : x ⟶ y := by
  rcases x with ⟨n,⟨⟨a,s⟩⟩⟩; rcases y with ⟨m,⟨⟨b,t⟩⟩⟩
  obtain ⟨k,h⟩ := homEquiv _ _ f
  change Sigma.SigmaHom (C := fun i => ((F i).obj (op (e.obj a.unop)) : Type u)) ⟨n,s.unop⟩ ⟨m,((F m).map (e.map k).op).toFunctor.obj t.unop⟩ at h
  cases h with | mk z => exact Sigma.SigmaHom.mk (arrow k z)
theorem inj_arrow (m : Nat) {x y : Total (F m) e} (k : grade _ e x ⟶ grade _ e y)
    (h : payload _ e x ⟶ ((F m).map (e.map k).op).toFunctor.obj (payload _ e y)) :
    (ChainPayload.fibreMap (inj F m) e).map (arrow (x := x) (y := y) k h) =
      arrow (x := (totalGather F e).obj ⟨m,x⟩) (y := (totalGather F e).obj ⟨m,y⟩) k (Sigma.SigmaHom.mk h) := by
  apply (homEquiv _ _).injective; apply Sigma.ext
  · rfl
  apply heq_of_eq; exact (ChainPayload.fibreMap_payload (inj F m) e (arrow (x := x) (y := y) k h)).eq
theorem gather_split {x y : Σ m, Total (F m) e} (f : (totalGather F e).obj x ⟶ (totalGather F e).obj y) :
    (totalGather F e).map (splitHom F e f) = f := by
  rcases x with ⟨n,⟨⟨a,s⟩⟩⟩; rcases y with ⟨m,⟨⟨b,t⟩⟩⟩
  obtain ⟨⟨k,h⟩,rfl⟩ := (homEquiv _ _).symm.surjective f
  change Sigma.SigmaHom (C := fun i => ((F i).obj (op (e.obj a.unop)) : Type u)) ⟨n,s.unop⟩ ⟨m,((F m).map (e.map k).op).toFunctor.obj t.unop⟩ at h
  cases h; exact inj_arrow F e _ _ _
theorem split_gather {x y : Σ m, Total (F m) e} (f : x ⟶ y) : splitHom F e ((totalGather F e).map f) = f := by
  cases f with | @mk n x y g =>
    obtain ⟨⟨k,h⟩,rfl⟩ := (homEquiv _ _).symm.surjective g
    change splitHom F e (x := ⟨n,x⟩) (y := ⟨n,y⟩) ((ChainPayload.fibreMap (inj F n) e).map (arrow (x := x) (y := y) k h)) = _
    rw [inj_arrow]; rfl
instance gatherIso : (totalGather F e).IsIso where
  faithful := ⟨fun {_x _y} {f g} h => (split_gather F e f).symm.trans ((congrArg (splitHom F e) h).trans (split_gather F e g))⟩
  full := ⟨fun f => ⟨splitHom F e f,gather_split F e f⟩⟩
  bijective_obj := Function.bijective_iff_has_inverse.mpr ⟨splitObj F e,fun ⟨_,_⟩ => rfl,fun _ => rfl⟩
end Distribution
variable {P : Endpoints.{b,w,u,max u v} B} (S : P.Split)
def stepGather := gather (fun m => (step S).obj (F m)) (fun m => (step S).map (inj F m))
theorem homIso {C D : Cat.{max u v,u}} (G : C ⥤ D) [G.IsIso] : IsIso G.toCatHom :=
  ⟨⟨G.strictInv.toCatHom,congrArg Functor.toCatHom G.asIsomorphism.unit_eq.symm,congrArg Functor.toCatHom G.asIsomorphism.counit_eq⟩⟩
instance stepIso : IsIso (stepGather F S) := by
  let _ : ∀ a, IsIso ((stepGather F S).app a) := fun a => @homIso (Cat.of (Σ m, Total (F m) (P.extend a.unop))) (Cat.of (Total (sum F) (P.extend a.unop))) (totalGather F (P.extend a.unop)) (gatherIso F _)
  exact NatIso.isIso_of_isIso_app _
variable (Y : Psh.{b,w,u,v} B)
abbrev family (n : Nat) (m : Nat) := pow S (pow S Y m) n
def byInner (n : Nat) := gather (family S Y n) (fun m => ChainPayload.layerMap (inc S Y m) S n)
theorem byInner_at (n m : Nat) : inj (family S Y n) m ≫ byInner S Y n = ChainPayload.layerMap (inc S Y m) S n := inj_gather _ _ _
theorem step_rec (n : Nat) : byInner S Y (n+1) = stepGather (family S Y n) S ≫ (step S).map (byInner S Y n) := by
  apply ext_sum (family S Y (n+1)); intro m
  have h := inj_gather (fun m => (step S).obj (family S Y n m)) (fun m => (step S).map (inj (family S Y n) m)) m
  exact (byInner_at S Y (n+1) m).trans ((congrArg (step S).map (byInner_at S Y n m).symm).trans
    (((step S).map_comp _ _).trans ((congrArg (· ≫ (step S).map (byInner S Y n)) h.symm).trans (Category.assoc ..))))
theorem byInnerIso : (n : Nat) → IsIso (byInner S Y n)
  | 0 => by
    let _ : ∀ a, IsIso ((byInner S Y 0).app a) := fun a => by
      change IsIso ((Sigma.desc fun m => (Iterates.inclusion P S Y m a)).toCatHom)
      have h : Sigma.desc (fun m => Iterates.inclusion P S Y m a) = 𝟭 _ := sigma_ext (fun _ => rfl)
      rw [h]; change IsIso (𝟙 (Cat.of (Iterates.Packed P S Y a))); infer_instance
    exact NatIso.isIso_of_isIso_app _
  | n+1 => by
    let := byInnerIso n
    let _ : IsIso ((step S).map (byInner S Y n)) := Functor.map_isIso _ _
    let _ : IsIso (stepGather (family S Y n) S) := stepIso _ _
    rw [step_rec]; exact (asIso (stepGather (family S Y n) S) ≪≫ asIso ((step S).map (byInner S Y n))).isIso_hom
section Index
variable (K : Nat × Nat → Type u) [∀ i, Category.{max u v} (K i)]
abbrev inner (n : Nat) (m : Nat) := Sigma.incl (C := fun m => K (n,m)) m
abbrev outer (n : Nat) := Sigma.incl (C := fun n => Σ m, K (n,m)) n
def nest : (Σ i, K i) ⥤ Σ n, Σ m, K (n,m) := Sigma.desc fun i => inner K i.1 i.2 ⋙ outer K i.1
def unnest : (Σ n, Σ m, K (n,m)) ⥤ Σ i, K i := Sigma.desc fun n => Sigma.desc fun m => Sigma.incl (C := K) (n,m)
def indexIso : IsoCat (Σ i, K i) (Σ n, Σ m, K (n,m)) where
  functor := nest K
  inverse := unnest K
  unit_eq := by apply sigma_ext; rintro ⟨m,n⟩; rfl
  counit_eq := by apply sigma_ext; intro n; apply sigma_ext; intro m; rfl
end Index
def ofCatIso {C D : Cat.{max u v,u}} (i : C ≅ D) : IsoCat C D :=
  ⟨i.hom.toFunctor,i.inv.toFunctor,congrArg Cat.Hom.toFunctor i.hom_inv_id.symm,congrArg Cat.Hom.toFunctor i.inv_hom_id⟩
variable (A : B)
abbrev double (i : Nat × Nat) := ((family S Y i.1 i.2).obj (op A) : Type u)
noncomputable def innerIso (n : Nat) : IsoCat (Σ m, double S Y A (n,m)) ((pow S ((free S).obj Y) n).obj (op A)) := by
  let := byInnerIso S Y n
  exact ofCatIso ((asIso (byInner S Y n)).app (op A))
/-- The independently defined map into the iterated free object, carrying both
tags through every outer grade. Splitting off the outer tag alone is insufficient. -/
noncomputable def packing : (Σ i, double S Y A i) ≌ Iterates.Packed P S ((free S).obj Y) (op A) :=
  (indexIso (double S Y A)).toEquivalence.trans (ZeroPower.Sum.equiv fun n => (innerIso S Y A n).toEquivalence)
theorem packing_at (n m : Nat) : Sigma.incl (C := double S Y A) (n,m) ⋙ (packing S Y A).functor =
    ((ChainPayload.layerMap (inc S Y m) S n).app (op A)).toFunctor ⋙ Iterates.inclusion P S ((free S).obj Y) n (op A) := rfl
/-- Arithmetic transport in the length tag only, not a permutation of grades. -/
theorem sameLength (i : Nat × Nat) : family S Y i.1 i.2 = pow S Y (i.1+i.2) :=
  (nested S Y i.2 i.1).trans (congrArg (pow S Y) (Nat.add_comm i.2 i.1))
abbrev wholeLayer (i : Nat × Nat) := ((pow S Y (i.1+i.2)).obj (op A) : Type u)
def retag (i : Nat × Nat) : IsoCat (wholeLayer S Y A i) (double S Y A i) :=
  ofCatIso ((eqToIso (sameLength S Y i).symm).app (op A))
noncomputable def cutEquiv : (Σ i, wholeLayer S Y A i) ≌ Iterates.Packed P S ((free S).obj Y) (op A) :=
  (ZeroPower.Sum.equiv (fun i => (retag S Y A i).toEquivalence)).trans (packing S Y A)
theorem inc_cast (l k : Nat) (h : l = k) : eqToHom (congrArg (pow S Y) h) ≫ inc S Y k = inc S Y l := by subst k; exact Category.id_comp _
theorem join_cast (i : Nat × Nat) :
    eqToHom (sameLength S Y i).symm ≫ ChainPayload.layerMap (inc S Y i.2) S i.1 ≫
      inc S ((free S).obj Y) i.1 ≫ join S Y = inc S Y (i.1+i.2) := by
  rw [join_summand]
  have h := inc_cast S Y (i.2+i.1) (i.1+i.2) (Nat.add_comm i.2 i.1)
  rw [← h,← Category.assoc,← Category.assoc,eqToHom_trans,eqToHom_trans,eqToHom_refl,Category.id_comp]
theorem cut_join_at (i : Nat × Nat) : Sigma.incl (C := wholeLayer S Y A) i ⋙
    (cutEquiv S Y A).functor ⋙ ((join S Y).app (op A)).toFunctor =
    Iterates.inclusion P S Y (i.1+i.2) (op A) := by
  rcases i with ⟨n,m⟩
  exact congrArg Cat.Hom.toFunctor (NatTrans.congr_app (join_cast S Y (n,m)) (op A))
theorem cut_join : (cutEquiv S Y A).functor ⋙ ((join S Y).app (op A)).toFunctor =
    Sigma.desc (fun i : Nat × Nat => Iterates.inclusion P S Y (i.1+i.2) (op A)) :=
  sigma_ext (cut_join_at S Y A)
section Rigidity
open BlockCartesian
variable {I : Type} {C D : I → Type u} [∀ i, Category.{max u v} (C i)] [∀ i, Category.{max u v} (D i)]
def isoSum (E : ∀ i, IsoCat (C i) (D i)) : IsoCat (Σ i, C i) (Σ i, D i) where
  functor := ZeroPower.Sum.map fun i => (E i).functor
  inverse := ZeroPower.Sum.map fun i => (E i).inverse
  unit_eq := sigma_ext fun i => congrArg (· ⋙ Sigma.incl (C := C) i) (E i).unit_eq
  counit_eq := sigma_ext fun i => congrArg (· ⋙ Sigma.incl (C := D) i) (E i).counit_eq
noncomputable def rigid : IsoCat (Σ i, wholeLayer S Y A i) (Iterates.Packed P S ((free S).obj Y) (op A)) :=
  ((isoSum (retag S Y A)).trans (indexIso (double S Y A))).trans (isoSum (innerIso S Y A))
theorem rigid_forward : (rigid S Y A).functor = (cutEquiv S Y A).functor := rfl
abbrev forget := Sigma.desc (fun i : Nat × Nat => Iterates.inclusion P S Y (i.1+i.2) (op A))
abbrev mu := ((join S Y).app (op A)).toFunctor
theorem recover : (rigid S Y A).inverse ⋙ forget S Y A = mu S Y A := by
  have h : (rigid S Y A).functor ⋙ mu S Y A = forget S Y A := cut_join S Y A
  exact (congrArg ((rigid S Y A).inverse ⋙ ·) h.symm).trans (congrArg (· ⋙ mu S Y A) (rigid S Y A).counit_eq)
theorem joinIncoming : UniqueIncoming (mu S Y A) := by
  rw [← recover S Y A]
  exact compIncoming (isoIncoming (rigid S Y A).inverse) (descIncoming _ (fun i : Nat × Nat => inclIncoming (K := fun k => ((pow S Y k).obj (op A) : Type u)) (i.1+i.2)))
noncomputable def profile (x : Iterates.Packed P S ((free S).obj Y) (op A)) := ((rigid S Y A).inverse.obj x).1
theorem profile_at (i : Nat × Nat) (x : wholeLayer S Y A i) : profile S Y A ((cutEquiv S Y A).functor.obj ⟨i,x⟩) = i :=
  congrArg Sigma.fst (Functor.congr_obj (rigid S Y A).unit_eq.symm ⟨i,x⟩)
theorem profile_map {x y : Iterates.Packed P S ((free S).obj Y) (op A)} (f : x ⟶ y) : profile S Y A x = profile S Y A y := by
  unfold profile
  have g := (rigid S Y A).inverse.map f
  generalize (rigid S Y A).inverse.obj x = a at g ⊢
  generalize (rigid S Y A).inverse.obj y = b at g ⊢
  cases g; rfl
/-- A particular packed double object is determined by its multiplied object
and its two cut lengths; multiplication alone does not recover the cut. -/
theorem obj_ext {x y : Iterates.Packed P S ((free S).obj Y) (op A)} (h : profile S Y A x = profile S Y A y)
    (e : (mu S Y A).obj x = (mu S Y A).obj y) : x = y := by
  apply (rigid S Y A).inverse.bijective_obj.injective
  have t : (forget S Y A).obj ((rigid S Y A).inverse.obj x) = (forget S Y A).obj ((rigid S Y A).inverse.obj y) :=
    (Functor.congr_obj (recover S Y A) x).trans (e.trans (Functor.congr_obj (recover S Y A) y).symm)
  change ((rigid S Y A).inverse.obj x).1 = ((rigid S Y A).inverse.obj y).1 at h
  generalize (rigid S Y A).inverse.obj x = a at h t ⊢
  generalize (rigid S Y A).inverse.obj y = b at h t ⊢
  rcases a with ⟨i,z⟩; rcases b with ⟨k,w⟩; change i = k at h; subst k
  exact congrArg (Sigma.mk i) (Sigma.mk.inj_iff.mp t).2.eq
theorem profile_length (x : Iterates.Packed P S ((free S).obj Y) (op A)) :
    (profile S Y A x).1 + (profile S Y A x).2 = ((mu S Y A).obj x).1 :=
  congrArg Sigma.fst (Functor.congr_obj (recover S Y A) x)
abbrev choices (x : Iterates.Packed P S Y (op A)) := {i : Nat × Nat // i.1+i.2 = x.1}
def atCut (x : Iterates.Packed P S Y (op A)) (i : choices S Y A x) : wholeLayer S Y A i.1 :=
  cast (congrArg (fun k => ((pow S Y k).obj (op A) : Type u)) i.2.symm) x.2
theorem cut_image (x : Iterates.Packed P S Y (op A)) (i : choices S Y A x) :
    (forget S Y A).obj ⟨i.1,atCut S Y A x i⟩ = x := by
  rcases x with ⟨k,z⟩; rcases i with ⟨i,h⟩; change i.1+i.2 = k at h; subst k; rfl
/-- Exact object fibre of the multiplication over a given packed path: only
its cut position is free, and the dependent grades and payload are not permuted. -/
noncomputable def cutFibre (x : Iterates.Packed P S Y (op A)) :
    {y // (mu S Y A).obj y = x} ≃ choices S Y A x where
  toFun y := ⟨profile S Y A y.1,(profile_length S Y A y.1).trans (congrArg Sigma.fst y.2)⟩
  invFun i := ⟨(cutEquiv S Y A).functor.obj ⟨i.1,atCut S Y A x i⟩,
    (Functor.congr_obj (cut_join S Y A) _).trans (cut_image S Y A x i)⟩
  left_inv y := Subtype.ext (obj_ext S Y A (profile_at S Y A _ _) (by
    exact ((Functor.congr_obj (cut_join S Y A) _).trans (cut_image S Y A x _)).trans y.2.symm))
  right_inv i := Subtype.ext (profile_at S Y A i.1 _)
def positions (x : Iterates.Packed P S Y (op A)) : choices S Y A x ≃ Fin (x.1+1) where
  toFun i := ⟨i.1.1,by have h := i.2; omega⟩
  invFun k := ⟨(k.val,x.1-k.val),by have h := k.isLt; dsimp; omega⟩
  left_inv i := by apply Subtype.ext; apply Prod.ext; · rfl
                   have h := i.2; dsimp; omega
  right_inv _ := rfl
theorem zero_ext {x y : Iterates.Packed P S ((free S).obj Y) (op A)}
    (e : (mu S Y A).obj x = (mu S Y A).obj y) (h : ((mu S Y A).obj x).1 = 0) : x = y := by
  apply obj_ext S Y A _ e
  have f := profile_length S Y A x
  have g := profile_length S Y A y
  have j := congrArg Sigma.fst e
  apply Prod.ext <;> omega
end Rigidity
end ContextualComposition.GrothendieckStep.PackedCuts
