module
public import ContextualComposition.ChainPayload
public import Mathlib.CategoryTheory.Monad.Basic
/-! The right-hand packed telescope: distribute one Grothendieck extension over
the length tag in the payload, then fold generators to form multiplication.
The hom universe max u v is closed under the size of SigmaHom at object
universe u. The packed construction therefore composes with itself here.
No bound on the base universe or equality to the base size is required. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.PackedFree
open CategoryTheory CategoryTheory.Functor Opposite
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split)
abbrev step : (Bᵒᵖ ⥤ Cat.{max u v,u}) ⥤ (Bᵒᵖ ⥤ Cat.{max u v,u}) where
  obj Y := P.extensionPresheaf Y S
  map T := ChainPayload.extensionMap T S
  map_id Y := ChainPayload.layerMap_id (Y := Y) S 1
  map_comp T U := ChainPayload.layerMap_comp T S U 1
abbrev free : (Bᵒᵖ ⥤ Cat.{max u v,u}) ⥤ (Bᵒᵖ ⥤ Cat.{max u v,u}) := ChainPayload.iterateConstruction S
abbrev pow (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (n : Nat) := Iterates.layer P S Y n
def inc (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (n : Nat) : pow S Y n ⟶ (free S).obj Y where
  app A := (Iterates.inclusion P S Y n A).toCatHom
  naturality _ _ _ := rfl

section Sigma
variable {I : Type*} {C : I → Type*} [∀ i, Category* (C i)] {D : Type*} [Category* D]
theorem sigma_ext {F G : (Σ i, C i) ⥤ D} (h : ∀ i, Sigma.incl i ⋙ F = Sigma.incl i ⋙ G) : F = G := by
  fapply Functor.ext
  · rintro ⟨i,x⟩; exact Functor.congr_obj (h i) x
  · rintro ⟨i,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (h i) f
end Sigma
theorem pack_ext {Y Z : (Bᵒᵖ ⥤ Cat.{max u v,u})} {f g : (free S).obj Y ⟶ Z}
    (h : ∀ n, inc S Y n ≫ f = inc S Y n ≫ g) : f = g := by
  apply NatTrans.ext; funext A; apply congrArg Functor.toCatHom
  exact sigma_ext fun n => congrArg Cat.Hom.toFunctor (NatTrans.congr_app (h n) A)
def desc {Y Z : (Bᵒᵖ ⥤ Cat.{max u v,u})} (f : ∀ n, pow S Y n ⟶ Z) : (free S).obj Y ⟶ Z where
  app A := (Sigma.desc fun n => ((f n).app A).toFunctor).toCatHom
  naturality A D a := by
    apply congrArg Functor.toCatHom
    apply sigma_ext
    intro n; exact congrArg Cat.Hom.toFunctor ((f n).naturality a)
theorem inc_desc {Y Z : (Bᵒᵖ ⥤ Cat.{max u v,u})} (f : ∀ n, pow S Y n ⟶ Z) (n : Nat) :
    inc S Y n ≫ desc S f = f n := by apply NatTrans.ext; rfl
theorem inc_map {Y Z : (Bᵒᵖ ⥤ Cat.{max u v,u})} (f : Y ⟶ Z) (n : Nat) :
    inc S Y n ≫ (free S).map f = ChainPayload.layerMap f S n ≫ inc S Z n := by apply NatTrans.ext; rfl

section Distribution
variable (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) {K : Type*} [Category* K] (e : K ⥤ B)
abbrev gather : (Σ n, Total (pow S Y n) e) ⥤ Total ((free S).obj Y) e :=
  Sigma.desc fun n => ChainPayload.fibreMap (inc S Y n) e
def splitObj (x : Total ((free S).obj Y) e) : Σ n, Total (pow S Y n) e :=
  ⟨(payload _ e x).1,pair _ e (grade _ e x) (payload _ e x).2⟩
def splitHom {x y : Σ n, Total (pow S Y n) e} (f : (gather S Y e).obj x ⟶ (gather S Y e).obj y) : x ⟶ y := by
  rcases x with ⟨n,⟨⟨a,s⟩⟩⟩; rcases y with ⟨m,⟨⟨b,t⟩⟩⟩
  obtain ⟨k,h⟩ := homEquiv _ _ f
  change Sigma.SigmaHom (C := fun i => ((pow S Y i).obj (op (e.obj a.unop)) : Type u)) ⟨n,s.unop⟩ ⟨m,((pow S Y m).map (e.map k).op).toFunctor.obj t.unop⟩ at h
  cases h with | mk z => exact Sigma.SigmaHom.mk (arrow k z)
private theorem inc_arrow (n : Nat) {x y : Total (pow S Y n) e} (k : grade _ e x ⟶ grade _ e y)
    (h : payload _ e x ⟶ ((pow S Y n).map (e.map k).op).toFunctor.obj (payload _ e y)) :
    (ChainPayload.fibreMap (inc S Y n) e).map (arrow (x := x) (y := y) k h) =
      arrow (x := (gather S Y e).obj ⟨n,x⟩) (y := (gather S Y e).obj ⟨n,y⟩) k (Sigma.SigmaHom.mk h) := by
  apply (homEquiv _ _).injective
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  have hh := ChainPayload.fibreMap_payload (inc S Y n) e (arrow (x := x) (y := y) k h)
  exact hh.eq
theorem gather_split {x y : Σ n, Total (pow S Y n) e} (f : (gather S Y e).obj x ⟶ (gather S Y e).obj y) :
    (gather S Y e).map (splitHom S Y e f) = f := by
  rcases x with ⟨n,⟨⟨a,s⟩⟩⟩; rcases y with ⟨m,⟨⟨b,t⟩⟩⟩
  obtain ⟨⟨k,h⟩,rfl⟩ := (homEquiv _ _).symm.surjective f
  change Sigma.SigmaHom (C := fun i => ((pow S Y i).obj (op (e.obj a.unop)) : Type u)) ⟨n,s.unop⟩ ⟨m,((pow S Y m).map (e.map k).op).toFunctor.obj t.unop⟩ at h
  cases h; exact inc_arrow S Y e _ _ _
theorem split_gather {x y : Σ n, Total (pow S Y n) e} (f : x ⟶ y) :
    splitHom S Y e ((gather S Y e).map f) = f := by
  cases f with | @mk n x y g =>
    obtain ⟨⟨k,h⟩,rfl⟩ := (homEquiv _ _).symm.surjective g
    change splitHom S Y e (x := ⟨n,x⟩) (y := ⟨n,y⟩) ((ChainPayload.fibreMap (inc S Y n) e).map (arrow (x := x) (y := y) k h)) = _
    rw [inc_arrow]; rfl
instance gatherFaithful : (gather S Y e).Faithful where
  map_injective h := (split_gather S Y e _).symm.trans ((congrArg (splitHom S Y e) h).trans (split_gather S Y e _))
/-- Directly move the length tag past the outer grade without changing that grade. -/
def distribute : Total ((free S).obj Y) e ⥤ Σ n, Total (pow S Y n) e where
  obj := splitObj S Y e
  map {x y} f := splitHom S Y e (x := splitObj S Y e x) (y := splitObj S Y e y) f
  map_id x := by
    apply (gather S Y e).map_injective
    exact (gather_split S Y e (x := splitObj S Y e x) (y := splitObj S Y e x) (𝟙 x)).trans ((gather S Y e).map_id (splitObj S Y e x)).symm
  map_comp {x y z} f g := by
    apply (gather S Y e).map_injective
    exact (gather_split S Y e (x := splitObj S Y e x) (y := splitObj S Y e z) (f ≫ g)).trans
      ((congrArg₂ (· ≫ ·) (gather_split S Y e (x := splitObj S Y e x) (y := splitObj S Y e y) f).symm
        (gather_split S Y e (x := splitObj S Y e y) (y := splitObj S Y e z) g).symm).trans ((gather S Y e).map_comp _ _).symm)
theorem distribute_gather : distribute S Y e ⋙ gather S Y e = 𝟭 _ := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    exact (gather_split S Y e (x := splitObj S Y e x) (y := splitObj S Y e y) f).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm)
theorem gather_distribute : gather S Y e ⋙ distribute S Y e = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ (Sigma.incl (C := fun n => Total (pow S Y n) e) n).map f ≫ 𝟙 _
    exact (split_gather S Y e (Sigma.SigmaHom.mk f)).trans (by rw [Category.id_comp,Category.comp_id]; rfl)
theorem step_ext {D : Type*} [Category* D] {F G : Total ((free S).obj Y) e ⥤ D}
    (h : ∀ n, ChainPayload.fibreMap (inc S Y n) e ⋙ F = ChainPayload.fibreMap (inc S Y n) e ⋙ G) : F = G := by
  have k : gather S Y e ⋙ F = gather S Y e ⋙ G := by
    apply sigma_ext; intro n
    have q : Sigma.incl n ⋙ gather S Y e = ChainPayload.fibreMap (inc S Y n) e := rfl
    change (Sigma.incl n ⋙ gather S Y e) ⋙ F = (Sigma.incl n ⋙ gather S Y e) ⋙ G
    rw [q,h n]
  have j := congrArg (distribute S Y e ⋙ ·) k
  change (distribute S Y e ⋙ gather S Y e) ⋙ F = (distribute S Y e ⋙ gather S Y e) ⋙ G at j
  rw [distribute_gather] at j
  exact j
end Distribution
def consAt (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (A : Bᵒᵖ) :=
  distribute S Y (P.extend A.unop) ⋙ Sigma.desc (fun n => Iterates.inclusion P S Y (n+1) A)
theorem inc_consAt (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (n : Nat) (A : Bᵒᵖ) :
    ChainPayload.fibreMap (inc S Y n) (P.extend A.unop) ⋙ consAt S Y A = Iterates.inclusion P S Y (n+1) A := by
  let D := Sigma.desc (fun n => Iterates.inclusion P S Y (n+1) A)
  exact congrArg (fun F => Sigma.incl n ⋙ F ⋙ D) (gather_distribute S Y (P.extend A.unop))
theorem inc_at_cat (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (n : Nat) (A : Bᵒᵖ) :
    (((step S).map (inc S Y n)).app A ≫ (consAt S Y A).toCatHom) = (inc S Y (n+1)).app A :=
  congrArg Functor.toCatHom (inc_consAt S Y n A)
theorem step_ext_cat (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (A : Bᵒᵖ) {D : Cat.{max u v,u}}
    {F G : ((step S).obj ((free S).obj Y)).obj A ⟶ D}
    (h : ∀ n, ((step S).map (inc S Y n)).app A ≫ F = ((step S).map (inc S Y n)).app A ≫ G) : F = G :=
  congrArg Functor.toCatHom (step_ext S Y (P.extend A.unop) (F := F.toFunctor) (G := G.toFunctor)
    fun n => congrArg Cat.Hom.toFunctor (h n))
set_option backward.isDefEq.respectTransparency false in
/-- One outer grade acts on an arbitrarily packed tail. -/
def cons (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) : (step S).obj ((free S).obj Y) ⟶ (free S).obj Y where
  app A := (consAt S Y A).toCatHom
  naturality A D a := by
    apply step_ext_cat S Y A
    intro n
    rw [← Category.assoc,← NatTrans.naturality,Category.assoc,inc_at_cat S Y n D]
    exact ((inc S Y (n+1)).naturality a).trans <|
      (congrArg (· ≫ ((free S).obj Y).map a) (inc_at_cat S Y n A).symm).trans (Category.assoc _ _ _)
theorem inc_cons (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (n : Nat) :
    (step S).map (inc S Y n) ≫ cons S Y = inc S Y (n+1) := by
  apply NatTrans.ext; funext A; exact congrArg Functor.toCatHom (inc_consAt S Y n A)
theorem step_pack_ext {Y Z : (Bᵒᵖ ⥤ Cat.{max u v,u})} {f g : (step S).obj ((free S).obj Y) ⟶ Z}
    (h : ∀ n, (step S).map (inc S Y n) ≫ f = (step S).map (inc S Y n) ≫ g) : f = g := by
  apply NatTrans.ext; funext A; apply congrArg Functor.toCatHom
  exact step_ext S Y (P.extend A.unop) fun n => congrArg Cat.Hom.toFunctor (NatTrans.congr_app (h n) A)
section Algebra
set_option backward.isDefEq.respectTransparency false
variable {Y Z W : (Bᵒᵖ ⥤ Cat.{max u v,u})}
def foldLayer (a : (step S).obj Z ⟶ Z) (f : Y ⟶ Z) : (n : Nat) → (pow S Y n ⟶ Z)
  | 0 => f
  | n+1 => (step S).map (foldLayer a f n) ≫ a
def fold (a : (step S).obj Z ⟶ Z) (f : Y ⟶ Z) : (free S).obj Y ⟶ Z := desc S (foldLayer S a f)
theorem inc_fold (a : (step S).obj Z ⟶ Z) (f : Y ⟶ Z) (n : Nat) :
    inc S Y n ≫ fold S a f = foldLayer S a f n := inc_desc S _ n
abbrev HomLaw {X Z : (Bᵒᵖ ⥤ Cat.{max u v,u})} (a : (step S).obj X ⟶ X) (c : (step S).obj Z ⟶ Z) (f : X ⟶ Z) :=
  a ≫ f = (step S).map f ≫ c
theorem fold_hom (a : (step S).obj Z ⟶ Z) (f : Y ⟶ Z) : HomLaw S (cons S Y) a (fold S a f) := by
  apply step_pack_ext; intro n
  erw [← Category.assoc,inc_cons S Y n,inc_fold S a f (n+1),← Category.assoc,← Functor.map_comp,inc_fold S a f n]
  rfl
theorem unique (a : (step S).obj Z ⟶ Z) (k : (free S).obj Y ⟶ Z) (hk : HomLaw S (cons S Y) a k) :
    k = fold S a (inc S Y 0 ≫ k) := by
  apply pack_ext; intro n; erw [inc_fold S a (Y := Y) (inc S Y 0 ≫ k) n]
  induction n with
  | zero => rfl
  | succ n ih =>
    erw [← inc_cons S Y n,Category.assoc,hk,← Category.assoc,← Functor.map_comp,ih]
    rfl
theorem hom_ext (a : (step S).obj Z ⟶ Z) {f g : (free S).obj Y ⟶ Z}
    (hf : HomLaw S (cons S Y) a f) (hg : HomLaw S (cons S Y) a g) (h : inc S Y 0 ≫ f = inc S Y 0 ≫ g) : f = g :=
  (unique S a f hf).trans ((congrArg (fold S a) h).trans (unique S a g hg).symm)
theorem hom_comp {X : (Bᵒᵖ ⥤ Cat.{max u v,u})} {a : (step S).obj X ⟶ X} {b : (step S).obj Y ⟶ Y}
    {c : (step S).obj Z ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : HomLaw S a b f) (hg : HomLaw S b c g) : HomLaw S a c (f ≫ g) := by
  unfold HomLaw at *; rw [← Category.assoc,hf,Category.assoc,hg,Functor.map_comp,Category.assoc]
theorem map_hom (f : Y ⟶ Z) : HomLaw S (cons S Y) (cons S Z) ((free S).map f) := by
  apply step_pack_ext; intro n
  erw [← Category.assoc,inc_cons S Y n,inc_map S f (n+1)]
  calc
    _ = (step S).map (ChainPayload.layerMap f S n) ≫ (step S).map (inc S Z n) ≫ cons S Z :=
      congrArg ((step S).map (ChainPayload.layerMap f S n) ≫ ·) (inc_cons S Z n).symm
    _ = (step S).map (ChainPayload.layerMap f S n ≫ inc S Z n) ≫ cons S Z :=
      ((step S).map_comp_assoc _ _ _).symm
    _ = (step S).map (inc S Y n ≫ (free S).map f) ≫ cons S Z :=
      congrArg (fun t => (step S).map t ≫ cons S Z) (inc_map S f n).symm
    _ = _ := (step S).map_comp_assoc _ _ _
def join (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) := fold S (cons S Y) (𝟙 ((free S).obj Y))
theorem zero_join (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) : inc S ((free S).obj Y) 0 ≫ join S Y = 𝟙 ((free S).obj Y) :=
  inc_fold S _ _ 0
theorem join_natural (f : Y ⟶ Z) :
    (free S).map ((free S).map f) ≫ join S Z = join S Y ≫ (free S).map f := by
  apply hom_ext S (cons S Z) (hom_comp S (map_hom S _) (fold_hom S _ _)) (hom_comp S (fold_hom S _ _) (map_hom S _))
  erw [← Category.assoc,inc_map,Category.assoc,zero_join,Category.comp_id]
theorem join_assoc (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) :
    (free S).map (join S Y) ≫ join S Y = join S ((free S).obj Y) ≫ join S Y := by
  apply hom_ext S (cons S Y) (hom_comp S (map_hom S _) (fold_hom S _ _)) (hom_comp S (fold_hom S _ _) (fold_hom S _ _))
  erw [← Category.assoc,inc_map,Category.assoc,zero_join,Category.comp_id]
theorem join_right (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) :
    (free S).map (inc S Y 0) ≫ join S Y = 𝟙 ((free S).obj Y) := by
  apply hom_ext S (Y := Y) (cons S Y) (hom_comp S (map_hom S _) (fold_hom S _ _))
  · unfold HomLaw; rw [Functor.map_id,Category.id_comp,Category.comp_id]
  · erw [← Category.assoc,inc_map,Category.assoc,zero_join,Category.comp_id]
/-- Monad on the packed-iterate presheaf endofunctor. Its unit inserts zero
outer grades; this is not the length-one unit for a telescope of spans. -/
def monad : Monad (Bᵒᵖ ⥤ Cat.{max u v,u}) where
  toFunctor := free S
  η := { app := fun Y => inc S Y 0, naturality := fun _ _ f => (inc_map S f 0).symm }
  μ := { app := join S, naturality := fun _ _ f => join_natural S f }
  assoc := join_assoc S
  left_unit := zero_join S
  right_unit := join_right S
/-- The universal property at a generator Y: interpretations of single steps
extend uniquely to all dependent chains, including their payload arrows. -/
def foldEquiv (a : (step S).obj Z ⟶ Z) :
    {k : (free S).obj Y ⟶ Z // HomLaw S (cons S Y) a k} ≃ (Y ⟶ Z) where
  toFun k := inc S Y 0 ≫ k.val
  invFun f := ⟨fold S a f,fold_hom S a f⟩
  left_inv k := Subtype.ext (unique S a k.val k.property).symm
  right_inv f := inc_fold S a f 0
def generator : step S ⟶ free S where
  app Y := inc S Y 1
  naturality _ _ f := (inc_map S f 1).symm
theorem nested (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (m : Nat) :
    (n : Nat) → pow S (pow S Y m) n = pow S Y (m+n)
  | 0 => rfl
  | n+1 => congrArg (step S).obj (nested Y m n)
theorem foldLayer_map (f : Y ⟶ Z) (a : (step S).obj W ⟶ W) (k : Z ⟶ W) (n : Nat) :
    ChainPayload.layerMap f S n ≫ foldLayer S a k n = foldLayer S a (f ≫ k) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step S).map (ChainPayload.layerMap f S n) ≫ (step S).map (foldLayer S a k n) ≫ a = _
    exact ((step S).map_comp_assoc _ _ _).symm.trans (congrArg (fun t => (step S).map t ≫ a) ih)
theorem foldLayer_inc (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (m n : Nat) :
    foldLayer S (cons S Y) (inc S Y m) n = eqToHom (nested S Y m n) ≫ inc S Y (m+n) := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
    change (step S).map (foldLayer S (cons S Y) (inc S Y m) n) ≫ cons S Y = _
    rw [ih,Functor.map_comp_assoc,inc_cons,eqToHom_map]
    rfl
/-- On the (outer n, inner m) summand multiplication returns length m+n.
This equality of natural transformations controls whole arrows, not just the tag. -/
theorem join_summand (Y : (Bᵒᵖ ⥤ Cat.{max u v,u})) (m n : Nat) :
    ChainPayload.layerMap (inc S Y m) S n ≫ inc S ((free S).obj Y) n ≫ join S Y =
      eqToHom (nested S Y m n) ≫ inc S Y (m+n) := by
  change _ ≫ inc S ((free S).obj Y) n ≫ fold S (cons S Y) (𝟙 _) = _
  rw [inc_fold S,foldLayer_map S,Category.comp_id]
  exact foldLayer_inc S Y m n
end Algebra
end ContextualComposition.GrothendieckStep.PackedFree
