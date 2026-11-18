module
public import ContextualComposition.ChainRestriction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ChainPayload
open CategoryTheory CategoryTheory.Functor Opposite TelescopeSquares
universe b w u v k j
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K]
variable {Y Z W : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
def cell (e : K ⥤ B) : diagram Y e ⟶ diagram Z e := whiskerLeft e.op (whiskerRight T Cat.opFunctor)

def fibreMap (e : K ⥤ B) : Total Y e ⥤ Total Z e := (Grothendieck.map (cell T e)).op

theorem fibreMap_id (e : K ⥤ B) : fibreMap (𝟙 Y) e = 𝟭 _ := by
  have h : cell (𝟙 Y) e = 𝟙 _ := by
    apply NatTrans.ext; funext p
    exact Cat.opFunctor.map_id _
  unfold fibreMap
  rw [h,Grothendieck.map_id_eq]; rfl

theorem fibreMap_comp (U : Z ⟶ W) (e : K ⥤ B) : fibreMap (T ≫ U) e = fibreMap T e ⋙ fibreMap U e := by
  have h : cell (T ≫ U) e = cell T e ≫ cell U e := by
    apply NatTrans.ext; funext p
    exact Cat.opFunctor.map_comp _ _
  unfold fibreMap
  rw [h,Grothendieck.map_comp_eq]; rfl

variable {L : Type*} [Category* L]
theorem base_square (e : K ⥤ B) (d : L ⥤ B) (r : K ⥤ L) (l : r ⋙ d ⟶ e) :
    restrict Y e d r l ⋙ fibreMap T d = fibreMap T e ⋙ restrict Z e d r l := by
  have h : restrictionCell Y e d r l ≫ whiskerLeft r.op (cell T d) =
      cell T e ≫ restrictionCell Z e d r l := by
    apply NatTrans.ext; funext p
    exact (whiskerRight T Cat.opFunctor).naturality ((NatTrans.op l).app p)
  have hm := congrArg Grothendieck.map h
  simp only [Grothendieck.map_comp_eq] at hm
  exact congrArg (fun F => (F ⋙ Grothendieck.pre (diagram Z d) r.op).op) hm

variable {P : Endpoints.{b,w,u,v} B} (S : P.Split)
def extensionMap : P.extensionPresheaf Y S ⟶ P.extensionPresheaf Z S where
  app A := (fibreMap T (P.extend A.unop)).toCatHom
  naturality _ _ f := congrArg Functor.toCatHom (base_square T _ _ _ (P.lift f.unop))

def layerMap : (n : Nat) → Iterates.layer P S Y n ⟶ Iterates.layer P S Z n
  | 0 => T
  | n+1 => extensionMap (layerMap n) S

theorem layerMap_id : (n : Nat) → layerMap (𝟙 Y) S n = 𝟙 _
  | 0 => rfl
  | n+1 => by
    change extensionMap (layerMap (𝟙 Y) S n) S = _
    rw [layerMap_id n]
    apply NatTrans.ext; funext A
    exact congrArg Functor.toCatHom (fibreMap_id _)

theorem layerMap_comp (U : Z ⟶ W) : (n : Nat) →
    layerMap (T ≫ U) S n = layerMap T S n ≫ layerMap U S n
  | 0 => rfl
  | n+1 => by
    change extensionMap (layerMap (T ≫ U) S n) S = _
    rw [layerMap_comp U n]
    apply NatTrans.ext; funext A
    exact congrArg Functor.toCatHom (fibreMap_comp _ _ _)

theorem target {A D : B} (a : A ⟶ D) (z : Y.obj (op D)) :
    (T.app (op A)).toFunctor.obj ((Y.map a.op).toFunctor.obj z) =
      (Z.map a.op).toFunctor.obj ((T.app (op D)).toFunctor.obj z) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (T.naturality a.op)) z

def onSquare {n A D} {a : A ⟶ D} {t : Chain P n A} {z : Chain P n D}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    (f : DecoratedHom Y a t z x y) : DecoratedHom Z a t z
      ((T.app (op (endpoint t))).toFunctor.obj x) ((T.app (op (endpoint z))).toFunctor.obj y) :=
  ⟨f.1,(T.app (op (endpoint t))).toFunctor.map f.2 ≫ eqToHom (target T (terminalMap f.1) y)⟩

theorem onSquare_id {n A} (t : Chain P n A) (x : Y.obj (op (endpoint t))) :
    onSquare T (decoratedId S Y t x) = decoratedId S Z t ((T.app _).toFunctor.obj x) := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  dsimp only [onSquare,decoratedId]
  rw [eqToHom_map,eqToHom_trans]

private theorem strip {C : Type*} [Category* C] {x y z : C} (m : x ⟶ y) (h : y = z) :
    Aligned (m ≫ eqToHom h) m := Aligned.trailing _ _

set_option backward.isDefEq.respectTransparency false in
private theorem map_change {A D : B} (a : A ⟶ D) {x y : Y.obj (op D)} (h : x ⟶ y) :
    Aligned ((T.app (op A)).toFunctor.map ((Y.map a.op).toFunctor.map h))
      ((Z.map a.op).toFunctor.map ((T.app (op D)).toFunctor.map h)) := by
  have eqF := congrArg Cat.Hom.toFunctor (T.naturality a.op)
  exact ⟨target T a x,target T a y,by
    have e := Functor.congr_hom eqF h
    exact (CategoryTheory.comp_eqToHom_iff _ _ _).2 (by simpa only [Category.assoc,Cat.Hom.comp_toFunctor,Functor.comp_map] using e)⟩

set_option backward.isDefEq.respectTransparency false in
theorem onSquare_comp {n A D E} {a : A ⟶ D} {b : D ⟶ E} {t : Chain P n A} {z : Chain P n D}
    {l : Chain P n E} {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    {j : Y.obj (op (endpoint l))} (f : DecoratedHom Y a t z x y) (g : DecoratedHom Y b z l y j) :
    onSquare T (decoratedComp S Y f g) = decoratedComp S Z (onSquare T f) (onSquare T g) := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply Aligned.eq
  change Aligned (_ ≫ eqToHom _) (_ ≫ _ ≫ eqToHom _)
  apply (strip _ _).trans
  conv_rhs => rw [← Category.assoc]
  apply Aligned.trans _ (strip _ _).symm
  dsimp only [decoratedComp,onSquare]
  rw [Functor.map_comp,Functor.map_comp]
  apply Aligned.comp
  · exact (strip _ _).symm
  · rw [eqToHom_map]
    apply (strip _ _).trans
    apply (map_change T (terminalMap f.1) g.2).trans
    exact ((strip _ _).map _).symm

set_option backward.isDefEq.respectTransparency false in
theorem fibreMap_payload (e : K ⥤ B) {x y : Total Y e} (f : x ⟶ y) :
    Aligned (payloadMap ((fibreMap T e).map f)) ((T.app (op (e.obj (grade Y e x)))).toFunctor.map (payloadMap f)) := by
  have hh : payloadMap ((fibreMap T e).map f) =
      (T.app (op (e.obj (grade Y e x)))).toFunctor.map (payloadMap f) ≫
        eqToHom (target T (e.map (gradeMap f)) (payload Y e y)) := by
    change (Grothendieck.Hom.fiber ((Grothendieck.map (cell T e)).map f.unop)).unop = _
    dsimp [Grothendieck.map,payloadMap]; simp; rw [unop_comp]; congr 1; apply eqToHom_unop
  exact hh ▸ Aligned.trailing _ _

theorem realized {n A} (t : Chain P n A) (x : Y.obj (op (endpoint t))) :
    realize Z S t ((T.app (op (endpoint t))).toFunctor.obj x) =
      ((layerMap T S n).app (op A)).toFunctor.obj (realize Y S t x) := by
  induction t with
  | nil => rfl
  | cons p t ih => exact congrArg (pair _ _ p) (ih x)

def onFibreObj {n A} (X : Fibre P Y n A) : Fibre P Z n A :=
  ⟨X.chain,(T.app (op (endpoint X.chain))).toFunctor.obj X.value⟩

theorem onSquare_rebase {n A D} {a b : A ⟶ D} {t : Chain P n A} {z : Chain P n D}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    (h : a = b) (f : DecoratedHom Y a t z x y) :
    onSquare T (rebaseDecorated Y h f) = rebaseDecorated Z h (onSquare T f) := by subst b; rfl

def onFibre (n : Nat) (A : B) : Fibre.asCat (Y := Y) S n A ⥤ Fibre.asCat (Y := Z) S n A where
  obj X := onFibreObj T X
  map f := onSquare T f
  map_id X := onSquare_id T S X.chain X.value
  map_comp f g := (onSquare_rebase T _ _).trans (congrArg (rebaseDecorated Z _) (onSquare_comp T S f g))

private theorem pair_align (e : K ⥤ B) {p q : K} {x x' : Y.obj (op (e.obj p))}
    {y y' : Y.obj (op (e.obj q))} (hx : x = x') (hy : y = y')
    {f : pair Y e p x ⟶ pair Y e q y} {g : pair Y e p x' ⟶ pair Y e q y'}
    (hg : gradeMap f = gradeMap g) (hp : Aligned (payloadMap f) (payloadMap g)) : Aligned f g := by
  subst x'; subst y'
  have aux {k j : p ⟶ q} (h : k = j)
      {m : x ⟶ (Y.map (e.map k).op).toFunctor.obj y} {l : x ⟶ (Y.map (e.map j).op).toFunctor.obj y}
      (hm : Aligned m l) : HEq m l := by subst j; exact heq_of_eq hm.eq
  have he := (homEquiv _ _).injective (Sigma.ext hg (aux hg hp))
  rw [he]; exact Aligned.refl _

private theorem alignedEq {C : Type*} [Category* C] {x y : C} {f g : x ⟶ y} (h : f = g) : Aligned f g := by
  subst g; exact Aligned.refl _

set_option backward.isDefEq.respectTransparency false in
theorem compared_square : {n : Nat} → {A D : B} → {a : A ⟶ D} → (t : Chain P n A) → (z : Chain P n D) →
    (x : Y.obj (op (endpoint t))) → (y : Y.obj (op (endpoint z))) → (f : DecoratedHom Y a t z x y) →
    Aligned (squareEquiv Z S a t z _ _ (onSquare T f))
      (((layerMap T S n).app (op A)).toFunctor.map (squareEquiv Y S a t z x y f))
  | 0, _, _, _, .nil _, .nil _, _, _, f => Aligned.trailing _ _
  | n+1, A, D, a, .cons p t, .cons q z, x, y, f => by
    let M := layerMap T S n
    let F := Iterates.layer P S Y n
    let G := Iterates.layer P S Z n
    have hx := realized T S t x
    have hy := realized T S z y
    let e := P.extend A
    let d := P.extend D
    let m := (P.lift a).app q
    have hy' : (G.map m.op).toFunctor.obj (realize Z S z ((T.app _).toFunctor.obj y)) =
        (M.app _).toFunctor.obj ((F.map m.op).toFunctor.obj (realize Y S z y)) :=
      (congrArg (G.map m.op).toFunctor.obj hy).trans (target M m (realize Y S z y)).symm
    apply pair_align e hx hy' (by rfl)
    apply Aligned.trans _ (fibreMap_payload M e (squareEquiv Y S a (.cons p t) (.cons q z) x y f)).symm
    apply (alignedEq (compared_tail Z S (onSquare T f))).trans
    apply (Aligned.trailing _ _).trans
    apply (compared_square t z x y (tailPart Y f)).trans
    apply Aligned.symm
    apply Aligned.map
    exact (alignedEq (compared_tail Y S f)).trans (Aligned.trailing _ _)
private theorem vert {n A} {X Q : Fibre P Y n A} (f : Fibre.Hom X Q) :
    Aligned (Fibre.homComparison S X Q f) (squareEquiv Y S _ _ _ _ _ f) := by
  have aux {C : Type u} [Category.{v} C] {x a b : C} (p : a = b) (m : x ⟶ a) :
      Aligned (Equiv.cast (congrArg (fun dest => x ⟶ dest) p) m) m := by subst b; exact Aligned.refl _
  exact aux (Functor.congr_obj (congrArg Cat.Hom.toFunctor ((Iterates.layer P S Y n).map_id (op A))) (Fibre.obj S Q)) _

private theorem conjugate {C : Type*} [Category* C] {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'}
    (h : Aligned f g) (s : x = x') (t : y' = y) : f = eqToHom s ≫ g ≫ eqToHom t := by
  subst x'; subst y'; simpa using h.eq

theorem comparison_square (n : Nat) (A : B) :
    onFibre T S n A ⋙ Fibre.comparison S n A =
      Fibre.comparison S n A ⋙ ((layerMap T S n).app (op A)).toFunctor := by
  fapply Functor.ext
  · intro X; exact realized T S X.chain X.value
  · intro X Q f
    apply conjugate
    exact (vert S (X := onFibreObj T X) (Q := onFibreObj T Q) (onSquare T f)).trans
      ((compared_square T S X.chain Q.chain X.value Q.value f).trans
      (((vert S f).symm).map _))

private theorem obj_inj (n : Nat) (A : B) : Function.Injective (Fibre.obj S (Y := Y) (n := n) (A := A)) := by
  rintro ⟨t,x⟩ ⟨z,y⟩ h
  have e := (realizedEquiv Y S n A).injective (a₁ := ⟨t,x⟩) (a₂ := ⟨z,y⟩) h
  exact congrArg (fun d => (⟨d.1,d.2⟩ : Fibre P Y n A)) e

set_option backward.isDefEq.respectTransparency false in
private theorem reflect {n A} {C : Type*} [Category* C] {F G : C ⥤ Fibre.asCat (Y := Y) S n A}
    (h : F ⋙ Fibre.comparison S n A = G ⋙ Fibre.comparison S n A) : F = G := by
  fapply Functor.ext
  · intro X; exact obj_inj S n A (Functor.congr_obj h X)
  · intro X Q f
    apply (Fibre.comparison S n A).map_injective
    simp only [Functor.map_comp,eqToHom_map]
    exact Functor.congr_hom h f

theorem mixed (n : Nat) {A D : B} (a : A ⟶ D) :
    Fibre.pullFunctor (Y := Y) S a ⋙ onFibre T S n A = onFibre T S n D ⋙ Fibre.pullFunctor S a := by
  apply reflect S (n := n) (A := A)
  change Fibre.pullFunctor S a ⋙ (onFibre T S n A ⋙ Fibre.comparison S n A) = onFibre T S n D ⋙ (Fibre.pullFunctor S a ⋙ Fibre.comparison S n A)
  rw [comparison_square,Fibre.comparison_square]
  change (Fibre.pullFunctor S a ⋙ Fibre.comparison S n A) ⋙ _ = (onFibre T S n D ⋙ Fibre.comparison S n D) ⋙ _
  rw [Fibre.comparison_square,comparison_square]
  exact congrArg (fun H => Fibre.comparison (Y := Y) S n D ⋙ H.toFunctor)
    ((layerMap T S n).naturality a.op)

def sourceMap (n : Nat) : Fibre.sourcePresheaf (Y := Y) S n ⟶ Fibre.sourcePresheaf (Y := Z) S n where
  app A := (onFibre T S n A.unop).toCatHom
  naturality _ _ f := congrArg Functor.toCatHom (mixed T S n f.unop)
theorem sourceMap_id (n : Nat) : sourceMap (𝟙 Y) S n = 𝟙 _ := by
  apply NatTrans.ext; funext A
  apply congrArg Functor.toCatHom
  apply reflect S (n := n) (A := A.unop)
  rw [comparison_square,layerMap_id]; rfl

theorem sourceMap_comp (U : Z ⟶ W) (n : Nat) : sourceMap (T ≫ U) S n = sourceMap T S n ≫ sourceMap U S n := by
  apply NatTrans.ext; funext A
  change (onFibre (T ≫ U) S n A.unop).toCatHom = (onFibre T S n A.unop ⋙ onFibre U S n A.unop).toCatHom
  apply congrArg Functor.toCatHom
  apply reflect S
  rw [comparison_square,layerMap_comp]
  change _ = onFibre T S n A.unop ⋙ (onFibre U S n A.unop ⋙ Fibre.comparison S n A.unop)
  rw [comparison_square]
  change _ = (onFibre T S n A.unop ⋙ Fibre.comparison S n A.unop) ⋙ _
  rw [comparison_square]
  rfl

def pack {C : Nat → Type*} {D : Nat → Type*} [∀ n, Category* (C n)] [∀ n, Category* (D n)]
    (F : ∀ n, C n ⥤ D n) : (Σ n,C n) ⥤ Σ n,D n := Sigma.desc fun n => F n ⋙ Sigma.incl n

private theorem pack_comp {C D E : Nat → Type*}
    [∀ n, Category* (C n)] [∀ n, Category* (D n)] [∀ n, Category* (E n)]
    (F : ∀ n, C n ⥤ D n) (G : ∀ n, D n ⥤ E n) :
    pack (fun n => F n ⋙ G n) = pack F ⋙ pack G := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]; exact (Category.comp_id _).symm

theorem pack_square {C D E H : Nat → Type*}
    [∀ n, Category* (C n)] [∀ n, Category* (D n)] [∀ n, Category* (E n)] [∀ n, Category* (H n)]
    (F : ∀ n, C n ⥤ D n) (G : ∀ n, D n ⥤ H n) (R : ∀ n,C n ⥤ E n) (V : ∀ n,E n ⥤ H n)
    (hh : ∀ n, F n ⋙ G n = R n ⋙ V n) : pack F ⋙ pack G = pack R ⋙ pack V := by
  rw [← pack_comp,← pack_comp]; exact congrArg pack (funext hh)

def allSourceMap : Fibre.allSourcePresheaf (Y := Y) S ⟶ Fibre.allSourcePresheaf (Y := Z) S where
  app A := (pack fun n => onFibre T S n A.unop).toCatHom
  naturality _ _ f := congrArg Functor.toCatHom (pack_square _ _ _ _ fun n => mixed T S n f.unop)

def allIterateMap : Iterates.packedPresheaf P S Y ⟶ Iterates.packedPresheaf P S Z where
  app A := (pack fun n => ((layerMap T S n).app A).toFunctor).toCatHom
  naturality _ _ f := congrArg Functor.toCatHom (pack_square _ _ _ _ fun n =>
    congrArg Cat.Hom.toFunctor ((layerMap T S n).naturality f))

theorem allComparison_square (A : B) :
    ((allSourceMap T S).app (op A)).toFunctor ⋙ Fibre.allComparison S A =
      Fibre.allComparison S A ⋙ ((allIterateMap T S).app (op A)).toFunctor :=
  pack_square _ _ _ _ fun n => comparison_square T S n A

private theorem pack_id {C : Nat → Type*} [∀ n, Category* (C n)] :
    pack (fun n => 𝟭 (C n)) = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]; exact (Category.comp_id _).symm

theorem allSource_id : allSourceMap (𝟙 Y) S = 𝟙 _ := by
  apply NatTrans.ext; funext A
  apply congrArg Functor.toCatHom
  apply Eq.trans _ pack_id
  apply congrArg pack
  exact funext fun n => congrArg Cat.Hom.toFunctor (NatTrans.congr_app (sourceMap_id S n) A)

theorem allSource_comp (U : Z ⟶ W) : allSourceMap (T ≫ U) S = allSourceMap T S ≫ allSourceMap U S := by
  apply NatTrans.ext; funext A
  apply congrArg Functor.toCatHom
  apply Eq.trans _ (pack_comp (fun n => onFibre T S n A.unop) (fun n => onFibre U S n A.unop))
  apply congrArg pack
  exact funext fun n => congrArg Cat.Hom.toFunctor (NatTrans.congr_app (sourceMap_comp T S U n) A)

theorem allIterate_id : allIterateMap (𝟙 Y) S = 𝟙 _ := by
  apply NatTrans.ext; funext A
  apply congrArg Functor.toCatHom
  apply Eq.trans _ pack_id
  apply congrArg pack
  exact funext fun n => congrArg Cat.Hom.toFunctor (NatTrans.congr_app (layerMap_id S n) A)

theorem allIterate_comp (U : Z ⟶ W) : allIterateMap (T ≫ U) S = allIterateMap T S ≫ allIterateMap U S := by
  apply NatTrans.ext; funext A
  apply congrArg Functor.toCatHom
  apply Eq.trans _ (pack_comp (fun n => ((layerMap T S n).app A).toFunctor) (fun n => ((layerMap U S n).app A).toFunctor))
  apply congrArg pack
  exact funext fun n => congrArg Cat.Hom.toFunctor (NatTrans.congr_app (layerMap_comp T S U n) A)

noncomputable def sourceConstruction : (Bᵒᵖ ⥤ Cat.{v,u}) ⥤ (Bᵒᵖ ⥤ Cat) where
  obj Y := Fibre.allSourcePresheaf (Y := Y) S
  map T := allSourceMap T S
  map_id _ := allSource_id S
  map_comp T U := allSource_comp T S U

def iterateConstruction : (Bᵒᵖ ⥤ Cat.{v,u}) ⥤ (Bᵒᵖ ⥤ Cat) where
  obj Y := Iterates.packedPresheaf P S Y
  map T := allIterateMap T S
  map_id _ := allIterate_id S
  map_comp T U := allIterate_comp T S U
end ContextualComposition.GrothendieckStep.ChainPayload
