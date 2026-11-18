module
public import ContextualComposition.ChainIdentity
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeSquares
open CategoryTheory Opposite
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B}

/-- Pull the head grade along the given base map and continue over its endpoint lift. -/
def pullChain : {n : Nat} → {A D : B} → (a : A ⟶ D) → Chain P n D → Chain P n A
  | 0, A, _, _, .nil _ => .nil A
  | _+1, _, _, a, .cons q z => .cons ((P.grades.map a.op).toFunctor.obj q) (pullChain ((P.lift a).app q) z)

theorem next_cart {A D : B} (a : A ⟶ D) (q : P.grades.obj (op D)) :
    next a (𝟙 ((P.grades.map a.op).toFunctor.obj q)) = (P.lift a).app q := by simp [next]

def liftSquare : {n : Nat} → {A D : B} → (a : A ⟶ D) → (z : Chain P n D) → Square a (pullChain a z) z
  | 0, _, _, _, .nil _ => PUnit.unit
  | _+1, _, _, a, .cons q z => ⟨𝟙 _, rebaseSquare (t := pullChain ((P.lift a).app q) z) (z := z)
      (next_cart a q).symm (liftSquare ((P.lift a).app q) z)⟩

def endLift : {n : Nat} → {A D : B} → (a : A ⟶ D) → (z : Chain P n D) → endpoint (pullChain a z) ⟶ endpoint z
  | 0, _, _, a, .nil _ => a
  | _+1, _, _, a, .cons q z => endLift ((P.lift a).app q) z

theorem terminal_lift : {n : Nat} → {A D : B} → (a : A ⟶ D) → (z : Chain P n D) →
    terminalMap (u := a) (t := pullChain a z) (z := z) (liftSquare a z) = endLift a z
  | 0, _, _, _, .nil _ => rfl
  | _+1, _, _, a, .cons q z => (terminal_rebase _ _).trans (terminal_lift ((P.lift a).app q) z)

variable (Y : Bᵒᵖ ⥤ Cat.{v,u}) (S : P.Split)
def pullValue {n A D} (a : A ⟶ D) (z : Chain P n D) (y : Y.obj (op (endpoint z))) :
    Y.obj (op (endpoint (pullChain a z))) := (Y.map (endLift a z).op).toFunctor.obj y

def liftDecorated {n A D} (a : A ⟶ D) (z : Chain P n D) (y : Y.obj (op (endpoint z))) :
    DecoratedHom Y a (pullChain a z) z (pullValue Y a z y) y :=
  ⟨liftSquare a z,eqToHom (congrArg (fun k : endpoint (pullChain a z) ⟶ endpoint z => (Y.map k.op).toFunctor.obj y) (terminal_lift a z).symm)⟩

theorem realized_pull : {n : Nat} → {A D : B} → (a : A ⟶ D) → (z : Chain P n D) →
    (y : Y.obj (op (endpoint z))) →
    realize Y S (pullChain a z) (pullValue Y a z y) =
      ((Iterates.layer P S Y n).map a.op).toFunctor.obj (realize Y S z y)
  | 0, _, _, _, .nil _, _ => rfl
  | n+1, A, _, a, .cons q z, y =>
    congrArg (pair (Iterates.layer P S Y n) (P.extend A) ((P.grades.map a.op).toFunctor.obj q))
      (realized_pull ((P.lift a).app q) z y)

set_option backward.isDefEq.respectTransparency false in
theorem tail_lift {n A D} (a : A ⟶ D) (q : P.grades.obj (op D)) (z : Chain P n ((P.extend D).obj q))
    (y : Y.obj (op (endpoint z))) :
    tailPart Y (liftDecorated Y a (.cons q z) y) =
      rebaseDecorated Y (next_cart a q).symm (liftDecorated Y ((P.lift a).app q) z y) := by
  rw [rebaseDecorated_data]
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  dsimp only [tailPart,liftDecorated]
  rw [eqToHom_trans]
private theorem alignedOfEq {C : Type*} [Category* C] {x y : C} {f g : x ⟶ y} (h : f = g) : Aligned f g := by subst g; exact Aligned.refl _
private theorem alignedTransport {C : Type*} [Category* C] {x y : C} (h : x = y) :
    Aligned (eqToHom h) (𝟙 x) := by subst y; exact Aligned.refl _
private theorem gradeTransport {K : Type*} [Category* K] {e : K ⥤ B} {x y : Total Y e} (h : x = y) :
    Aligned (gradeMap (eqToHom h)) (𝟙 (grade Y e x)) := by subst y; exact Aligned.refl _
set_option backward.isDefEq.respectTransparency false in
private theorem payloadTransport {K : Type*} [Category* K] {e : K ⥤ B} {x y : Total Y e} (h : x = y) :
    Aligned (payloadMap (eqToHom h)) (𝟙 (payload Y e x)) := by
  subst y
  change Aligned ((Grothendieck.Hom.fiber (𝟙 x.unop)).unop) _
  rw [Grothendieck.id_fiber,eqToHom_unop]
  exact alignedTransport _

private theorem extAligned {K : Type*} [Category* K] {e : K ⥤ B}
    {x y : Total Y e} {f g : x ⟶ y} (head : gradeMap f = gradeMap g)
    (tail : Aligned (payloadMap f) (payloadMap g)) : f = g := by
  apply (homEquiv x y).injective
  refine Sigma.ext head ?_
  have aux {k j : grade Y e x ⟶ grade Y e y}
      {m : payload Y e x ⟶ (Y.map (e.map k).op).toFunctor.obj (payload Y e y)}
      {l : payload Y e x ⟶ (Y.map (e.map j).op).toFunctor.obj (payload Y e y)}
      (hk : k = j) (hh : Aligned m l) : HEq m l := by
    subst j; exact heq_of_eq hh.eq
  exact aux head tail

set_option backward.isDefEq.respectTransparency false in
theorem compared_lift : {n : Nat} → {A D : B} → (a : A ⟶ D) → (z : Chain P n D) →
    (y : Y.obj (op (endpoint z))) →
    squareEquiv Y S a (pullChain a z) z (pullValue Y a z y) y (liftDecorated Y a z y) =
      eqToHom (realized_pull Y S a z y)
  | 0, _, _, _, .nil _, _ => rfl
  | n+1, A, _, a, .cons q z, y => by
    let F := Iterates.layer P S Y n
    apply extAligned F (e := P.extend A)
    · exact (gradeTransport F (e := P.extend A) (realized_pull Y S a (.cons q z) y)).eq.symm
    · apply Aligned.trans _ (payloadTransport F _).symm
      apply (alignedOfEq (compared_tail Y S (p := (P.grades.map a.op).toFunctor.obj q) (t := pullChain ((P.lift a).app q) z) (liftDecorated Y a (.cons q z) y))).trans
      apply (Aligned.trailing _ _).trans
      change Aligned (squareEquiv Y S _ _ _ _ _ (tailPart Y (liftDecorated Y a (.cons q z) y))) _
      rw [tail_lift,comparison_rebase]
      apply (Aligned.trailing _ _).trans
      apply (alignedOfEq (compared_lift ((P.lift a).app q) z y)).trans
      exact alignedTransport _

namespace Cartesian
variable {n : Nat} {A D E : B} (a : A ⟶ D) (b : D ⟶ E)
    (t : Chain P n A) (z : Chain P n E)
    (x : Y.obj (op (endpoint t))) (y : Y.obj (op (endpoint z)))

theorem postTarget :
    ((Iterates.layer P S Y n).map a.op).toFunctor.obj (realize Y S (pullChain b z) (pullValue Y b z y)) =
      ((Iterates.layer P S Y n).map (a ≫ b).op).toFunctor.obj (realize Y S z y) := by
  rw [realized_pull,op_comp,Functor.map_comp]; rfl

def postEquiv :
    DecoratedHom Y a t (pullChain b z) x (pullValue Y b z y) ≃ DecoratedHom Y (a ≫ b) t z x y :=
  (squareEquiv Y S a _ _ _ _).trans ((Equiv.cast (congrArg (fun dest => (realize Y S t x ⟶ dest))
    (postTarget Y S a b z y))).trans (squareEquiv Y S _ _ _ _ _).symm)

private theorem castAligned {C : Type*} [Category* C] {x l r : C} (j : l = r) (f : x ⟶ l) :
    Aligned (Equiv.cast (congrArg (fun dest => x ⟶ dest) j) f) f := by subst r; exact Aligned.refl _

set_option backward.isDefEq.respectTransparency false in
theorem post_evaluation (f : DecoratedHom Y a t (pullChain b z) x (pullValue Y b z y)) :
    postEquiv Y S a b t z x y f = decoratedComp S Y f (liftDecorated Y b z y) := by
  apply (squareEquiv Y S _ _ _ _ _).injective
  simp only [postEquiv,Equiv.trans_apply,Equiv.apply_symm_apply,square_comp_native]
  apply Aligned.eq
  apply (castAligned (postTarget Y S a b z y) _).trans
  apply Aligned.symm
  apply (native_reduced _ _ _).trans
  rw [compared_lift]
  conv_rhs => rw [← Category.comp_id (squareEquiv Y S a t (pullChain b z) x (pullValue Y b z y) f)]
  apply (Aligned.refl _).comp
  rw [← Functor.map_id]
  apply Aligned.map
  exact alignedTransport _

/-- Every source square over a;b factors uniquely over a through the chosen lift over b. -/
theorem unique_factor (h : DecoratedHom Y (a ≫ b) t z x y) :
    ∃! f : DecoratedHom Y a t (pullChain b z) x (pullValue Y b z y),
      decoratedComp S Y f (liftDecorated Y b z y) = h := by
  let e := postEquiv Y S a b t z x y
  refine ⟨e.symm h,?_,?_⟩
  · exact (post_evaluation Y S a b t z x y (e.symm h)).symm.trans (e.apply_symm_apply _)
  · intro f hf
    apply e.injective
    rw [e.apply_symm_apply]
    exact (post_evaluation Y S a b t z x y f).trans hf
end Cartesian
namespace Fibre
variable {Y} {n : Nat} {A D : B} (a : A ⟶ D)
def pullObj (Z : Fibre P Y n D) : Fibre P Y n A :=
  ⟨pullChain a Z.chain,pullValue Y a Z.chain Z.value⟩

def lifted (Z : Fibre P Y n D) :
    DecoratedHom Y a (pullObj a Z).chain Z.chain (pullObj a Z).value Z.value :=
  liftDecorated Y a Z.chain Z.value

/-- The map is specified on the source by the unique cartesian square, rather
than by lifting an arbitrary RHS transport through a pointwise equivalence. -/
noncomputable def pullHom {X Z : Fibre P Y n D} (f : Hom X Z) : Hom (pullObj a X) (pullObj a Z) :=
  Classical.choose (Cartesian.unique_factor Y S (𝟙 A) a (pullObj a X).chain Z.chain (pullObj a X).value Z.value
    (rebaseDecorated Y ((Category.comp_id a).trans (Category.id_comp a).symm) (decoratedComp S Y (lifted a X) f)))

theorem pullHom_square {X Z : Fibre P Y n D} (f : Hom X Z) :
    decoratedComp S Y (pullHom S a f) (lifted a Z) =
      rebaseDecorated Y ((Category.comp_id a).trans (Category.id_comp a).symm) (decoratedComp S Y (lifted a X) f) :=
  (Classical.choose_spec (Cartesian.unique_factor Y S (𝟙 A) a (pullObj a X).chain Z.chain
    (pullObj a X).value Z.value _)).1

private theorem verticalAligned {E : B} {X Z : Fibre P Y n E} (f : Hom X Z) :
    Aligned (homComparison S X Z f) (squareEquiv Y S _ _ _ _ _ f) := by
  exact Cartesian.castAligned (Functor.congr_obj (congrArg Cat.Hom.toFunctor
    ((Iterates.layer P S Y n).map_id (op E))) (obj S Z)) _

set_option backward.isDefEq.respectTransparency false in
theorem pullHom_aligned {X Z : Fibre P Y n D} (f : Hom X Z) :
    Aligned (homComparison S _ _ (pullHom S a f))
      (((Iterates.layer P S Y n).map a.op).toFunctor.map (homComparison S X Z f)) := by
  apply (verticalAligned S _).trans
  apply Aligned.trans _ ((verticalAligned S f).symm.map _)
  let g := pullHom S a f
  have e := congrArg (squareEquiv Y S (𝟙 A ≫ a) (pullObj a X).chain Z.chain (pullObj a X).value Z.value)
    (pullHom_square S a f)
  rw [comparison_rebase,square_comp_native,square_comp_native] at e
  have h := alignedOfEq e
  have hl (T : Fibre P Y n D) : Aligned
      (squareEquiv Y S a (pullObj a T).chain T.chain (pullObj a T).value T.value (lifted a T))
      (𝟙 (obj S (pullObj a T))) := (alignedOfEq (compared_lift Y S a T.chain T.value)).trans (alignedTransport _)

  apply Aligned.trans _ (Aligned.trans h _)
  · apply Aligned.symm
    apply (native_reduced _ _ _).trans
    conv_rhs => rw [← Category.comp_id (squareEquiv Y S (𝟙 A) _ _ _ _ g)]
    apply (Aligned.refl _).comp
    rw [← Functor.map_id]
    apply Aligned.map
    exact hl Z
  · apply (Aligned.trailing _ _).trans
    apply (native_reduced _ _ _).trans
    conv_rhs => rw [← Category.id_comp (((Iterates.layer P S Y n).map a.op).toFunctor.map (squareEquiv Y S (𝟙 D) X.chain Z.chain X.value Z.value f))]
    have hh := alignedOfEq (compared_lift Y S a X.chain X.value)
    apply Aligned.comp (hh.trans _) (Aligned.refl _)
    exact ⟨realized_pull Y S a X.chain X.value,rfl,by simp⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable def pullFunctor :
    asCat (Y := Y) S n D ⥤ asCat (Y := Y) S n A where
  obj X := pullObj a X
  map f := pullHom S a f
  map_id X := by
    apply (homComparison S _ _).injective
    apply Aligned.eq
    apply (pullHom_aligned S a (ident S X)).trans
    change Aligned _ (homComparison S _ _ (ident S (pullObj a X)))
    rw [ident_comparison,Functor.map_id,ident_comparison]
    have he := realized_pull Y S a X.chain X.value
    exact ⟨he.symm,he.symm,by simp⟩
  map_comp f g := by
    apply (homComparison S _ _).injective
    apply Aligned.eq
    apply (pullHom_aligned S a (paste S f g)).trans
    change Aligned _ (homComparison S _ _ (paste S (pullHom S a f) (pullHom S a g)))
    rw [paste_comparison,Functor.map_comp,paste_comparison]
    apply Aligned.comp (pullHom_aligned S a f).symm (pullHom_aligned S a g).symm
private theorem aligned_conj {C : Type*} [Category* C] {x y x' y' : C}
    {f : x ⟶ y} {g : x' ⟶ y'} (h : Aligned f g) (s : x = x') (t : y' = y) :
    f = eqToHom s ≫ g ≫ eqToHom t := by
  subst x'; subst y'; simpa using h.eq

set_option backward.isDefEq.respectTransparency false in
theorem comparison_square : pullFunctor (Y := Y) S a ⋙ comparison S n A =
    comparison S n D ⋙ ((Iterates.layer P S Y n).map a.op).toFunctor := by
  fapply Functor.ext
  · intro X; exact realized_pull Y S a X.chain X.value
  · intro X Z f
    exact aligned_conj (pullHom_aligned S a f) _ _

private theorem obj_injective (a : B) : Function.Injective (obj S (Y := Y) (n := n) (A := a)) := by
  rintro ⟨t,x⟩ ⟨z,y⟩ h
  have e := (realizedEquiv Y S n a).injective (a₁ := ⟨t,x⟩) (a₂ := ⟨z,y⟩) h
  exact congrArg (fun d => (⟨d.1,d.2⟩ : Fibre P Y n a)) e

/- Postcomposition by the comparison reflects equality of functors: it is
injective on objects (not merely essentially surjective) as well as faithful. -/
set_option backward.isDefEq.respectTransparency false in
private theorem reflect_functors {C : Type*} [Category* C] {F G : C ⥤ asCat (Y := Y) S n A}
    (h : F ⋙ comparison S n A = G ⋙ comparison S n A) : F = G := by
  fapply Functor.ext
  · intro X; exact obj_injective S A (Functor.congr_obj h X)
  · intro X Z f
    apply (comparison S n A).map_injective
    simp only [Functor.map_comp,eqToHom_map]
    exact Functor.congr_hom h f

theorem pullFunctor_id (A : B) : pullFunctor (Y := Y) (n := n) S (𝟙 A) = 𝟭 _ := by
  apply reflect_functors S
  rw [comparison_square,op_id,Functor.map_id]
  rfl

theorem pullFunctor_comp {E : B} (b : D ⟶ E) :
    pullFunctor (Y := Y) (n := n) S (a ≫ b) = pullFunctor S b ⋙ pullFunctor S a := by
  apply reflect_functors S
  rw [comparison_square,op_comp,Functor.map_comp]
  change _ = pullFunctor S b ⋙ (pullFunctor S a ⋙ comparison S n A)
  rw [comparison_square]
  change _ = (pullFunctor S b ⋙ comparison S n D) ⋙ _
  rw [comparison_square]
  rfl

noncomputable def sourcePresheaf (n : Nat) : Bᵒᵖ ⥤ Cat where
  obj A := asCat (Y := Y) S n A.unop
  map a := (pullFunctor S a.unop).toCatHom
  map_id A := congrArg Functor.toCatHom (pullFunctor_id S A.unop)
  map_comp a b := congrArg Functor.toCatHom (pullFunctor_comp S b.unop a.unop)

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


noncomputable def allPull : All (Y := Y) S D ⥤ All (Y := Y) S A :=
  Sigma.Functor.sigma fun n => pullFunctor (Y := Y) (n := n) S a

theorem allPull_id (A : B) : allPull (Y := Y) S (𝟙 A) = 𝟭 _ := by
  unfold allPull; simp only [pullFunctor_id]; exact sigma_id

theorem allPull_comp {E : B} (b : D ⟶ E) :
    allPull (Y := Y) S (a ≫ b) = allPull S b ⋙ allPull S a := by
  unfold allPull; simp only [pullFunctor_comp]; apply sigma_comp

noncomputable def allSourcePresheaf : Bᵒᵖ ⥤ Cat where
  obj A := Cat.of (All (Y := Y) S A.unop)
  map a := (allPull S a.unop).toCatHom
  map_id A := congrArg Functor.toCatHom (allPull_id S A.unop)
  map_comp a b := congrArg Functor.toCatHom (allPull_comp S b.unop a.unop)

private def sigmaBetween {C : Nat → Type*} {D : Nat → Type*} [∀ n, Category* (C n)] [∀ n, Category* (D n)]
    (F : ∀ n, C n ⥤ D n) : (Σ n, C n) ⥤ Σ n, D n := Sigma.desc fun n => F n ⋙ Sigma.incl n

private theorem sigmaBetween_comp {C : Nat → Type*} {D : Nat → Type*} {E : Nat → Type*}
    [∀ n, Category* (C n)] [∀ n, Category* (D n)] [∀ n, Category* (E n)]
    (F : ∀ n, C n ⥤ D n) (G : ∀ n, D n ⥤ E n) :
    sigmaBetween (fun n => F n ⋙ G n) = sigmaBetween F ⋙ sigmaBetween G := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; rfl
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]
    exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
theorem allComparison_square :
    allPull (Y := Y) S a ⋙ allComparison S A =
      allComparison S D ⋙ Iterates.packedMap P S Y a.op := by
  change sigmaBetween (fun n => pullFunctor (n := n) S a) ⋙ sigmaBetween (fun n => comparison S n A) =
    sigmaBetween (fun n => comparison S n D) ⋙ sigmaBetween (fun n => ((Iterates.layer P S Y n).map a.op).toFunctor)
  rw [← sigmaBetween_comp,← sigmaBetween_comp]
  exact congrArg sigmaBetween (funext fun n => comparison_square (Y := Y) (n := n) S a)
end Fibre
end ContextualComposition.GrothendieckStep.TelescopeSquares
