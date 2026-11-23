module
public import ContextualComposition.NativeIndependentAugFold
@[expose] public section

/-! The independently defined product of two dependent input maps:
the parent and each continuation are literal rectangular products. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

theorem mem_ordered_product {X Y : Type u} (xs : List X) (ys : List Y) (p : X × Y) :
    p ∈ xs.product ys ↔ p.1 ∈ xs ∧ p.2 ∈ ys := by
  rcases p with ⟨x,y⟩
  change (x,y) ∈ xs.flatMap (fun x => ys.map (fun y => (x,y))) ↔ _
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,rfl,rfl⟩
    exact ⟨ha,hb⟩
  · rintro ⟨hx,hy⟩
    exact ⟨x,hx,y,hy,rfl,rfl⟩

variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

def crossLabel {X Y : Type u} (T : Bi (coeff (C:=C))) (V : X → C) (P : Y → C) :
    X × Y → C :=
  fun x => T.obj (V x.1) (P x.2)

def crossChildLabel {X U Y W : Type u} (T : Bi (coeff (C:=C))) (A : X → U → C) (B : Y → W → C) :
    X × Y → U × W → C :=
  fun x => crossLabel T (A x.1) (B x.2)

def crossChildWord {X U Y W : Type u} (us : X → List U) (vs : Y → List W) :
    X × Y → List (U × W) :=
  fun x => (us x.1).product (vs x.2)

set_option backward.isDefEq.respectTransparency false in
def rectangularWordCell {X Y X' Y' : Type u} [DecidableEq X'] [DecidableEq Y']
    (xs : List X) (ys : List Y) (f : X → X') (g : Y → Y') (t : X' × Y')
    (V : X → C) (P : Y → C) {a b : C}
    (p : fold 𝒮 Zₐ V (wordFibre xs f t.1) ⟶ a) (q : fold 𝒮 Zₐ P (wordFibre ys g t.2) ⟶ b) :
    fold 𝒮 Zₐ (crossLabel T V P) (wordFibre (xs.product ys) (Prod.map f g) t) ⟶ T.obj a b :=
  eqToHom (congrArg (fold 𝒮 Zₐ (crossLabel T V P)) (product_word_fibre xs ys f g t)) ≫
    rectWordChart (crossLabel T V P) (wordFibre xs f t.1) (wordFibre ys g t.2) ≫
    independentCell R L V P (wordFibre xs f t.1) (wordFibre ys g t.2) p q

set_option backward.isDefEq.respectTransparency false in
def OrderedDependentMap.independentProduct :
    OrderedDependentMap (xs.product ys) (crossChildWord us vs)
      (xs'.product ys') (crossChildWord us' vs')
      (crossLabel T V P) (crossChildLabel T A B) (crossLabel T V' P') (crossChildLabel T A' B') where
  parent := Prod.map D.parent E.parent
  child x := Prod.map (D.child x.1) (E.child x.2)
  parent_mem x hx := by
    have hh := (mem_ordered_product xs ys x).mp hx
    exact (mem_ordered_product xs' ys' _).mpr
      ⟨D.parent_mem _ hh.1,E.parent_mem _ hh.2⟩
  child_mem x hx k hk := by
    have hh := (mem_ordered_product xs ys x).mp hx
    have kk := (mem_ordered_product (us x.1) (vs x.2) k).mp hk
    exact (mem_ordered_product (us' (D.parent x.1)) (vs' (E.parent x.2)) _).mpr
      ⟨D.child_mem _ hh.1 _ kk.1,E.child_mem _ hh.2 _ kk.2⟩
  outer t ht := by
    have h := (mem_ordered_product xs' ys' t).mp ht
    exact rectangularWordCell R L xs ys D.parent E.parent t V P (D.outer t.1 h.1) (E.outer t.2 h.2)
  inner x hx t ht := by
    have h := (mem_ordered_product xs ys x).mp hx
    have m := (mem_ordered_product (us' (D.parent x.1)) (vs' (E.parent x.2)) t).mp ht
    exact rectangularWordCell R L (us x.1) (vs x.2) (D.child x.1) (E.child x.2) t (A x.1) (B x.2)
      (D.inner x.1 h.1 t.1 m.1) (E.inner x.2 h.2 t.2 m.2)

def jointPairRetag {X U Y W : Type u} : ((X × Y) × (U × W)) ≃ (X × U × Y × W) where
  toFun t := (t.1.1,t.2.1,t.1.2,t.2.2)
  invFun t := ((t.1,t.2.2.1),(t.2.1,t.2.2.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem jointPairRetag_word {X U Y W : Type u}
    (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W) :
    (dependentWord (xs.product ys) (crossChildWord us vs)).map jointPairRetag =
      (fourJointExpr xs ys us vs).leaves := by
  rw [leaves_fourJoint]
  unfold dependentWord crossChildWord List.product
  simp only [List.map_flatMap, List.flatMap_assoc, List.flatMap_map, List.map_map]
  rfl

theorem independentProduct_carrier (t : (X × Y) × (U × W)) :
    jointPairRetag (origDepCarrier (D.independentProduct E R L) t) =
      quadCarrierMap D.parent D.child E.parent E.child (jointPairRetag t) := rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
