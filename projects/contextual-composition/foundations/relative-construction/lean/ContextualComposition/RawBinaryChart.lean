module
public import ContextualComposition.BinaryNativeFlat
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u
namespace GridExpr
variable {I J X : Type u}
def reindex (f : I → J) : GridExpr I → GridExpr J
  | .zero => .zero
  | .leaf i => .leaf (f i)
  | .bin a b => .bin (a.reindex f) (b.reindex f)
theorem over_map {Y : Type u} (f : X → Y) (A : Y → GridExpr I) (xs : List X) :
    over A (xs.map f) = over (fun x => A (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, over, ih]
theorem reindex_over (f : I → J) (A : X → GridExpr I) (xs : List X) :
    (over A xs).reindex f = over (fun x => (A x).reindex f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [over, reindex, ih]
theorem leaves_reindex (f : I → J) (e : GridExpr I) :
    (e.reindex f).leaves = e.leaves.map f := by
  induction e with
  | zero => rfl
  | leaf => rfl
  | bin a b ha hb => simp only [reindex,leaves,List.map_append,ha,hb]
end GridExpr
namespace GridCircuit
variable {I J : Type u}
def reindex (f : I → J) {e g} : GridCircuit I e g → GridCircuit J (e.reindex f) (g.reindex f)
  | .ident e => .ident _
  | .seq p q => .seq (reindex f p) (reindex f q)
  | .bin p q => .bin (reindex f p) (reindex f q)
  | .dupZero => .dupZero
  | .mergeZero => .mergeZero
  | .middle a b c d => .middle _ _ _ _
end GridCircuit

variable {C X U Y W : Type u}
variable (A : X → U → C) (B : Y → W → C)
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
def forgetLabels (p : X × U × Y × W) : X × C × Y × C :=
  (p.1,A p.1 p.2.1,p.2.2.1,B p.2.2.1 p.2.2.2)
theorem branch_reindex (x : X) (u : U) (y : Y) :
    (innerQuad vs x y u).reindex (forgetLabels A B) =
      innerQuad (fun y => (vs y).map (B y)) x y (A x u) := by
  unfold innerQuad
  rw [GridExpr.reindex_over]
  change _ = GridExpr.over _ ((vs y).map (B y))
  rw [GridExpr.over_map]
  rfl
theorem occurrence_reindex :
    (fourOccurrenceExpr xs ys us vs).reindex (forgetLabels A B) =
      fourOccurrenceExpr xs ys (fun x => (us x).map (A x)) (fun y => (vs y).map (B y)) := by
  unfold fourOccurrenceExpr
  rw [GridExpr.reindex_over]
  congr 1
  funext x
  rw [GridExpr.reindex_over]
  change _ = GridExpr.over _ ((us x).map (A x))
  rw [GridExpr.over_map]
  congr 1
  funext u
  rw [GridExpr.reindex_over]
  congr 1
  funext y
  exact branch_reindex A B vs x u y
theorem joint_reindex :
    (fourJointExpr xs ys us vs).reindex (forgetLabels A B) =
      fourJointExpr xs ys (fun x => (us x).map (A x)) (fun y => (vs y).map (B y)) := by
  unfold fourJointExpr
  rw [GridExpr.reindex_over]
  congr 1
  funext x
  rw [GridExpr.reindex_over]
  congr 1
  funext y
  rw [GridExpr.reindex_over]
  change _ = GridExpr.over _ ((us x).map (A x))
  rw [GridExpr.over_map]
  congr 1
  funext u
  exact branch_reindex A B vs x u y
end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary Binary.ofMonoidal
variable {T : Bi (coeff (C:=C))}
variable {X U Y W : Type u} (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (V : X → C) (Wv : Y → C) (A : X → U → C) (B : Y → W → C)
def indexInput (A : X → U → C) (us : X → List U) : Input X C := ⟨fun x => (us x).map (A x)⟩
local notation "LA" => fun x u => T.obj (V x) (A x u)
local notation "LB" => fun y v => T.obj (Wv y) (B y v)
local notation "Av" => fun x => T.obj (V x)
local notation "Bv" => fun y => T.obj (Wv y)

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem raw_word :
    word (quadLabels (T:=T) LA LB) (fourOccurrenceExpr xs ys us vs) =
    word (quadLabels (T:=T) Av Bv) (fourOccurrenceExpr xs ys ((indexInput A us)).terms ((indexInput B vs)).terms) := by
  simp only [indexInput]
  unfold word
  rw [← occurrence_reindex A B xs ys us vs, GridExpr.leaves_reindex, List.map_map]
  rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem raw_joint_word :
    word (quadLabels (T:=T) LA LB) (fourJointExpr xs ys us vs) =
    word (quadLabels (T:=T) Av Bv) (fourJointExpr xs ys ((indexInput A us)).terms ((indexInput B vs)).terms) := by
  simp only [indexInput]
  unfold word
  rw [← joint_reindex A B xs ys us vs, GridExpr.leaves_reindex, List.map_map]
  rfl

variable (R : Gather 𝒮 T (𝟙_ C)) (L : LeftGather 𝒮 T (𝟙_ C))
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {a b c d : C}
variable (β : ∀ x : X, inner (S:=𝒮) (Z:=𝟙_ C) (indexInput A us) x ⟶ b)
variable (θ : ∀ y : Y, inner (S:=𝒮) (Z:=𝟙_ C) (indexInput B vs) y ⟶ d)
variable (α : fold 𝒮 (𝟙_ C) V xs ⟶ a) (γ : fold 𝒮 (𝟙_ C) Wv ys ⟶ c)
variable {I : C} (m : Middle T I)

def rawEntry :=
  eqToHom (congrArg (fun l => tailFold l (𝟙_ C)) (raw_word (T:=T) xs ys us vs V Wv A B))
noncomputable def rawSeparate :=
  compressTree (quadLabels (T:=T) Av Bv) (fourOccurrenceExpr xs ys ((indexInput A us)).terms ((indexInput B vs)).terms) ≫
    transportSource (K:=coeff (C:=C))
      (occurrence_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys ((indexInput A us)).terms ((indexInput B vs)).terms)
      (occurrenceMap R L xs ys V Wv (indexInput A us) (indexInput B vs) β θ α γ m)
noncomputable def rawJoint :=
  flatCircuit (quadLabels (T:=T) Av Bv) (fourExchangeChart xs ys ((indexInput A us)).terms ((indexInput B vs)).terms) (𝟙_ C) ≫
    compressTree (quadLabels (T:=T) Av Bv) (fourJointExpr xs ys ((indexInput A us)).terms ((indexInput B vs)).terms) ≫
    transportSource (K:=coeff (C:=C))
      (joint_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys ((indexInput A us)).terms ((indexInput B vs)).terms)
      (jointNative R L xs ys V Wv (indexInput A us) (indexInput B vs) β θ α γ m)

include N NR NL in
/-- Fixed-target coefficient equality from the literal raw address list.
The raw entry uses only exact transport of the coefficient word, with
order and multiplicity unchanged. -/
theorem raw_native_binary_flat (H : MedialLinear m R L) (Q : MedialInner m R L) :
    rawEntry (T:=T) xs ys us vs V Wv A B ≫ rawSeparate xs ys us vs V Wv A B R L β θ α γ m =
    rawEntry (T:=T) xs ys us vs V Wv A B ≫ rawJoint xs ys us vs V Wv A B R L β θ α γ m := by
  exact congrArg (fun g => rawEntry (T:=T) xs ys us vs V Wv A B ≫ g)
    (native_binary_flat R L N NR NL xs ys V Wv (indexInput A us) (indexInput B vs) β θ α γ m H Q)
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
