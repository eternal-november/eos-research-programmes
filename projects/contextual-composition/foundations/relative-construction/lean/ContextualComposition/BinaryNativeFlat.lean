module
public import ContextualComposition.FourLevelRoutes
@[expose] public section
/-! Equality of the actual binary coefficient composites on the chosen
flat addressed source, independently of chart-based normalization. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary Binary.ofMonoidal
variable {T : Bi (coeff (C:=C))}
variable (R : Gather 𝒮 T (𝟙_ C)) (L : LeftGather 𝒮 T (𝟙_ C))
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {X Y : Type u} (xs : List X) (ys : List Y)
variable (V : X → C) (W : Y → C) (J : Input X C) (P : Input Y C)
variable {a b c d : C}
variable (β : ∀ x, inner (S:=𝒮) (Z:=𝟙_ C) J x ⟶ b)
variable (θ : ∀ y, inner (S:=𝒮) (Z:=𝟙_ C) P y ⟶ d)
variable (α : fold 𝒮 (𝟙_ C) V xs ⟶ a) (γ : fold 𝒮 (𝟙_ C) W ys ⟶ c)
variable {I : C} (m : Middle T I)
local notation "Av" => (fun x => T.obj (V x))
local notation "Bv" => (fun y => T.obj (W y))
/-- On the occurrence-first chart, the actual coefficient arrow is the
independent distributor, tensor of two dependent cells, then the target
shuffle. All four structural and aggregation factors are observable. -/
def occurrenceMap :=
  occurrenceFirst R L Av Bv xs ys J.terms P.terms ≫
    T.map (dep R V J L xs β α) (dep R W P L ys θ γ) ≫ m.cell a b c d
include N NR NL in
/-- Binary fixed-target coefficient equality from the common flat word.
The two entry charts are grouped independently; the flat structural
route is the canonical block-transpose program, not an arbitrary
other program with the same alleged permutation. -/
theorem native_binary_flat (H : MedialLinear m R L) (Q : MedialInner m R L) :
    compressTree (quadLabels (T:=T) Av Bv) (fourOccurrenceExpr xs ys J.terms P.terms) ≫
      transportSource (K:=coeff (C:=C)) (occurrence_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys J.terms P.terms)
        (occurrenceMap R L xs ys V W J P β θ α γ m) =
    flatCircuit (quadLabels (T:=T) Av Bv) (fourExchangeChart xs ys J.terms P.terms) (𝟙_ C) ≫
      compressTree (quadLabels (T:=T) Av Bv) (fourJointExpr xs ys J.terms P.terms) ≫
      transportSource (K:=coeff (C:=C)) (joint_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys J.terms P.terms)
        (jointNative R L xs ys V W J P β θ α γ m) := by
  rw [← Category.assoc (flatCircuit _ _ _), independent_std_charts, Category.assoc]
  have h := transport_paste
    (occurrence_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys J.terms P.terms)
    (joint_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys J.terms P.terms)
    (fourExchangeChart_eval (symmetricCross (C:=C)) (T:=T) Av Bv xs ys J.terms P.terms)
    (jointNative R L xs ys V W J P β θ α γ m)
  unfold occurrenceMap
  have k := binary_native_routes (symmetricCross (C:=C)) R L N xs ys NR NL V W J P β θ α γ m H Q
  let C₀ := compressTree (quadLabels (T:=T) Av Bv) (fourOccurrenceExpr xs ys J.terms P.terms)
  calc
    _ = C₀ ≫ transportSource (K:=coeff (C:=C)) (occurrence_expr_obj Av Bv xs ys J.terms P.terms)
      (exchangeInner (T:=T) (symmetricCross (C:=C)) Av Bv xs ys J.terms P.terms ≫ jointNative R L xs ys V W J P β θ α γ m) :=
      congrArg (fun f => C₀ ≫ transportSource (K:=coeff (C:=C)) _ f) k
    _ = _ := congrArg (fun f => C₀ ≫ f) h.symm
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
