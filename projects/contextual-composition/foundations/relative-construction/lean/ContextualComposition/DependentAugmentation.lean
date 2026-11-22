module

public import ContextualComposition.NativePartition

@[expose] public section

/-! Right tensor unitor and additive distribution: actual native augmentation
comparisons, including arbitrary maps from source zero. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {T S : Bi K} {Z U : C}
variable {G : Gather S T Z} (L : LeftGather S T Z)
/-- Local unitor/distributor diagrams. Only binary and nullary structure
appear in these premises, not arbitrary native aggregates or finite sums. -/
structure UnitCompat (G : Gather S T Z) (U : C) where
  ρ (a : C) : K.Hom (T.obj a U) a
  natural {a b : C} (p : K.Hom a b) : K.seq (T.map p (K.id U)) (ρ b) = K.seq (ρ a) p
  nil : K.seq (G.nil U) (ρ Z) = K.id Z
  cons (a b : C) : K.seq (G.cons a b U) (ρ (S.obj a b)) = S.map (ρ a) (ρ b)
variable (R : UnitCompat G U)
theorem gather_unit {X : Type w} (V : X → C) (xs : List X) :
    K.seq (gather G V U xs) (R.ρ _) = act S Z (fun x => R.ρ (V x)) xs := by
  induction xs with
  | nil => exact R.nil
  | cons x xs ih =>
    simp only [gather, act, fold, K.assoc, R.cons, ← S.map_seq, K.id_seq, ih]
variable {X : Type w} (V : X → C) (J : Input X C)
def augmentation (xs : List X) (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U)
    (ε : K.Hom (fold S Z V xs) U) :
    K.Hom (fold S Z (rowSource (S:=S) (T:=T) (Z:=Z) V J) xs) U :=
  K.seq (act S Z (fun x => K.seq (row V J L δ x) (R.ρ (V x))) xs) ε
/-- Normalization to the paper's continuation-before-global-augmentation
form; no family of component augmentations of the outer resource is used. -/
theorem augmentation_normal (xs : List X) (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U)
    (ε : K.Hom (fold S Z V xs) U) :
    K.seq (dep G V J L xs δ ε) (R.ρ U) = augmentation L R V J xs δ ε := by
  simp only [dep, augmentation, K.assoc, R.natural]
  rw [← K.assoc (gather _ _ _ _), gather_unit, ← K.assoc, act_seq]
/-- A single final outer merge with any number of source parents and
arbitrary actual continuation maps into the final common continuation.
Includes the globally empty source and empty inner sums. -/
theorem collapse_preserves {a b : C} (xs : List X)
    (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b) (α : K.Hom (fold S Z V xs) a)
    (ε' : K.Hom a U) (δ' : K.Hom b U)
    (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U) (ε : K.Hom (fold S Z V xs) U)
    (hβ : ∀ x, K.seq (β x) δ' = δ x) (hα : K.seq α ε' = ε) :
    K.seq (dep G V J L xs β α) (K.seq (T.map ε' δ') (R.ρ U)) =
      augmentation L R V J xs δ ε := by
  rw [← K.assoc, post, hα]
  simpa only [hβ] using augmentation_normal L R V J xs (fun x => K.seq (β x) δ') ε

theorem fibre_augmentation {a b : C} (xs : List X)
    (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b) (α : K.Hom (fold S Z V xs) a)
    (δ' : K.Hom b U) :
    K.seq (dep G V J L xs β α) (K.seq (T.map (K.id a) δ') (R.ρ a)) =
    K.seq (act S Z (fun x => K.seq (row V J L (fun i => K.seq (β i) δ') x) (R.ρ (V x))) xs) α := by
  rw [← K.assoc, post, K.seq_id]
  simp only [dep, K.assoc, R.natural]
  rw [← K.assoc (gather _ _ _ _), gather_unit, ← K.assoc, act_seq]

/-- Global augmentation on the prepartitioned outer domain. The coefficient
b at a target j is the whole target continuation sum. There is exactly one
outer epsilon, never one augmentation per target j. The comparison from the
unpartitioned extension to this domain is a separate structural obligation. -/
theorem grouped_augmentation {I : Type w} (ds : I → Fibre (S:=S) (Z:=Z))
    (js : List I) (δ' : ∀ j, K.Hom (ds j).b U)
    (ε' : K.Hom (fold S Z (fun j => (ds j).a) js) U)
    (ε : K.Hom (fold S Z (fun j => fold S Z (ds j).V (ds j).xs) js) U)
    (outer : K.seq (act S Z (fun j => (ds j).α) js) ε' = ε) :
    K.seq (act S Z (fun j => dep G (ds j).V (ds j).J L (ds j).xs (ds j).β (ds j).α) js)
      (K.seq (act S Z (fun j => K.seq (T.map (K.id (ds j).a) (δ' j)) (R.ρ (ds j).a)) js) ε') =
    K.seq (act S Z (fun j => act S Z
      (fun x => K.seq (row (ds j).V (ds j).J L (fun i => K.seq ((ds j).β i) (δ' j)) x)
        (R.ρ ((ds j).V x))) (ds j).xs) js) ε := by
  rw [← K.assoc, act_seq]
  simp only [fibre_augmentation]
  rw [← act_seq, K.assoc, outer]
end ContextualComposition.NativeFinitePush.DependentFibre
