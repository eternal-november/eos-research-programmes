module

public import ContextualComposition.FiniteProbabilityLaws
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-! Finite positive history experiments and their canonical support samplers.
The fixed-endpoint law category is discrete; arrows in the experiments
retain the actual law-preserving map on each witness fibre. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.PositiveHistoryReflection
open CategoryTheory FiniteProbabilityLaws
universe u
variable {A B C D : Type u}

abbrev Supported (p : Law B) := {b // b ∈ p.mass.support}

def supportLaw (p : Law B) : Law (Supported p) := by
  classical
  apply ofFinite (fun b => p.mass b.val) (fun b => point_nonneg p b.val)
  exact (Finset.sum_attach _ (fun b => p.mass b)).trans p.normalized

theorem support_weight (p : Law B) (b : Supported p) : (supportLaw p).mass b = p.mass b.val := rfl

theorem image_supportLaw (p : Law B) : image Subtype.val (supportLaw p) = p := by
  classical
  ext b
  change (supportLaw p).mass.mapDomain Subtype.val b = _
  by_cases h : b ∈ p.mass.support
  · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective (supportLaw p).mass ⟨b,h⟩).trans (support_weight p _)
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨⟨_,ha⟩,rfl⟩; exact h ha), Finsupp.notMem_support_iff.mp h]

theorem image_positive (p : Law B) (f : B → C) (b : B) (pos : 0 < p.mass b) :
    0 < (image f p).mass (f b) := by
  classical
  change 0 < p.mass.mapDomain f (f b)
  rw [Finsupp.mapDomain_apply_eq_sum]
  exact pos.trans_le (Finset.single_le_sum (fun i _ => point_nonneg p i)
    (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr pos.ne',rfl⟩))

theorem injective_image {f : B → C} (hf : Function.Injective f) : Function.Injective (image f) := by
  intro p q e
  ext b
  have eq := congrArg (fun r : Law C => r.mass (f b)) e
  simpa only [image,Finsupp.mapDomain_apply_of_injective hf] using eq

structure History (A B : Type u) where
  witness : A → Type u
  finite : ∀ a, Finite (witness a)
  weights : ∀ a, Law (witness a)
  output : ∀ a, witness a → B

def kernel (P : History A B) (a : A) : Law B := image (P.output a) (P.weights a)
def FullSupport (P : History A B) := ∀ a x, 0 < (P.weights a).mass x

structure Map (P Q : History A B) where
  run : ∀ a, P.witness a → Q.witness a
  preserves : ∀ a, image (run a) (P.weights a) = Q.weights a
  output : ∀ a x, Q.output a (run a x) = P.output a x

@[ext] theorem Map.ext {P Q : History A B} {r s : Map P Q} (eq : r.run = s.run) : r = s := by
  cases r; cases s; cases eq; rfl

def idMap (P : History A B) : Map P P := ⟨fun _ => id,fun a => image_id (P.weights a),fun _ _ => rfl⟩

def compMap {P Q R : History A B} (f : Map P Q) (g : Map Q R) : Map P R :=
  ⟨fun a => g.run a ∘ f.run a,fun a => (image_comp _ _ _).symm.trans
    ((congrArg (image (g.run a)) (f.preserves a)).trans (g.preserves a)),
    fun a x => (g.output a _).trans (f.output a x)⟩

instance : Category (History A B) where
  Hom := Map
  id := idMap
  comp := compMap
  id_comp _ := Map.ext rfl
  comp_id _ := Map.ext rfl
  assoc _ _ _ := Map.ext rfl

theorem map_kernel {P Q : History A B} (f : Map P Q) : kernel P = kernel Q := by
  funext a
  change image (P.output a) _ = image (Q.output a) _
  rw [← f.preserves a,image_comp]
  exact congrArg (fun g => image g (P.weights a)) (funext fun x => (f.output a x).symm)

/-- Varying-endpoint history squares keep the supplied map on raw
witnesses and the deterministic output square. -/
structure Endpoint {A' B' : Type u} (P : History A B) (Q : History A' B') (u : A → A') (v : B → B') where
  run : ∀ a, P.witness a → Q.witness (u a)
  preserves : ∀ a, image (run a) (P.weights a) = Q.weights (u a)
  output : ∀ a x, Q.output (u a) (run a x) = v (P.output a x)

@[ext] theorem Endpoint.ext {A' B' : Type u} {P : History A B} {Q : History A' B'} {u : A → A'} {v : B → B'}
    {s t : Endpoint P Q u v} (h : s.run = t.run) : s = t := by cases s; cases t; cases h; rfl

theorem endpoint_kernel {A' B' : Type u} {P : History A B} {Q : History A' B'} {u : A → A'} {v : B → B'}
    (s : Endpoint P Q u v) (a : A) : image v (kernel P a) = kernel Q (u a) := by
  change image v (image _ _) = image _ _
  rw [image_comp,← s.preserves a,image_comp]
  exact congrArg (fun k => image k (P.weights a)) (funext fun w => (s.output a w).symm)

structure Positive (A B : Type u) where
  history : History A B
  positive : FullSupport history

instance : Category (Positive A B) where
  Hom P Q := Map P.history Q.history
  id P := idMap P.history
  comp := compMap
  id_comp _ := Map.ext rfl
  comp_id _ := Map.ext rfl
  assoc _ _ _ := Map.ext rfl

def support (k : A → Law B) : Positive A B where
  history := ⟨fun a => Supported (k a),fun _ => inferInstance,fun a => supportLaw (k a),fun _ => Subtype.val⟩
  positive a x := lt_of_le_of_ne (point_nonneg (k a) x.val) (Finsupp.mem_support_iff.mp x.property).symm

theorem kernel_support (k : A → Law B) : kernel (support k).history = k := funext fun a => image_supportLaw (k a)

def toSupport (P : Positive A B) (k : A → Law B) (h : kernel P.history = k) : P ⟶ support k := by
  subst k
  let f (a : A) (x : P.history.witness a) : Supported (kernel P.history a) :=
    ⟨P.history.output a x,Finsupp.mem_support_iff.mpr (image_positive _ _ x (P.positive a x)).ne'⟩
  refine ⟨f,?_,fun _ _ => rfl⟩
  intro a
  apply injective_image (f := Subtype.val) Subtype.val_injective
  exact (image_comp _ _ _).trans (image_supportLaw _).symm

theorem unique_to_support (P : Positive A B) (k : A → Law B) (f g : P ⟶ support k) : f = g := by
  apply Map.ext; funext a x
  apply Subtype.ext
  exact (f.output a x).trans (g.output a x).symm

def toSupportEndpoint {A' B' : Type u} (P : Positive A B) (k : A' → Law B') (u : A → A') (v : B → B')
    (h : ∀ a, image v (kernel P.history a) = k (u a)) : Endpoint P.history (support k).history u v := by
  let f (a : A) (w : P.history.witness a) : Supported (k (u a)) :=
    ⟨v (P.history.output a w),by
      rw [← h a]
      exact Finsupp.mem_support_iff.mpr (image_positive _ v _ (image_positive _ _ _ (P.positive a w))).ne'⟩
  refine ⟨f,?_,fun _ _ => rfl⟩
  intro a
  apply injective_image (f := Subtype.val) Subtype.val_injective
  exact (image_comp (P.history.weights a) (f a) Subtype.val).trans
    ((image_comp (P.history.weights a) (P.history.output a) v).symm.trans ((h a).trans (image_supportLaw _).symm))

def endpointEquiv {A' B' : Type u} (P : Positive A B) (k : A' → Law B') (u : A → A') (v : B → B') :
    (∀ a, image v (kernel P.history a) = k (u a)) ≃ Endpoint P.history (support k).history u v where
  toFun := toSupportEndpoint P k u v
  invFun t a := (endpoint_kernel t a).trans (congrFun (kernel_support k) (u a))
  left_inv _ := rfl
  right_inv t := by
    have eq (f g : Endpoint P.history (support k).history u v) : f.run = g.run := by
      funext a x
      exact Subtype.ext ((f.output a x).trans (g.output a x).symm)
    exact Endpoint.ext (eq _ t)

def evaluate : Positive A B ⥤ Discrete (A → Law B) where
  obj P := ⟨kernel P.history⟩
  map f := Discrete.eqToHom (map_kernel f)

def sampler : Discrete (A → Law B) ⥤ Positive A B where
  obj k := support k.as
  map {k l} f := toSupport _ l.as ((kernel_support k.as).trans (Discrete.eq_of_hom f))
  map_id _ := unique_to_support _ _ _ _
  map_comp _ _ := unique_to_support _ _ _ _

def homEquiv (P : Positive A B) (k : Discrete (A → Law B)) :
    (evaluate.obj P ⟶ k) ≃ (P ⟶ sampler.obj k) where
  toFun e := toSupport P k.as (Discrete.eq_of_hom e)
  invFun f := Discrete.eqToHom ((map_kernel f).trans (kernel_support _))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := unique_to_support _ _ _ _

def reflection : (evaluate (A := A) (B := B)) ⊣ sampler :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => unique_to_support _ _ _ _ }

instance : (sampler (A := A) (B := B)).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance : (sampler (A := A) (B := B)).Full where
  map_surjective {k l} f := ⟨Discrete.eqToHom ((kernel_support k.as).symm.trans ((map_kernel f).trans (kernel_support l.as))),
    unique_to_support _ _ _ _⟩

/-- A two-legged zigzag through a common positive experiment suffices. -/
theorem same_law_iff_cospan (P Q : Positive A B) :
    kernel P.history = kernel Q.history ↔ ∃ R : Positive A B, Nonempty (P ⟶ R) ∧ Nonempty (Q ⟶ R) := by
  constructor
  · intro h; exact ⟨support _,⟨toSupport P _ h⟩,⟨toSupport Q _ rfl⟩⟩
  · rintro ⟨R,⟨f⟩,⟨g⟩⟩; exact (map_kernel f).trans (map_kernel g).symm

end ContextualComposition.PositiveHistoryReflection
