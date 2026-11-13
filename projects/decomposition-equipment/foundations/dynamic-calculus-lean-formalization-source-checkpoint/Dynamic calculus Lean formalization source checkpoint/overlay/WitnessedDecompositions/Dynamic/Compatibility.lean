module

public import WitnessedDecompositions.Dynamic.Graph
public import WitnessedDecompositions.Dynamic.Occurrences

/-! Fine boundary compatibility under arbitrary original occurrence substitution. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u v w
namespace WitnessedDecompositions.Dynamic.Assignment
open Path
variable {V : Type u} [Quiver.{v} V]

/-- Glue compatible families at their actual common boundary map. -/
theorem compatible_comp (D : Assignment.{u, v, w} V) {X : Graph.{w}}
    {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (f : D.Family X (p.comp q))
    (h : Graph.Hom X (D.boundary a)) (m : Graph.Hom X (D.boundary b))
    (k : Graph.Hom X (D.boundary c))
    (hp : D.Compatible X p (compLeftFamily (fun d => Graph.Hom X (D.component d)) p q f) h m)
    (hq : D.Compatible X q (compRightFamily (fun d => Graph.Hom X (D.component d)) p q f) m k) :
    D.Compatible X (p.comp q) f h k := by
  induction q with
  | nil =>
      change m = k at hq
      cases hq
      exact hp
  | cons q e ih =>
      exact ⟨ih (fun i => f (.inl i)) ((f (.inr ())).comp (D.left _)) hp hq.1,
        hq.2⟩

/-- Expansion preserves compatibility whenever each inserted occurrence does.
Empty inserted profiles contribute equality of the two exposed boundary maps. -/
theorem compatible_expand (D : Assignment.{u, v, w} V) {X : Graph.{w}}
    {a b : V} (p : Quiver.Path a b) (f : D.Family X p)
    (h : Graph.Hom X (D.boundary a)) (k : Graph.Hom X (D.boundary b))
    (hp : D.Compatible X p f h k)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (g : D.Family X (expand p q))
    (hq : ∀ i, D.Compatible X (q i)
      (expandFamily (fun d => Graph.Hom X (D.component d)) p q g i)
      ((f i).comp (D.left _)) ((f i).comp (D.right _))) :
    D.Compatible X (expand p q) g h k := by
  induction p with
  | nil => exact hp
  | cons p e ih =>
      apply D.compatible_comp (expand p (fun i => q (.inl i))) (q (.inr ())) g h
        ((f (.inr ())).comp (D.left _)) k
      · apply ih (fun i => f (.inl i)) ((f (.inr ())).comp (D.left _)) hp.1
          (fun i => q (.inl i))
        intro i
        have hi := hq (.inl i)
        have he : expandFamily (fun d => Graph.Hom X (D.component d)) (p.cons e) q g (.inl i) =
            expandFamily (fun d => Graph.Hom X (D.component d)) p (fun i => q (.inl i))
              (compLeftFamily (fun d => Graph.Hom X (D.component d))
                (expand p (fun i => q (.inl i))) (q (.inr ())) g) i := by
          funext j
          exact expandFamily_cons_inl (fun d => Graph.Hom X (D.component d)) p e q g i j
        rw [he] at hi
        exact hi
      · have hi := hq (.inr ())
        rw [hp.2] at hi
        exact hi

/-- Literal coordinate-map composition is closed under all occurrence-wise
substitutions, without excluding any empty outer or inner profile. -/
theorem compatible_joinFamily (D : Assignment.{u, v, w} V) {X : Graph.{w}}
    {a b : V} (p : Quiver.Path a b) (f : D.Family X p)
    (h : Graph.Hom X (D.boundary a)) (k : Graph.Hom X (D.boundary b))
    (hp : D.Compatible X p f h k)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (g : ∀ i : Slot p, D.Family (D.component (componentAt p i)) (q i))
    (hg : ∀ i, D.Compatible (D.component (componentAt p i)) (q i) (g i)
      (D.left _) (D.right _)) :
    D.Compatible X (expand p q)
      (joinFamily (fun d => Graph.Hom X (D.component d)) p q
        (fun i j => (f i).comp (g i j))) h k := by
  apply D.compatible_expand p f h k hp q
  intro i
  have hc := D.compatible_precomp (q i) (g i) (D.left _) (D.right _) (hg i) (f i)
  have he : expandFamily (fun d => Graph.Hom X (D.component d)) p q
      (joinFamily (fun d => Graph.Hom X (D.component d)) p q
        (fun i j => (f i).comp (g i j))) i = (fun j => (f i).comp (g i j)) := by
    funext j
    exact expandFamily_joinFamily _ p q _ i j
  rw [he]
  exact hc

end WitnessedDecompositions.Dynamic.Assignment
