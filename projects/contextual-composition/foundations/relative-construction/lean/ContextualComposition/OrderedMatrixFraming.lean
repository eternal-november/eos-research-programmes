module
public import ContextualComposition.ConstantCollectionFraming
public import ContextualComposition.AugmentedMatrixFubini

/-! All four crossing modifications under Set framing in the finite
matrix-coefficient specialization. The native arrows include possibly
noninvertible blocks, with augmentation on every whole source column. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.OrderedMatrixFraming
open CategoryTheory OrderedArityReflection ConstantCollectionFraming AugmentedMatrixFubini
open scoped BigOperators
universe u v
variable (R : Type v) [CommSemiring R] {B X : Type u} {C D : Collection.{u}}

def unary (A : Family.{0,v} R) : Wiring (occurrence (fun _ : Fin 1 => A)) A where
  pos := Equiv.piUnique (fun _ : Fin 1 => A.Pos)
  basis x := Equiv.piUnique (fun i : Fin 1 => A.Basis (x i))
  aug x a := by
    change A.weight (x default) (a default) = ∏ i, A.weight (x i) (a i)
    exact (Fintype.prod_unique (fun i : Fin 1 => A.weight (x i) (a i))).symm

def framed {B : Type u} (x : X) (p : Point C B) := (CanonicalSetStrength.strength (extF C) X).app B (x,p)

theorem occurrence_native {F G : B → Family.{0,v} R} (h : ∀ b, Hom (F b) (G b)) (x : X) (p : Point C B) :
    occurrenceMap (fun i : Fin (framed x p).arity => h ((framed x p).label i).2) =
      occurrenceMap (fun i : Fin p.arity => h (p.label i)) := rfl

/-- Inserting singleton context units at all occurrences leaves the
actual permutation matrices of the context-unit modification unchanged. -/
theorem context_unit (x : X) (p : Point C B) :
    (occurrenceUnit (R := R) (E := Fin (framed x p).arity)).hom =
      (occurrenceUnit (R := R) (E := Fin p.arity)).hom := rfl

theorem content_unit (F : B → Family.{0,v} R) (x : X) (b : B) :
    (let p := framed x (ConstantCollectionFraming.unary b)
     (unary R (F (p.label (0 : Fin 1)).2)).hom) = (unary R (F b)).hom := rfl

theorem context_accumulation (F : B → Family.{0,v} R) (G : ∀ b, (F b).Pos → Family.{0,v} R)
    (x : X) (p : Point C B) :
    (let z := framed x p; fubini (fun i : Fin z.arity => F (z.label i).2) (fun i q => G (z.label i).2 q)) =
      fubini (fun i : Fin p.arity => F (p.label i)) (fun i q => G (p.label i) q) := rfl

theorem content_accumulation (F : B → Family.{0,v} R) (x : X) (p : Point C (Point D B)) :
    (let z := (extF C).map ((CanonicalSetStrength.strength (extF D) X).app B) (framed x p)
     (occurrenceRegroup (E := Fin z.arity) (F := fun i => Fin (z.label i).arity)
       (fun a => F (((z.label a.1).label a.2).2))).hom) =
      (occurrenceRegroup (E := Fin p.arity) (F := fun i => Fin (p.label i).arity)
        (fun a => F ((p.label a.1).label a.2))).hom := rfl

theorem context_accumulation_natural (F F' : B → Family.{0,v} R)
    (G : ∀ b, (F b).Pos → Family.{0,v} R) (G' : ∀ b, (F' b).Pos → Family.{0,v} R)
    (k : ∀ b, DepHom (G b) (G' b)) (x : X) (p : Point C B) :
    (let z := framed x p
     (fubiniLeftMap (fun i : Fin z.arity => k (z.label i).2)).comp
       (fubini (fun i : Fin z.arity => F' (z.label i).2) (fun i q => G' (z.label i).2 q))) =
      (fubini (fun i : Fin p.arity => F (p.label i)) (fun i q => G (p.label i) q)).comp
        (fubiniRightMap (fun i : Fin p.arity => k (p.label i))) :=
  fubini_natural (fun i : Fin p.arity => k (p.label i))

end ContextualComposition.OrderedMatrixFraming
