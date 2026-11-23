module

public import ContextualComposition.RetainedTreeReassociation
public import ContextualComposition.CouplingPossibilities

/-! Strict composition of induced maps of retained effects and the cycle and raw-surjectivity boundaries for nonempty powerset effects. -/

@[expose] public section
namespace ContextualComposition.TreeOverlapBoundaries

open CategoryTheory CouplingPullbacks CouplingPossibilities TreeOverlapAdmission RetainedTreeReassociation
universe u

section Maps

variable {V : Type u} (F : Type u ⥤ Type u) {D E G : Diagram V}
variable {p : ∀ i, F.obj (D.space i)} {r : ∀ i, F.obj (E.space i)} {t : ∀ i, F.obj (G.space i)}

theorem retained_identity {s} (c : Cut V s) (x : Retained F D p c) :
    (DiagramMap.identity D).mapRetained F (fun _ => push_id F _) c x = x := by
  apply (rootEquiv F D p c).injective
  exact Subtype.ext (push_id F x.1)

theorem retained_comp (m : DiagramMap D E) (n : DiagramMap E G)
    (hm : ∀ i, push F (m.vertex i) (p i) = r i) (hn : ∀ i, push F (n.vertex i) (r i) = t i)
    {s} (c : Cut V s) (x : Retained F D p c) :
    n.mapRetained F hn c (m.mapRetained F hm c x) =
      (m.thenMap n).mapRetained F (fun i => (push_push F (m.vertex i) (n.vertex i) (p i)).symm.trans ((congrArg _ (hm i)).trans (hn i))) c x := by
  apply (rootEquiv F G t c).injective
  exact Subtype.ext (push_push F _ _ _)

end Maps

inductive Vertex where | xy | yz | zx
deriving DecidableEq

/-- Raw bit b parametrizes (b,b) at xy and yz, and (b,!b) at zx. -/
def cycleLeg : Vertex → Vertex → Bool → Bool
  | .zx, .xy => Bool.not
  | _, _ => id

def cycle : Diagram Vertex where
  graph := ⊤
  space _ := Bool
  edge {i j} _ := ⟨Bool,cycleLeg i j,cycleLeg j i⟩
  reverse _ _ _ h := h.symm

def both : Poss Bool := ⟨Set.univ,⟨false,trivial⟩⟩

private theorem cycle_full (i j : Vertex) : push possibilities (cycleLeg i j) both = both := by
  apply Subtype.ext
  ext b
  constructor
  · exact fun _ => trivial
  · intro _
    change ∃ c ∈ Set.univ, cycleLeg i j c = b
    cases i <;> cases j <;> first | exact ⟨b,trivial,rfl⟩ | exact ⟨!b,trivial,Bool.not_not _⟩

theorem cycle_matches : Compatible possibilities cycle (fun _ => both) :=
  fun {i j} _ => (cycle_full i j).trans (cycle_full j i).symm

theorem cycle_empty (x : Raw cycle) : False := by
  have e₁ : x.val .xy = x.val .yz := x.property (v:=.xy) (w:=.yz) (by change Vertex.xy ≠ .yz; decide)
  have e₂ : x.val .yz = x.val .zx := x.property (v:=.yz) (w:=.zx) (by change Vertex.yz ≠ .zx; decide)
  have e₃ : Bool.not (x.val .zx) = x.val .xy := x.property (v:=.zx) (w:=.xy) (by change Vertex.zx ≠ .xy; decide)
  have bad := e₃.trans (e₁.trans e₂)
  cases h : x.val .zx <;> simp [h] at bad

theorem cycle_no_joint : ¬ Nonempty (Joint possibilities cycle (fun _ => both)) :=
  fun ⟨q⟩ => cycle_empty q.val.property.choose

def dead : Diagram Bool where
  graph := ⊤
  space _ := Bool
  edge {i j} _ := ⟨Bool,(if i then fun _ => false else id),(if j then fun _ => false else id)⟩
  reverse _ _ _ h := h.symm

def deadTuple : Raw dead := ⟨fun _ => false, fun {i j} _ => by cases i <;> cases j <;> rfl⟩
def singleton {X : Type*} (x : X) : Poss X := ⟨{x},⟨x,rfl⟩⟩

theorem dead_joint : Nonempty (Joint possibilities dead (fun _ => singleton false)) := by
  refine ⟨singleton deadTuple, fun i => Subtype.ext ?_⟩
  change (coord dead i) '' {deadTuple} = {false}
  rw [Set.image_singleton]; rfl

theorem dead_matches : Compatible possibilities dead (fun _ => singleton false) :=
  necessary possibilities dead _ dead_joint.some

theorem dead_projection : ¬ Function.Surjective (coord dead false) := by
  intro surj
  obtain ⟨t, ht⟩ := surj true
  have mismatch : t.val false = false := t.property (v:=false) (w:=true) (by change false ≠ true; decide)
  exact Bool.noConfusion (ht.symm.trans mismatch)

end ContextualComposition.TreeOverlapBoundaries
