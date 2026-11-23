module

public import ContextualComposition.DirectedStateIterates
public import ContextualComposition.SelectiveStateContraction

/-! Exchange of the two actual directed iterates descends through localization at independently chosen coordinate generators. Marks always travel with their own state coordinate. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.DirectedStateMarkedExchange

open CategoryTheory Opposite DirectedStateBalance DirectedStateDiagramMap DirectedStateNativeFaithfulness DirectedStateIntertwiners DirectedStateIterates
universe u
variable {S T : Type u} [Category.{u} S] [Category.{u} T]
  (A : Index T ⥤ Index S ⥤ Cat.{u,u}) (P : MorphismProperty T) (Q : MorphismProperty S)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

inductive Marked : {x y : Iterated A} → (x ⟶ y) → Prop
  | outer {i j : T} (h : i ⟶ j) (hp : P h) (x : Balance (strict (A.obj (op j,i)))) : Marked ((slide (strict (outer A)) h).app x)
  | inner (t : T) {i j : S} (h : i ⟶ j) (hq : Q h) (x : (A.obj (op t,t)).obj (op j,i)) :
    Marked ((outerInsert A t).map ((slide (strict (A.obj (op t,t))) h).app x))

abbrev marks : MorphismProperty (Iterated A) := @Marked _ _ _ _ A P Q
abbrev Result := (marks A P Q).Localization

theorem iso_of_conjugate {C : Type*} [Category* C] {a b a' b' : C} {f : a ⟶ b} {g : a' ⟶ b'}
    (p : Conjugate f g) (h : IsIso g) : IsIso f := by
  obtain ⟨rfl,rfl,e⟩ := p; simp only [eqToHom_refl,Category.comp_id,Category.id_comp] at e
  exact e.symm ▸ h

theorem inverts : (marks A P Q).IsInvertedBy (swap A ⋙ (marks A.flip Q P).Q) := by
  intro x y f hf
  let W := marks A.flip Q P
  cases hf with
  | outer h hp x =>
    obtain ⟨⟨s,x⟩⟩ := x
    exact iso_of_conjugate (map_conjugate W.Q (swap_outer_slide A h s x))
      (W.Q_inverts _ (Marked.inner (A:=A.flip) (P:=Q) (Q:=P) s h hp x))
  | inner t h hq x =>
    exact iso_of_conjugate (map_conjugate W.Q (swap_inner_slide A t h x))
      (W.Q_inverts _ (Marked.outer (A:=A.flip) (P:=Q) (Q:=P) h hq _))

def change : Result A P Q ⥤ Result A.flip Q P :=
  Localization.Construction.lift _ (inverts A P Q)

theorem change_fac : (marks A P Q).Q ⋙ change A P Q = swap A ⋙ (marks A.flip Q P).Q :=
  Localization.Construction.fac _ _

theorem change_twice : change A P Q ⋙ change A.flip Q P = 𝟭 _ := by
  apply Localization.Construction.uniq
  calc
    _ = (swap A ⋙ (marks A.flip Q P).Q) ⋙ change A.flip Q P :=
        congrArg (· ⋙ change A.flip Q P) (change_fac A P Q)
    _ = swap A ⋙ swap A.flip ⋙ (marks A P Q).Q :=
        congrArg (swap A ⋙ ·) (change_fac A.flip Q P)
    _ = (𝟭 (Iterated A)) ⋙ (marks A P Q).Q :=
        congrArg (· ⋙ (marks A P Q).Q) (swap_twice A)
    _ = _ := rfl

def localizedExchange : IsoCat (Result A P Q) (Result A.flip Q P) where
  functor := change A P Q
  inverse := change A.flip Q P
  unit_eq := (change_twice A P Q).symm
  counit_eq := change_twice A.flip Q P

end ContextualComposition.DirectedStateMarkedExchange
