module
public import ContextualComposition.RelativeTensorFourGeneratorComparison
public import ContextualComposition.RelativeTensorWhiskeredEquivalence
public import ContextualComposition.RelativeTensorOuterRowIdentity

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- The innermost balance passes through one reassociation with the third payload unchanged. -/
theorem associate_inner_slide (W : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY}) {a b : B} {c : C}
    (u : a ⟶ b) (x : X.obj ⟨a⟩) (m : (column M c).obj ⟨op b⟩) (w : W.obj ⟨op c⟩) :
    (associate X M W).map ((Reverse.insertL X M W c).map (productMap (balancing X (column M c) u x m).hom (𝟙 w))) =
      (balancing X (rightInner M W) u x ((insertM M W b c).obj (m,w))).hom := by
  rw [associate_native,outer_only_inner,inner_balance]

variable {a b : B} {c : C} {d : D} (u : a ⟶ b) (x : X.obj ⟨a⟩) (m : (column M c).obj ⟨op b⟩)
variable (n : (column N d).obj ⟨op c⟩) (y : Y.obj ⟨op d⟩)

abbrev shortRowPoint :=
  (insertM M (rightInner N Y) b c).obj (m,(insertM N Y c d).obj (n,y))

abbrev middleRowPoint :=
  (insertM (middleComposite M N) Y b d).obj ((insertM M (column N d) b c).obj (m,n),y)

/-- On the two-step route, the native B-slide becomes the same outer B-slide on the nested right row. -/
theorem twoStep_balanceB :
    (twoStep X M N Y).functor.map (farLeftBalanceB X M N Y u x m n y) =
      (balancing X (rightInner M (rightInner N Y)) u x (shortRowPoint M N Y m n y)).hom := by
  change (associate X M (rightInner N Y)).map ((associate (leftInner X M) N Y).map
    (farLeftBalanceB X M N Y u x m n y)) = _
  unfold farLeftBalanceB
  rw [associate_triple_native]
  change (associate X M (rightInner N Y)).map ((Reverse.insertL X M (rightInner N Y) c).map
    (productMap (balancing X (column M c) u x m).hom ((insertM N Y c d).map (𝟙 (n,y))))) = _
  rw [Functor.map_id,associate_inner_slide]

/-- On the first two edges of the three-step route, the native B-slide reaches the outer B-balance
with its middle-composite row still intact. -/
theorem firstTwo_balanceB :
    (firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y).map
      (farLeftBalanceB X M N Y u x m n y) =
      (balancing X (rightInner (middleComposite M N) Y) u x (middleRowPoint M N Y m n y)).hom := by
  change (associate X (middleComposite M N) Y).map ((mapFirst (outerAssociator X M N)).map
    (farLeftBalanceB X M N Y u x m n y)) = _
  unfold farLeftBalanceB
  rw [First.on_native]
  change (associate X (middleComposite M N) Y).map ((Reverse.insertL X (middleComposite M N) Y d).map
    (productMap ((associate X M (column N d)).map ((Reverse.insertL X M (column N d) c).map
      (productMap (balancing X (column M c) u x m).hom (𝟙 n)))) (𝟙 y))) = _
  rw [associate_inner_slide]
  exact associate_inner_slide X (middleComposite M N) Y u x ((insertM M (column N d) b c).obj (m,n)) y

/-- The remaining B-slide comparison along any supplied strong row map retains its full base-change
component, including its orientation before the final balance arrow. -/
theorem rowWhisker_balanceB (V : rightInner (middleComposite M N) Y ⟶ rightInner M (rightInner N Y)) :
    ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V).map
        (farLeftBalanceB X M N Y u x m n y) =
      (insertion X (rightInner M (rightInner N Y)) a).map
        (productMap (𝟙 x) (Second.port V u (middleRowPoint M N Y m n y)).hom) ≫
      (balancing X (rightInner M (rightInner N Y)) u x
        ((Second.part V b).obj (middleRowPoint M N Y m n y))).hom := by
  rw [Functor.comp_map,firstTwo_balanceB,Second.on_balance]

/-- The identity-on-fibres row comparison rebrackets the native endpoint of this B-slide. -/
theorem direct_row_point : (OuterRow.direct M N Y ⟨op b⟩).obj (middleRowPoint M N Y m n y) =
    shortRowPoint M N Y m n y := rfl

private theorem absorb_transport {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : (C × D) ⥤ E) (z : C) {l r : D} (p : l ⟶ r) {t : E} (q : I.obj (z,r) ⟶ t)
    (hp : ∃ h : l = r, p = eqToHom h) : HEq (I.map (productMap (𝟙 z) p) ≫ q) q := by
  obtain ⟨rfl,rfl⟩ := hp
  change HEq (I.map (𝟙 (z,l)) ≫ q) q
  rw [Functor.map_id,Category.id_comp]

private theorem balance_at_eq {J : Type*} [Category* J] (F : LocallyDiscrete J ⥤ᵖ Cat.{vX,uX})
    (G : LocallyDiscrete Jᵒᵖ ⥤ᵖ Cat.{vY,uY}) {a b : J} (u : a ⟶ b) (x : F.obj ⟨a⟩)
    {y z : G.obj ⟨op b⟩} (h : y = z) :
    HEq (balancing F G u x y).hom (balancing F G u x z).hom := by subst z; rfl

private theorem commute_transport {C : Type*} [Category* C] {a b c d : C}
    (f : a ⟶ b) (g : c ⟶ d) (e : a = c) (h : b = d) (k : HEq f g) :
    f ≫ (eqToIso h).hom = (eqToIso e).hom ≫ g := by
  subst c; subst d
  rw [eq_of_heq k]
  simp

/-- A row comparison that takes the primitive endpoint to its indicated row point and whose
naturality is an equality transport preserves this generator across both pentagon routes.
The endpoint comparison is retained on both sides. -/
theorem balanceB_compare_of_port (V : rightInner (middleComposite M N) Y ⟶ rightInner M (rightInner N Y))
    (objects : ∀ z, (twoStep X M N Y).functor.obj z =
      ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V).obj z)
    (point : (Second.part V b).obj (middleRowPoint M N Y m n y) = shortRowPoint M N Y m n y)
    (port : ∃ h, (Second.port V u (middleRowPoint M N Y m n y)).hom = eqToHom h) :
    CompareAt (H := (twoStep X M N Y).functor)
      (K := (firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V)
      (fun z => eqToIso (objects z)) (farLeftBalanceB X M N Y u x m n y) := by
  apply commute_transport
  rw [twoStep_balanceB,rowWhisker_balanceB]
  apply HEq.symm
  exact (absorb_transport _ x _ _ port).trans
    (balance_at_eq X (rightInner M (rightInner N Y)) u x point)

end ContextualComposition.RelativeTensor.Iterated
