module
public import ContextualComposition.RelativeTensorFourGeneratorComparison
public import ContextualComposition.RelativeTensorOuterAssociator
public import ContextualComposition.RelativeTensorOuterRowIdentity

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.Pentagon
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

abbrev middlePairObject {b : B} {c : C} {d : D} (m : (column M c).obj ⟨op b⟩) (n : (column N d).obj ⟨op c⟩) :=
  (insertion (row M b) (column N d) c).obj (m,n)

abbrev leftTripleObject {b : B} {c : C} {d : D} (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩) (n : (column N d).obj ⟨op c⟩) :=
  (insertion (leftInner X M) (column N d) c).obj ((insertion X (column M c) b).obj (x,m),n)

variable {b : B} {c : C} {d e : D} (v : d ⟶ e) (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩)
variable (n : (column N d).obj ⟨op c⟩) (y : Y.obj ⟨op e⟩)

/-- The same D-balance at the innermost junction of the fully right-associated carrier. -/
abbrev rightBalanceD :=
  (insertR X M (rightInner N Y) b).map (productMap (𝟙 x)
    ((insertR (row M b) N Y c).map (productMap (𝟙 m) (balancing (row N c) Y v n y).hom)))

/-- The short route carries the outermost D-balance across both associators to the innermost D-balance. -/
theorem short_balanceD :
    (twoStep X M N Y).functor.map (farLeftBalanceD X M N Y v (leftTripleObject X M N x m n) y) =
      rightBalanceD X M N Y v x m n y := by
  change (associate X M (rightInner N Y)).map ((associate (leftInner X M) N Y).map (balancing _ Y v (leftTripleObject X M N x m n) y).hom) = _
  rw [associate_outer_balance]
  change (associate X M (rightInner N Y)).map ((Reverse.insertL X M (rightInner N Y) c).map
    (productMap (𝟙 ((insertion X (column M c) b).obj (x,m))) (balancing (row N c) Y v n y).hom)) = _
  rw [associate_native,outer_leaf]
  rfl

private theorem edge_port {d e : D} (v : d ⟶ e) (z : (leftBrackets X M N).obj ⟨d⟩) :
    (First.port (outerAssociator X M N) v z).hom = 𝟙 _ := by
  change (eqToHom (last_naturality X M (N.map v.toLoc)).symm).app z = _
  rw [eqToHom_app]
  rfl

/-- The first two edges of the long route produce the original D-balance of the substituted middle row. -/
theorem beforeRow_balanceD :
    (firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y).map
      (farLeftBalanceD X M N Y v (leftTripleObject X M N x m n) y) =
      (insertR X (middleComposite M N) Y b).map (productMap (𝟙 x) (balancing (row (middleComposite M N) b) Y v (middlePairObject M N m n) y).hom) := by
  change (associate X (middleComposite M N) Y).map ((mapFirst (outerAssociator X M N)).map (balancing _ Y v (leftTripleObject X M N x m n) y).hom) = _
  rw [First.on_balance,edge_port]
  change (associate X (middleComposite M N) Y).map (_ ≫ (Reverse.insertL X (middleComposite M N) Y e).map (𝟙 _)) = _
  rw [Functor.map_id,Category.comp_id,associate_outer_balance]
  rfl

/-- The actual direct row component takes the substituted-row D-balance to the native innermost balance. -/
theorem row_balanceD :
    (OuterRow.direct M N Y ⟨op b⟩).map (balancing (row (middleComposite M N) b) Y v (middlePairObject M N m n) y).hom =
      (insertR (row M b) N Y c).map (productMap (𝟙 m) (balancing (row N c) Y v n y).hom) := by
  change (associate (row M b) N Y).map ((mapFirst (OuterRow.rowId M N ⟨op b⟩)).map (balancing _ Y v (middlePairObject M N m n) y).hom) = _
  rw [First.on_balance]
  have h : (First.port (OuterRow.rowId M N ⟨op b⟩) v (middlePairObject M N m n)).hom = 𝟙 _ := rfl
  rw [h]
  change (associate (row M b) N Y).map (_ ≫ (Reverse.insertL (row M b) N Y e).map (𝟙 _)) = _
  rw [Functor.map_id,Category.comp_id,associate_outer_balance]
  rfl

section Last
variable (V : rightInner (middleComposite M N) Y ⟶ rightInner M (rightInner N Y))

/-- On this generator the last strong change is evaluated only at the original B-row. -/
theorem long_balanceD_app :
    ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond V).map
      (farLeftBalanceD X M N Y v (leftTripleObject X M N x m n) y) =
      (keep X M (rightInner N Y) x).map
        ((Second.part V b).map (balancing (row (middleComposite M N) b) Y v (middlePairObject M N m n) y).hom) := by
  change (mapSecond V).map ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y).map _) = _
  rw [beforeRow_balanceD,Second.on_native]
  rfl

private theorem map_on_equal {J K L : Type*} [Category* J] [Category* K] [Category* L] {F G : J ⥤ K}
    (h : F = G) (P : K ⥤ L) {u v : J} (f : u ⟶ v) : HEq (P.map (F.map f)) (P.map (G.map f)) := by subst G; rfl

/-- Equality after independently identifying the strong map's row component, across its two endpoints. -/
theorem long_balanceD_heq (component : Second.part V b = OuterRow.direct M N Y ⟨op b⟩) :
    HEq (((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond V).map
        (farLeftBalanceD X M N Y v (leftTripleObject X M N x m n) y)) (rightBalanceD X M N Y v x m n y) :=
  (heq_of_eq (long_balanceD_app X M N Y v x m n y V)).trans
    ((map_on_equal component (keep X M (rightInner N Y) x) _).trans
      (heq_of_eq (congrArg (keep X M (rightInner N Y) x).map (row_balanceD M N Y v m n y))))

private theorem compareArrow {T : Type*} [Category* T] {a b a' b' : T} (f : a ⟶ b) (g : a' ⟶ b') (p : a = a') (q : b = b') (h : HEq f g) :
    f ≫ eqToHom q = eqToHom p ≫ g := by subst a'; subst b'; cases eq_of_heq h; simp

/-- The D-junction field required by the four-generator extensionality theorem, for the independently computed row components and any route object identification. -/
theorem balanceD_test_of_components (component : ∀ b : B, Second.part V b = OuterRow.direct M N Y ⟨op b⟩)
    (p : ∀ z, (twoStep X M N Y).functor.obj z = ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond V).obj z)
    (z : Tensor (leftInner X M) (column N d)) :
    CompareAt (H := (twoStep X M N Y).functor) (K := (firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond V)
      (fun z => eqToIso (p z)) (farLeftBalanceD X M N Y v z y) := by
  obtain ⟨⟨c,⟨⟨b,x,m⟩⟩,n⟩⟩ := z
  let z := leftTripleObject X M N x m n
  let L := leftInner (leftInner X M) N
  exact compareArrow _ _ (p ((insertion L Y d).obj (z,(backward Y v).obj y)))
    (p ((insertion L Y e).obj ((forward L v).obj z,y))) ((heq_of_eq (short_balanceD X M N Y v x m n y)).trans
    (long_balanceD_heq X M N Y v x m n y V (component b)).symm)

end Last

end ContextualComposition.RelativeTensor.Iterated.Pentagon
