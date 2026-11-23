module
public import ContextualComposition.RelativeTensorAssociatorLastChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (s : X ⟶ X')
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

private theorem interchange_inv {G H : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}} (t : G ⟶ H) (x : Tensor X G) :
    (Parametric.interchange s t).inv.toNatTrans.app x = 𝟙 _ := by
  change (eqToHom (factor_order s t).symm).app x = 𝟙 _
  rw [eqToHom_app]; rfl

/-- First-factor tensoring is a strong comparison between the two second-factor actions. -/
def varyFirst : Second.action.{vB,uB,vX,uX,vM,uM} X ⟶ Second.action X' where
  app G := (mapFirst (G := G) s).toCatHom
  naturality t := (Parametric.interchange s t).symm
  naturality_naturality := by
    intro A D f g m
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (mapFirst (G := D) s).map ((Second.mapCell (F := X) m.as).app x) ≫ (Parametric.interchange s g).inv.toNatTrans.app x =
      (Parametric.interchange s f).inv.toNatTrans.app x ≫ (Second.mapCell (F := X') m.as).app ((mapFirst (G := A) s).obj x)
    erw [interchange_inv,interchange_inv,Category.comp_id,Category.id_comp,Second.cell_app,Second.cell_app,First.on_native,Functor.map_id]
    rfl
  naturality_id A := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (Parametric.interchange s (𝟙 A)).inv.toNatTrans.app x ≫ (Second.identityIso X' A).hom.toNatTrans.app ((mapFirst (G := A) s).obj x) =
      (mapFirst (G := A) s).map ((Second.identityIso X A).hom.toNatTrans.app x) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [interchange_inv,Second.identity_hom_app,Category.id_comp]
    rfl
  naturality_comp {A B D} f g := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    change (Parametric.interchange s (f ≫ g)).inv.toNatTrans.app x ≫ (Second.compositeIso X' f g).hom.toNatTrans.app ((mapFirst (G := A) s).obj x) =
      (mapFirst (G := D) s).map ((Second.compositeIso X f g).hom.toNatTrans.app x) ≫ 𝟙 _ ≫
      (Parametric.interchange s g).inv.toNatTrans.app ((mapSecond (F := X) f).obj x) ≫ 𝟙 _ ≫
      (mapSecond (F := X') g).map ((Parametric.interchange s f).inv.toNatTrans.app x) ≫ 𝟙 _
    simp only [interchange_inv,Second.composite_hom_app,Functor.map_id]
    simp

/-- Vary the first factor of each column of the middle module. -/
def firstMap : leftInner X M ⟶ leftInner X' M :=
  Factorization.Endpoint.Indexed.reindex M (varyFirst s)

/-- Each column comparison has identity component at an outer transition, by binary factor interchange. -/
theorem first_port {c d : C} (v : c ⟶ d) (z : Tensor X (column M c)) :
    (First.port (firstMap s M) v z).hom = 𝟙 _ := by
  exact Parametric.interchange_app s (M.map v.toLoc) z

private theorem pad {D : Type*} [Category* D] {a b : D} {p q : a ⟶ b} (h : p = q) : p ≫ 𝟙 _ = 𝟙 _ ≫ q := by simpa using h

theorem first_inner {c : C} (y : Y.obj ⟨op c⟩) :
    mapFirst s ⋙ (innerCocone X' M Y c y).extend = (innerCocone X M Y c y).extend ⋙ mapFirst s := by
  fapply extGenerators
  · intro z; rfl
  · intro b x x' m m' p q
    apply pad
    dsimp only [Functor.comp_map]
    rw [First.on_native,inner_native,inner_native,First.on_native]
  · intro a b u x m
    apply pad
    dsimp only [Functor.comp_map]
    rw [First.on_balance,Functor.map_comp,inner_balance,inner_native,inner_balance,First.on_balance]
    change _ ≫ (insertR X' M Y b).map (productMap _ ((insertM M Y b c).map (𝟙 (m,y)))) = _
    rw [Functor.map_id]

theorem first_leaf {c : C} (z : Tensor X (column M c)) {y y' : Y.obj ⟨op c⟩} (p : y ⟶ y') :
    (mapFirst (G := rightInner M Y) s).map (leafMap X M Y z p) = leafMap X' M Y ((mapFirst s).obj z) p := by
  unfold leafMap
  rw [First.on_native,Functor.map_id]
  rfl

theorem first_native {c : C} {z z' : Tensor X (column M c)} {y y' : Y.obj ⟨op c⟩} (p : z ⟶ z') (q : y ⟶ y') :
    (mapFirst (firstMap s M) ⋙ associate X' M Y).map ((Reverse.insertL X M Y c).map (productMap p q)) =
      (associate X M Y ⋙ mapFirst s).map ((Reverse.insertL X M Y c).map (productMap p q)) := by
  dsimp only [Functor.comp_map]
  rw [First.on_native,associate_native,associate_native,outer_pair,outer_pair,Functor.map_comp,first_leaf]
  congr 1
  have h := Functor.congr_hom (first_inner s M Y y') p
  change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ at h
  erw [Category.id_comp,Category.comp_id] at h
  exact h

theorem first_outer_balance {c d : C} (v : c ⟶ d) (z : Tensor X (column M c)) (y : Y.obj ⟨op d⟩) :
    (mapFirst (firstMap s M) ⋙ associate X' M Y).map (balancing (leftInner X M) Y v z y).hom =
      (associate X M Y ⋙ mapFirst s).map (balancing (leftInner X M) Y v z y).hom := by
  obtain ⟨⟨b,x,m⟩⟩ := z
  let z := (insertion X (column M c) b).obj (x,m)
  dsimp only [Functor.comp_map]
  change (associate X' M Y).map ((mapFirst (firstMap s M)).map (balancing (leftInner X M) Y v z y).hom) = _
  rw [First.on_balance,first_port]
  change (associate X' M Y).map (_ ≫ (Reverse.insertL X' M Y d).map (𝟙 _)) = _
  rw [Functor.map_id,Category.comp_id,associate_outer_balance,associate_outer_balance]
  change _ = (mapFirst s).map ((insertR X M Y b).map (productMap (𝟙 x) (balancing (row M b) Y v m y).hom))
  rw [First.on_native,Functor.map_id]
  rfl

/-- The associator commutes on the whole localized tensor with an arbitrary strong comparison in the first factor. -/
theorem first_naturality :
    mapFirst (firstMap s M) ⋙ associate X' M Y = associate X M Y ⋙ mapFirst s := by
  fapply extGenerators
  · intro z; rfl
  · intro c z z' y y' p q; exact pad (first_native s M Y p q)
  · intro c d v z y; exact pad (first_outer_balance s M Y v z y)

section Four
universe vD uD vN uN vW uW
variable {D : Type uD} [Category.{vD} D]
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (W : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vW,uW})

/-- First-factor change commutes with the established two-step route from the far-left to the far-right four-factor carrier. -/
theorem twoStep_first_naturality :
    (mapFirst (firstMap (firstMap s M) N) : farLeft X M N W ⥤ farLeft X' M N W) ⋙ (twoStep X' M N W).functor =
      (twoStep X M N W).functor ⋙ mapFirst s := by
  exact (congrArg (· ⋙ associate X' M (rightInner N W)) (first_naturality (firstMap s M) N W)).trans
    (congrArg (associate (leftInner X M) N W ⋙ ·) (first_naturality s M (rightInner N W)))

end Four

end ContextualComposition.RelativeTensor.Iterated
