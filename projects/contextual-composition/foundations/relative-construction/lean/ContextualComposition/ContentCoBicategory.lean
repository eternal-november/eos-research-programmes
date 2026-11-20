module
public import ContextualComposition.RepresentableBicategoryAssembly
public import Mathlib.CategoryTheory.Bicategory.Opposites
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentCoBicategory
open CategoryTheory Opposite
open RepresentableBicategoryAssembly
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {B : Type u} {H : B → B → Type v} [∀ x y, Category.{w} (H x y)]
variable (O : Operations H)

def cellOp {x y z : B} : (H x y)ᵒᵖ × (H y z)ᵒᵖ ⥤ (H x z)ᵒᵖ where
  obj f := op (cmp O f.1.unop f.2.unop)
  map r := (compCell O r.1.unop r.2.unop).op
  map_id f := congrArg Quiver.Hom.op (cellId O f.1.unop f.2.unop)
  map_comp r s := congrArg Quiver.Hom.op (cellComp O s.1.unop r.1.unop s.2.unop r.2.unop)

def ops : Operations (fun x y => (H x y)ᵒᵖ) where
  unit x := op (O.unit x)
  multiply := cellOp O
  left f := (O.left f.unop).symm.op
  right f := (O.right f.unop).symm.op
  assoc f g h := (O.assoc f.unop g.unop h.unop).symm.op

theorem invertNatural {D : Type*} [Category D] {a b c d : D}
    (s : a ⟶ b) (t : c ⟶ d) (i : a ≅ c) (j : b ≅ d) (e : s ≫ j.hom = i.hom ≫ t) :
    i.inv ≫ s = t ≫ j.inv := by
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc,e,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

def whiskL {x y z : B} (f : H x y) {g h : H y z} (s : g ≅ h) :
    cmp O f g ≅ cmp O f h where
  hom := lW O f s.hom
  inv := lW O f s.inv
  hom_inv_id := by rw [← leftRule,s.hom_inv_id]; exact cellId O f g
  inv_hom_id := by rw [← leftRule,s.inv_hom_id]; exact cellId O f h

def whiskR {x y z : B} {f g : H x y} (s : f ≅ g) (h : H y z) :
    cmp O f h ≅ cmp O g h where
  hom := rW O s.hom h
  inv := rW O s.inv h
  hom_inv_id := by rw [← rightRule,s.hom_inv_id]; exact cellId O f h
  inv_hom_id := by rw [← rightRule,s.inv_hom_id]; exact cellId O g h

theorem triangleInv (L : Laws O) {x y z : B} (f : H x y) (g : H y z) :
    lW O f (O.left g).inv ≫ (O.assoc f (O.unit y) g).inv = rW O (O.right f).inv g := by
  have q : O.assoc f (O.unit y) g ≪≫ whiskL O f (O.left g) = whiskR O (O.right f) g :=
    Iso.ext (L.triangle f g)
  exact congrArg Iso.inv q

theorem pentagonInv (L : Laws O) {x y z r s : B} (f : H x y) (g : H y z) (h : H z r) (i : H r s) :
    lW O f (O.assoc g h i).inv ≫ (O.assoc f (cmp O g h) i).inv ≫ rW O (O.assoc f g h).inv i =
      (O.assoc f g (cmp O h i)).inv ≫ (O.assoc (cmp O f g) h i).inv := by
  have q : whiskR O (O.assoc f g h) i ≪≫ O.assoc f (cmp O g h) i ≪≫ whiskL O f (O.assoc g h i) =
      O.assoc (cmp O f g) h i ≪≫ O.assoc f g (cmp O h i) :=
    Iso.ext (L.pentagon f g h i)
  simpa only [Iso.trans_inv,Category.assoc,whiskL,whiskR] using congrArg Iso.inv q

theorem laws (L : Laws O) : Laws (ops O) where
  leftNat t := congrArg Quiver.Hom.op (invertNatural _ _ _ _ (L.leftNat t.unop))
  rightNat t := congrArg Quiver.Hom.op (invertNatural _ _ _ _ (L.rightNat t.unop))
  assocFirst t g h := congrArg Quiver.Hom.op (invertNatural _ _ _ _ (L.assocFirst t.unop g.unop h.unop))
  assocMiddle := by
    intro x y z r f g g' t h
    exact congrArg Quiver.Hom.op (invertNatural _ _ _ _ (L.assocMiddle f.unop t.unop h.unop))
  assocLast := by
    intro x y z r f g h h' t
    exact congrArg Quiver.Hom.op (invertNatural _ _ _ _ (L.assocLast f.unop g.unop t.unop))
  triangle f g := congrArg Quiver.Hom.op (triangleInv O L f.unop g.unop)
  pentagon f g h i := by
    apply Quiver.Hom.unop_inj
    rw [unop_comp,unop_comp,unop_comp,Category.assoc]
    exact pentagonInv O L f.unop g.unop h.unop i.unop

end ContextualComposition.GrothendieckStep.ContentCoBicategory
