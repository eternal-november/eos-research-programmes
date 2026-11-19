module
public import ContextualComposition.TaggedSourceCorner
@[expose] public section
namespace ContextualComposition.GrothendieckStep.WhiskerSquares
open CategoryTheory CategoryTheory.Functor Opposite SpanApex BoundaryPaste SuffixCell
section General
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
theorem whiskComposite (Q : A ⥤ B) (T : C ⥤ D) {F G H : B ⥤ C} (a : F ⟶ G) (b : G ⟶ H) (c : F ⟶ H) (h : a ≫ b = c) :
    whiskerLeft Q (whiskerRight a T) ≫ whiskerLeft Q (whiskerRight b T) = whiskerLeft Q (whiskerRight c T) := by
  ext x
  exact (T.map_comp _ _).symm.trans (congrArg T.map (NatTrans.congr_app h (Q.obj x)))
theorem alongComposite {K J L : Type*} [Category* K] [Category* J] [Category* L]
    (e : K ⥤ B) (p : J ⥤ B) (q : L ⥤ B) {F G H : J ⥤ L} (f : F ⋙ q = p) (g : G ⋙ q = p) (h : H ⋙ q = p)
    (a : F ≅ G) (b : G ≅ H) (c : F ≅ H) (va : vertical p q f g a.hom) (vb : vertical p q g h b.hom) (vc : vertical p q f h c.hom)
    (eqn : a.hom ≫ b.hom = c.hom) : (alongIsoCell e p q f g a va).hom ≫ (alongIsoCell e p q g h b vb).hom =
    (alongIsoCell e p q f h c vc).hom := by
  change alongCell e p q f g a.hom va ≫ alongCell e p q g h b.hom vb = alongCell e p q f h c.hom vc
  rw [along_comp]; congr 1
universe u v
variable {P : Type u} [Category.{v} P] {K J : Type*} [Category* K] [Category* J]
variable (Y Z : Pᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ P) (p d : J ⥤ P)
variable {F G H : Total Y d ⥤ Total Z (𝟭 P)}
theorem foldComposite (f : F ⋙ pr Z = tailSource Y p d) (g : G ⋙ pr Z = tailSource Y p d) (h : H ⋙ pr Z = tailSource Y p d)
    (a : F ≅ G) (b : G ≅ H) (c : F ≅ H) (va : vertical _ _ f g a.hom) (vb : vertical _ _ g h b.hom) (vc : vertical _ _ f h c.hom)
    (eqn : a.hom ≫ b.hom = c.hom) :
    (foldIsoCell Y Z e p d f g a va).hom ≫ (foldIsoCell Y Z e p d g h b vb).hom = (foldIsoCell Y Z e p d f h c vc).hom :=
  whiskComposite (separate Y e p d) (unview Z e) _ _ _ (alongComposite e _ _ f g h a b c va vb vc eqn)
end General
section Algebra
variable {C : Type*} [Category* C] {A B D E X Y : C}
theorem twoFaces (a : A ⟶ B) (b : D ⟶ E) (u : A ≅ X) (v : B ≅ X) (w : D ≅ Y) (z : E ≅ Y) (j : X ≅ Y)
    (p : a ≫ v.hom = u.hom) (q : b ≫ z.hom = w.hom) :
    a ≫ (v ≪≫ j ≪≫ z.symm).hom = (u ≪≫ j ≪≫ w.symm).hom ≫ b := by
  apply (cancel_mono z.hom).mp
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id,q]
  rw [← Category.assoc,p]
end Algebra
end ContextualComposition.GrothendieckStep.WhiskerSquares
