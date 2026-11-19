module
public import ContextualComposition.ContextadLawTransport
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadCellPasting
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex FibreValue ContextadRoutes ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
universe u v
section Fibre
variable {K L B : Type*} [Category* K] [Category* L] [Category* B]
variable (p : K ⥤ B) (q : L ⥤ B)
theorem fiberId (F : K ⥤ L) (h : F ⋙ q = p) (k) (A : B) :
    (onFiber F F h h (Iso.refl _) k A).hom = 𝟙 _ := by
  ext x : 2
  apply Subtype.ext
  simp [onFiber,vertical]; rfl
theorem fiberComp (F G H : K ⥤ L) (f : F ⋙ q = p) (g : G ⋙ q = p) (h : H ⋙ q = p)
    (i : F ≅ G) (j : G ≅ H) (hi hj hk) (A : B) :
    (onFiber F H f h (i ≪≫ j) hk A).hom =
      (onFiber F G f g i hi A).hom ≫ (onFiber G H g h j hj A).hom := by
  ext x : 2
  apply Subtype.ext
  change _ = (_ : _ ⟶ _) ≫ (_ : _ ⟶ _)
  simp [onFiber,vertical,Category.assoc]
theorem fiberIdEq (F : K ⥤ L) (h : F ⋙ q = p) (v : F ≅ F) (e : v = Iso.refl _) (k) (A : B) :
    (onFiber F F h h v k A).hom = 𝟙 _ := by subst v; exact fiberId _ _ F h k A
theorem fiberCompEq (F G H : K ⥤ L) (f : F ⋙ q = p) (g : G ⋙ q = p) (h : H ⋙ q = p)
    (i : F ≅ G) (j : G ≅ H) (v : F ≅ H) (e : v = i ≪≫ j) (hi hj hk) (A : B) :
    (onFiber F H f h v hk A).hom = (onFiber F G f g i hi A).hom ≫ (onFiber G H g h j hj A).hom := by
  subst v; exact fiberComp _ _ F G H f g h i j hi hj hk A
end Fibre
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {i j : Nat} {r s t : Map S i j}
def idCell (r : Map S i j) : Cell r r where
  grade := Iso.refl _
  source x := by simpa using pureId ((power S j).source.obj (r.grade.obj x))
  endpoint := by simp
def thenCell (a : Cell r s) (b : Cell s t) : Cell r t where
  grade := a.grade ≪≫ b.grade
  source x := by simp only [Iso.trans_hom,NatTrans.comp_app,Functor.map_comp]; exact pureComp (a.source x) (b.source x)
  endpoint := by simp only [Iso.trans_hom,whiskerRight_comp,Category.assoc,b.endpoint,a.endpoint]
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem rawId (r : Map S i j) : (rawCell Y (idCell r)).hom = 𝟙 _ :=
  WeightedCells.weightId Y _ _ _
theorem rawComp (a : Cell r s) (b : Cell s t) :
    (rawCell Y (thenCell a b)).hom = (rawCell Y a).hom ≫ (rawCell Y b).hom :=
  WeightedCells.weightComp Y _ _ _ _ _ _ _
theorem globId (r : Map S i j) : globalCell Y (idCell r) = Iso.refl _ := by
  apply Iso.ext
  simp [globalCell,rawId]
theorem globComp (a : Cell r s) (b : Cell s t) :
    globalCell Y (thenCell a b) = globalCell Y a ≪≫ globalCell Y b := by
  apply Iso.ext
  simp [globalCell,rawComp]
theorem evaluatedId (r : Map S i j) (A : B) : (evalCell Y (idCell r) A).hom = 𝟙 _ := by
  simp only [evalCell,isoWhiskerLeft_hom,isoWhiskerRight_hom]
  rw [fiberIdEq _ _ _ (over Y r) _ (globId Y r) _ A]
  simp
theorem evaluatedComp (a : Cell r s) (b : Cell s t) (A : B) :
    (evalCell Y (thenCell a b) A).hom = (evalCell Y a A).hom ≫ (evalCell Y b A).hom := by
  unfold evalCell
  simp only [isoWhiskerLeft_hom,isoWhiskerRight_hom]
  rw [fiberCompEq _ _ _ _ _ (over Y r) (over Y s) (over Y t) _ _ _ (globComp Y a b)
    (globalVertical Y a) (globalVertical Y b) (globalVertical Y _) A]
  simp only [whiskerRight_comp,whiskerLeft_comp]
end ContextualComposition.GrothendieckStep.ContextadCellPasting
