module
public import ContextualComposition.AmbientHorizontalRead
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientLetterRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X : Obj.{u,v} B} {i j k l : Nat} {r s t : Map S j k}
theorem frame {a b a' b' : obj S j X ⟶ obj S k X} (p : a' = a) (q : b = b') {v : a ⟶ b} {c : Cell r s}
    (h : Reads v c) : Reads (eqToHom p ≫ v ≫ eqToHom q) c := by
  subst a'; subst b'; simpa using h
theorem frameIso {a b a' b' : obj S j X ⟶ obj S k X} (p : a' = a) (q : b = b') (v : a ≅ b) {c : Cell r s}
    (h : Reads v.hom c) : Reads (eqToIso p ≪≫ v ≪≫ eqToIso q).hom c := frame p q h
theorem castL {v w : obj S j X ⟶ obj S k X} {a : v ⟶ w} (e : t = r) {c : Cell r s} (h : Reads a c) : Reads a (thenCell (ContextadSchedule.castCell e) c) := by
  subst t; intro x; apply (h x).trans
  rw [show (rawCell X (thenCell _ c)).hom = _ from rawComp X _ _,show (rawCell X (ContextadSchedule.castCell rfl)).hom = _ from rawId X r,Category.id_comp]
  exact Aligned.refl _
theorem castR {v w : obj S j X ⟶ obj S k X} {a : v ⟶ w} (e : s = t) {c : Cell r s} (h : Reads a c) : Reads a (thenCell c (ContextadSchedule.castCell e)) := by
  subst t; intro x; apply (h x).trans
  rw [show (rawCell X (thenCell c _)).hom = _ from rawComp X _ _,show (rawCell X (ContextadSchedule.castCell rfl)).hom = _ from rawId X s,Category.comp_id]
  exact Aligned.refl _
theorem middleRead {a b : obj S j X ⟶ obj S k X} {w z : obj S k X ⟶ obj S l X} {s' : Map S j l} {r' : Map S j l}
    (h : a ≫ w ≅ b ≫ z) {c : Cell r' s'} (q : Reads h.hom c) (f : obj S i X ⟶ obj S j X) (p : Map S i j) (k : encode S f = raw X p) :
    Reads (middle f a w h).hom (before c p) := by
  simp only [middle,Iso.trans_hom,Strict.associator_eqToIso,Iso.symm_hom,eqToIso.hom,eqToIso.inv,whiskerLeftIso_hom]
  exact frame (Category.assoc f a w) (Category.assoc f b z).symm (pre q f p k)
variable (X) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
def leftRead := frameIso (route S X (leftUnit d) (tensor m) (presIso c.left.grade (fun _ h => h)) m.cart (E S (obj S 1 X) d) (outerE S X d)) (idRoute S X 1)
  (AmbientNativeModification.cmp c.left (presIso c.left.grade (fun _ h => h)) (fun _ h => h) X) (AmbientHorizontalRead.cmp (X := X) c.left (presIso c.left.grade (fun _ h => h)) (fun _ h => h))
def rightRead := frameIso (route S X (rightUnit d) (tensor m) (presIso c.right.grade (fun _ h => h)) m.cart (K S (E S X d)) (innerE S X d)) (idRoute S X 1)
  (AmbientNativeModification.cmp c.right (presIso c.right.grade (fun _ h => h)) (fun _ h => h) X) (AmbientHorizontalRead.cmp (X := X) c.right (presIso c.right.grade (fun _ h => h)) (fun _ h => h))
def assocRead := frameIso (route S X (firstTwo m) (tensor m) (assocCart m) m.cart (M S (obj S 1 X) m) (outerM S X m))
  (route S X (lastTwo m) (tensor m) (presIso c.assoc.grade.symm (assocCart m)) m.cart (K S (M S X m)) (innerM S X m)).symm
  (AmbientNativeModification.cmp c.assoc (assocCart m) (presIso c.assoc.grade.symm (assocCart m)) X) (AmbientHorizontalRead.cmp (X := X) c.assoc (assocCart m) (presIso c.assoc.grade.symm (assocCart m)))
end ContextualComposition.GrothendieckStep.AmbientLetterRead
