module
public import ContextualComposition.AmbientMonadMaps
public import ContextualComposition.AmbientScheduleRealization
public import ContextualComposition.ContextadOutsideTransport
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientHorizontalFrames
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open AmbientBicategory AmbientCoordinates ContextadLawTransport ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadAmbientPayload AmbientRoundTrip AmbientBlockIteration ContextadWeakAction ContextadOuterCharts
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
universe u v
section Generic
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
theorem joinChart (U : A ⥤ E) (V : B ⥤ F) (J : C ⥤ E) (K : D ⥤ F) [U.IsIso] [J.IsIso]
    (L : A ⥤ C) (M : B ⥤ D) (r : A ⥤ B) (s : C ⥤ D) (u : L ⋙ J = U) (v : M ⋙ K = V)
    (k : r ⋙ M = L ⋙ s) : U.strictInv ⋙ r ⋙ V = J.strictInv ⋙ s ⋙ K := by
  apply U.asIsomorphism.functor_comp_injective
  apply (ContextadRecognition.eraseInv U _).trans
  apply (congrArg (r ⋙ ·) v.symm).trans
  apply (congrArg (· ⋙ K) k).trans
  exact (congrArg (L ⋙ ·) (ContextadRecognition.eraseInv J (s ⋙ K))).symm.trans (congrArg (· ⋙ J.strictInv ⋙ s ⋙ K) u)
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (X : Obj.{u,v} B) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S)
noncomputable abbrev E := oper S (insert S d) (unitCart d) X
noncomputable abbrev M := oper S (tensor m) m.cart X
abbrev tot {V W : Obj.{u,v} B} (a : V ⟶ W) := totalStrong a.hom
theorem totalOper {i j : Nat} (r : Map S i j) (p : gradeCart r) : tot (oper S r p X) = global X r :=
  encodeDecode _ _ _ _ (globalPres _ _ p)
theorem totalAfter {U V W : Obj.{u,v} B} (a : U ⟶ V) (b : V ⟶ W) : tot (a ≫ b) = tot a ⋙ tot b := strongComp a.hom b.hom
theorem outerE : global X (leftUnit d) = tot (E S (obj S 1 X) d) :=
  (ContextadOuterRigidity.functorRigid (outerUnitTotal X d) (ContextadOuterRigidity.outsideUnitTransport X d)).trans (totalOper S _ _ _).symm
theorem outerM : global X (firstTwo m) = tot (M S (obj S 1 X) m) :=
  (ContextadOuterRigidity.functorRigid (outerTensorTotal X m) (ContextadOuterRigidity.outsideTensorTransport X m)).trans (totalOper S _ _ _).symm
theorem liftOper {i j : Nat} (r : Map S i j) (p : gradeCart r) :
    (BlockEvaluation.global S (PackedFree.pow S X i) 1).strictInv ⋙ ContextadWeakAction.action (power S 1).dest (global X r) (over X r) ⋙ BlockEvaluation.global S (PackedFree.pow S X j) 1 =
    tot (AmbientBicategory.map S 1 (oper S r p X)) := by
  apply Eq.trans _ (encodedBlock S (nativeStrong X r p) 1).symm
  exact congrArg (fun z => (BlockEvaluation.global S (PackedFree.pow S X i) 1).strictInv ⋙ z ⋙ BlockEvaluation.global S (PackedFree.pow S X j) 1)
    (ContextadUnitTotal.congrAction _ _ _ (totalOper S X r p).symm)
theorem innerE : global X (rightUnit d) = tot (AmbientBicategory.map S 1 (E S X d)) :=
  (joinChart (chart S X 1) (chart S X 2) (chart S (obj S 0 X) 1) (chart S (obj S 1 X) 1)
    (splitAt X 1 0) (splitAt X 1 1) (raw X (rightUnit d)) _ (splitOne0 X) (splitOne1 X) (splitInside X 1 (insert S d))).trans (liftOper S X (insert S d) (unitCart d))
theorem innerM : global X (lastTwo m) = tot (AmbientBicategory.map S 1 (M S X m)) :=
  (joinChart (chart S X 3) (chart S X 2) (chart S (obj S 2 X) 1) (chart S (obj S 1 X) 1)
    (splitAt X 1 2) (splitAt X 1 1) (raw X (lastTwo m)) _ (splitOne2 X) (splitOne1 X) (splitInside X 1 (tensor m))).trans (liftOper S X (tensor m) m.cart)
theorem route {i j k : Nat} (r : Map S i j) (s : Map S j k) (p : gradeCart (comp r s)) (q : gradeCart s)
    (a : obj S i X ⟶ obj S j X) (h : global X r = tot a) : a ≫ oper S s q X = oper S (comp r s) p X := by
  apply InducedBicategory.hom_ext; apply encodeInjective
  exact (totalAfter a _).trans ((congrArg₂ (· ⋙ ·) h.symm (totalOper S X s q)).trans ((globalComp X r s).trans (totalOper S X _ p).symm))
theorem idRoute (i : Nat) : oper S (identity i) (fun _ h => h) X = 𝟙 (obj S i X) := by
  apply InducedBicategory.hom_ext; apply encodeInjective
  exact (totalOper S X _ _).trans ((globalId X i).trans strongId.symm)
variable (c : Constraints d m)
noncomputable def left : E S (obj S 1 X) d ≫ M S X m ≅ 𝟙 (obj S 1 X) :=
  eqToIso (route S X (leftUnit d) (tensor m) (presIso c.left.grade (fun _ h => h)) m.cart (E S (obj S 1 X) d) (outerE S X d)) ≪≫ AmbientNativeModification.cmp c.left (presIso c.left.grade (fun _ h => h)) (fun _ h => h) X ≪≫ eqToIso (idRoute S X 1)
noncomputable def right : AmbientBicategory.map S 1 (E S X d) ≫ M S X m ≅ 𝟙 (obj S 1 X) :=
  eqToIso (route S X (rightUnit d) (tensor m) (presIso c.right.grade (fun _ h => h)) m.cart (AmbientBicategory.map S 1 (E S X d)) (innerE S X d)) ≪≫ AmbientNativeModification.cmp c.right (presIso c.right.grade (fun _ h => h)) (fun _ h => h) X ≪≫ eqToIso (idRoute S X 1)
noncomputable def assoc : M S (obj S 1 X) m ≫ M S X m ≅ AmbientBicategory.map S 1 (M S X m) ≫ M S X m :=
  eqToIso (route S X (firstTwo m) (tensor m) (assocCart m) m.cart (M S (obj S 1 X) m) (outerM S X m)) ≪≫ AmbientNativeModification.cmp c.assoc (assocCart m) (presIso c.assoc.grade.symm (assocCart m)) X ≪≫ eqToIso (route S X (lastTwo m) (tensor m) (presIso c.assoc.grade.symm (assocCart m)) m.cart (AmbientBicategory.map S 1 (M S X m)) (innerM S X m)).symm
end ContextualComposition.GrothendieckStep.AmbientHorizontalFrames
