module
public import ContextualComposition.AmbientRebasedStrong
public import ContextualComposition.AmbientCoherentObserver
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientTypedConstraint
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open ContextadNativeLaws ContextadRoutes ContextadLawTransport ContextadModification AmbientSquareBridge
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
universe u v
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {i j : Nat} (p q : Map S i j) (cp : gradeCart p) (cq : gradeCart q) (c : Cell p q)
variable (a b : ∀ Z : Obj.{u,v} B, obj S i Z ⟶ obj S j Z)
variable (e : ∀ Z, a Z = oper S p cp Z) (w : ∀ Z, b Z = oper S q cq Z)
noncomputable def map := AmbientRebasedStrong.strong (AmbientPseudonaturality.operation S p cp) a e
noncomputable def iso : map p cp a e ≅ map q cq b w :=
  AmbientRebasedStrong.modification (AmbientPseudonaturality.operation S p cp) a e (AmbientPseudonaturality.operation S q cq) b w
    (fun X => AmbientNativeModification.cmp c cp cq X) (fun f => sourceSquare c cp cq f)
theorem app (Z : Obj.{u,v} B) (k : a Z ≅ b Z) (h : reframe (e Z) (w Z) (AmbientNativeModification.cmp c cp cq Z) = k) :
    (iso p q cp cq c a b e w).hom.as.app Z = k.hom := congrArg Iso.hom h
end ContextualComposition.GrothendieckStep.AmbientTypedConstraint
