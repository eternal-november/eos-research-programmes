module
public import ContextualComposition.ContextadAmbientOperation
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadAmbientPayload
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.StrongTrans Opposite FibreValue NativeCleavage
open ContextadModification SpanApex NativeBlocks ContextadRoutes ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
universe u v
section Generic
variable {D : Type*} [Category* D] (Y Z : Dᵒᵖ ⥤ Cat.{v,u}) (F G : Total Y (𝟭 D) ⥤ Total Z (𝟭 D))
    (f : F ⋙ proj Z = proj Y) (g : G ⋙ proj Z = proj Y) (i : F ≅ G) (h : ∀ x, Pure ((proj Z).map (i.hom.app x)))
    (p : Pres F (proj Y) (proj Z)) (q : Pres G (proj Y) (proj Z))
abbrev ModIso {A C : Dᵒᵖ ⥤ Cat.{v,u}} (s t : StrongTrans A.toPseudofunctor' C.toPseudofunctor') :=
  @Iso _ (StrongTrans.homCategory (F := A.toPseudofunctor') (G := C.toPseudofunctor')) s t
noncomputable def invertibleMod : ModIso (decodedStrong Y Z F f p) (decodedStrong Y Z G g q) :=
  StrongTrans.isoMk (F := Y.toPseudofunctor') (G := Z.toPseudofunctor') (η := decodedStrong Y Z F f p) (θ := decodedStrong Y Z G g q) (fun A => Cat.Hom.isoMk (component Y Z F G f g i h A.as.unop))
    (fun a => (modification Y Z F G f g i h p q).naturality a)
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {Y Z : PackedCuts.Psh.{u,max u v,u,v} B} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') {i j : Nat} (r : Map S i j)
noncomputable def blockStrong (n : Nat) := decodedStrong _ _ (blockTotal S a n) (blockOver S a n) (blockPres S a n)
theorem blockOne : blockStrong (S := S) a 1 = layerStrong S a := rfl
noncomputable def weakOperationIso (h : gradeCart r) :=
  invertibleMod _ _ (left a r) (right a r) (leftOver a r) (rightOver a r) (operationSquare a r) (operationBase a r)
    (fun f p => blockPres S a j _ (globalPres Y r h f p)) (fun f p => globalPres Z r h _ (blockPres S a i f p))
end ContextualComposition.GrothendieckStep.ContextadAmbientPayload
