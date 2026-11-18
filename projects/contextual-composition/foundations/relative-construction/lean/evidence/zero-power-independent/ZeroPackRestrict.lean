import ContextualComposition.ZeroPower
open CategoryTheory CategoryTheory.Functor Opposite
namespace ContextualComposition.GrothendieckStep.ZeroPower
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (S : P.Split) (Y : Bᵒᵖ ⥤ Cat.{v,u}) (A : B)
example (x : weighted Y A) : (packedEquiv S Y A).functor.obj ⟨0,x⟩ = ⟨0,(eval Y A).obj x⟩ := rfl
example (n : Nat) (x : Total Y (SpanPayload.Power.nativeEndpoint S n A)) : (packedEquiv S Y A).functor.obj ⟨n+1,x⟩ = ⟨n+1,(FibreValue.eval S Y n A).obj x⟩ := rfl
end ContextualComposition.GrothendieckStep.ZeroPower
