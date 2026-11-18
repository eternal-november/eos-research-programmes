module
public import ContextualComposition.FinalCube
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ZeroPower
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage
universe b w u v
variable {B : Type b} [Category.{w} B] (Y : Bᵒᵖ ⥤ Cat.{v,u})
/-- The source fibre of the identity span, weighted by its actual destination leg. -/
abbrev endpoint (A : B) := FibreTotal.endpoint (𝟭 B) (𝟭 B) A
abbrev weighted (A : B) := Total Y (endpoint A)
def eval (A : B) : weighted Y A ⥤ Y.obj (op A) :=
  FibreTotal.into Y (𝟭 B) (𝟭 B) A ⋙ FibreValue.value Y A
instance evalEquivalence (A : B) : (eval Y A).IsEquivalence :=
  @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ (FibreTotal.intoEquivalence Y _ _ A) (FibreValue.valueEquiv Y A).isEquivalence_functor
noncomputable def pull {A D : B} (a : A ⟶ D) : weighted Y D ⥤ weighted Y A :=
  FibreTotal.into Y (𝟭 B) (𝟭 B) D ⋙ Reindex.functor (FibreValue.choice Y) a ⋙ FibreTotal.out Y (𝟭 B) (𝟭 B) A
noncomputable def baseSquare {A D : B} (a : A ⟶ D) :
    pull Y a ⋙ eval Y A ≅ eval Y D ⋙ (Y.map a.op).toFunctor :=
  isoWhiskerLeft (FibreTotal.into Y (𝟭 B) (𝟭 B) D) (FibreValue.valueSquare Y a)
variable {Y} {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
theorem payloadSquare (A : B) :
    ChainPayload.fibreMap T (endpoint A) ⋙ eval Z A = eval Y A ⋙ (T.app (op A)).toFunctor :=
  EvalPayload.pasteEq _ _ _ _ _ _ _ (EvalPayload.intoSquare T (𝟭 B) (𝟭 B) A) (EvalPayload.valueSquare T A)

namespace Sum
universe i x y s t
variable {I : Type i} {C : I → Type x} {D : I → Type y}
  [∀ n, Category.{s} (C n)] [∀ n, Category.{t} (D n)]
def map (F : ∀ n, C n ⥤ D n) : (Σ n, C n) ⥤ (Σ n, D n) :=
  Sigma.desc fun n => F n ⋙ Sigma.incl n
def equiv (E : ∀ n, C n ≌ D n) : (Σ n, C n) ≌ (Σ n, D n) where
  functor := map fun n => (E n).functor
  inverse := map fun n => (E n).inverse
  unitIso := NatIso.ofComponents (fun ⟨n,x⟩ => (Sigma.incl n).mapIso ((E n).unitIso.app x)) (by
    rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    exact congrArg Sigma.SigmaHom.mk ((E n).unitIso.hom.naturality f))
  counitIso := NatIso.ofComponents (fun ⟨n,x⟩ => (Sigma.incl n).mapIso ((E n).counitIso.app x)) (by
    rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    exact congrArg Sigma.SigmaHom.mk ((E n).counitIso.hom.naturality f))
  functor_unitIso_comp := by
    rintro ⟨n,x⟩
    exact congrArg Sigma.SigmaHom.mk ((E n).functor_unitIso_comp x)
end Sum

open SpanPayload.Power
variable {P : Endpoints.{b,w,u,v} B} (S : P.Split) (Y : Bᵒᵖ ⥤ Cat.{v,u})
def nativeLayer (A : B) : Nat → Cat.{max w v,max b u}
  | 0 => Cat.of (weighted Y A)
  | n+1 => Cat.of (Total Y (nativeEndpoint S n A))
noncomputable def layerEquiv (A : B) : (n : Nat) → (nativeLayer S Y A n) ≌ (Iterates.layer P S Y n).obj (op A)
  | 0 => (eval Y A).asEquivalence
  | n+1 => (FibreValue.eval S Y n A).asEquivalence
noncomputable def packedEquiv (A : B) : (Σ n, nativeLayer S Y A n) ≌ Iterates.Packed P S Y (op A) :=
  Sum.equiv (layerEquiv S Y A)
end ContextualComposition.GrothendieckStep.ZeroPower
