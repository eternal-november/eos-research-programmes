module
public import ContextualComposition.CoproductSpan
@[expose] public section
namespace ContextualComposition.GrothendieckStep.SumChange
open CategoryTheory CategoryTheory.Functor Opposite CoproductSpan
universe i b w u v
def inverseSquare {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (L : C ≌ D) (M : E ≌ F) {s : C ⥤ E} {t : D ⥤ F} (h : L.functor ⋙ t ≅ s ⋙ M.functor) :
    L.inverse ⋙ s ≅ t ⋙ M.inverse :=
  Iso.inverseCompIso (G := L) (Iso.compInverseIso (H := M) h).symm
namespace Tagged
universe a c e f g h j k
variable {I : Type i} {C : I → Type a} {D : I → Type c} {E : I → Type e} {F : I → Type f}
  [∀ n, Category.{g} (C n)] [∀ n, Category.{h} (D n)] [∀ n, Category.{j} (E n)] [∀ n, Category.{k} (F n)]
def square (p : ∀ n, C n ⥤ D n) (q : ∀ n, E n ⥤ F n) (s : ∀ n, C n ⥤ E n)
    (t : ∀ n, D n ⥤ F n) (cell : ∀ n, p n ⋙ t n ≅ s n ⋙ q n) :
    ZeroPower.Sum.map p ⋙ ZeroPower.Sum.map t ≅ ZeroPower.Sum.map s ⋙ ZeroPower.Sum.map q :=
  NatIso.ofComponents (fun ⟨n,x⟩ => (Sigma.incl n).mapIso ((cell n).app x)) (by
    rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact congrArg Sigma.SigmaHom.mk ((cell n).hom.naturality f))
end Tagged
variable {B : Type b} [Category.{w} B] {Q : Endpoints.{b,w,b,w} B} (R : Q.Split)
variable {Y Z : Bᵒᵖ ⥤ Cat.{w,b}} (T : Y ⟶ Z)
open CoproductSpan.All
abbrev leaf (A : B) (n : Nat) := ChainPayload.fibreMap T (leg (src R) (dst R) A n)
abbrev target (A : B) (n : Nat) := ((ChainPayload.layerMap T R n).app (op A)).toFunctor
theorem componentPayload (A : B) : (n : Nat) →
    (component R Y A n).functor ⋙ target R T A n = leaf R T A n ⋙ (component R Z A n).functor
  | 0 => (ZeroPower.payloadSquare T A).symm
  | n+1 => (EvalPayload.evalSquare T R n A).symm
noncomputable def taggedPayload (A : B) :=
  Tagged.square (fun n => (component R Y A n).functor) (fun n => (component R Z A n).functor)
    (leaf R T A) (target R T A) (fun n => eqToIso (componentPayload R T A n))
noncomputable def inversePayload (A : B) :=
  inverseSquare (compare (src R) (dst R) A Y).asEquivalence (compare (src R) (dst R) A Z).asEquivalence
    (eqToIso (compare_payload (src R) (dst R) A Y T))
noncomputable def evaluationPayload (A : B) :
    (evaluation R Y A).functor ⋙ ZeroPower.Sum.map (target R T A) ≅
      ChainPayload.fibreMap T (wholeLeg (src R) (dst R) A) ⋙ (evaluation R Z A).functor :=
  SpanPayload.pasteIso (inversePayload R T A) (taggedPayload R T A)

variable (Y)
noncomputable def leafPull {A D : B} (a : A ⟶ D) : (n : Nat) →
    Total Y (leg (src R) (dst R) D n) ⥤ Total Y (leg (src R) (dst R) A n)
  | 0 => ZeroPower.pull Y a
  | n+1 => NativeCleavage.nativeReindex Y R n a
noncomputable def componentBase {A D : B} (a : A ⟶ D) : (n : Nat) →
    leafPull R Y a n ⋙ (component R Y A n).functor ≅
      (component R Y D n).functor ⋙ ((Iterates.layer Q R Y n).map a.op).toFunctor
  | 0 => ZeroPower.baseSquare Y a
  | n+1 => FibreValue.evalSquare R Y n a
noncomputable def taggedBase {A D : B} (a : A ⟶ D) :
    ZeroPower.Sum.map (leafPull R Y a) ⋙ (ZeroPower.Sum.equiv (component R Y A)).functor ≅
      (ZeroPower.Sum.equiv (component R Y D)).functor ⋙ Iterates.packedMap Q R Y a.op :=
  Tagged.square _ _ _ _ (componentBase R Y a)
end ContextualComposition.GrothendieckStep.SumChange
