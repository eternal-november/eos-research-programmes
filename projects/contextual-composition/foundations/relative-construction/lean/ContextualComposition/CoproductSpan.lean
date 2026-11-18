module
public import ContextualComposition.ZeroPower
@[expose] public section
namespace ContextualComposition.GrothendieckStep.CoproductSpan
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage
universe i k j b w u v
variable {I : Type i} {B : Type b} [Category.{w} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (A : B) (Y : Bᵒᵖ ⥤ Cat.{v,u})
abbrev fibreCat (t : I) := (p t).Fiber A
def incl (t : I) : fibreCat p A t ⥤ (Sigma.desc p).Fiber A :=
  SpanPayload.fibreFunctor (Sigma.incl t) (Sigma.desc p) rfl A
def pack : (Σ t, fibreCat p A t) ⥤ (Sigma.desc p).Fiber A := Sigma.desc (incl p A)
theorem obj_surj : Function.Surjective (pack p A).obj := by
  rintro ⟨⟨t,x⟩,hx⟩; exact ⟨⟨t,x,hx⟩,rfl⟩
def unpackHom {x y : Σ t, fibreCat p A t} (f : (pack p A).obj x ⟶ (pack p A).obj y) : x ⟶ y := by
  rcases x with ⟨t,x,hx⟩; rcases y with ⟨s,y,hy⟩; rcases f with ⟨f,hf⟩
  change Sigma.SigmaHom ⟨t,x⟩ ⟨s,y⟩ at f
  cases f with | mk g =>
    letI : (Sigma.desc p).IsHomLift (𝟙 A) (Sigma.SigmaHom.mk g) := hf
    exact Sigma.SigmaHom.mk (⟨g,IsHomLift.of_fac' (p _) _ g hx hy (IsHomLift.fac' (Sigma.desc p) _ (Sigma.SigmaHom.mk g))⟩)
theorem map_unpack {x y : Σ t, fibreCat p A t} (f : (pack p A).obj x ⟶ (pack p A).obj y) :
    (pack p A).map (unpackHom p A f) = f := by
  rcases x with ⟨t,x,hx⟩; rcases y with ⟨s,y,hy⟩; rcases f with ⟨f,hf⟩
  change Sigma.SigmaHom ⟨t,x⟩ ⟨s,y⟩ at f
  cases f; rfl
theorem unpack_map {x y : Σ t, fibreCat p A t} (f : x ⟶ y) :
    unpackHom p A ((pack p A).map f) = f := by cases f; rfl
instance packFull : (pack p A).Full where map_surjective f := ⟨_,map_unpack p A f⟩
instance packFaithful : (pack p A).Faithful where
  map_injective h := (unpack_map p A _).symm.trans ((congrArg (unpackHom p A) h).trans (unpack_map p A _))
instance packEquivalence : (pack p A).IsEquivalence where
  essSurj := ⟨fun y => by obtain ⟨x,h⟩ := obj_surj p A y; exact ⟨x,⟨eqToIso h⟩⟩⟩
def leg (t : I) := FibreTotal.endpoint (d t) (p t) A
def wholeLeg := FibreTotal.endpoint (Sigma.desc d) (Sigma.desc p) A
theorem over : pack p A ⋙ wholeLeg p d A = Sigma.desc (leg p d A) := by
  fapply Functor.ext
  · rintro ⟨t,x⟩; rfl
  · rintro ⟨t,x⟩ ⟨_,y⟩ ⟨f⟩; change _ = 𝟙 _ ≫ (leg p d A t).map f ≫ 𝟙 _; rw [Category.id_comp]; exact (Category.comp_id _).symm
def weightedPack : Total Y (Sigma.desc (leg p d A)) ⥤ Total Y (wholeLeg p d A) :=
  SpanPayload.totalMap Y (pack p A) _ (over p d A)
instance weightedEquivalence : (weightedPack p d A Y).IsEquivalence :=
  SpanPayload.totalIsEquivalence _ _ _ _
theorem payloadSquare {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z) :
    weightedPack p d A Y ⋙ ChainPayload.fibreMap T _ =
      ChainPayload.fibreMap T _ ⋙ weightedPack p d A Z :=
  SpanPayload.total_payload_natural _ _ _ T
namespace Distribute
variable (e : ∀ t, K t ⥤ B)
def tag (t : I) : Total Y (e t) ⥤ Total Y (Sigma.desc e) :=
  SpanPayload.totalMap Y (Sigma.incl t) _ rfl
def gather : (Σ t, Total Y (e t)) ⥤ Total Y (Sigma.desc e) := Sigma.desc (tag Y e)
theorem obj_surj : Function.Surjective (gather Y e).obj := by
  rintro ⟨⟨⟨t,k⟩,x⟩⟩
  exact ⟨⟨t,pair Y (e t) k x.unop⟩,rfl⟩
def splitHom {x y : Σ t, Total Y (e t)} (f : (gather Y e).obj x ⟶ (gather Y e).obj y) : x ⟶ y := by
  rcases x with ⟨t,⟨⟨k,u⟩⟩⟩; rcases y with ⟨s,⟨⟨l,v⟩⟩⟩
  obtain ⟨g,m⟩ := homEquiv _ _ f
  change Sigma.SigmaHom (C := K) ⟨t,k.unop⟩ ⟨s,l.unop⟩ at g
  cases g with | mk h => exact Sigma.SigmaHom.mk (arrow h m)
theorem gather_split {x y : Σ t, Total Y (e t)} (f : (gather Y e).obj x ⟶ (gather Y e).obj y) :
    (gather Y e).map (splitHom Y e f) = f := by
  rcases x with ⟨t,⟨⟨k,u⟩⟩⟩; rcases y with ⟨s,⟨⟨l,v⟩⟩⟩
  obtain ⟨⟨g,m⟩,rfl⟩ := (homEquiv _ _).symm.surjective f
  change Sigma.SigmaHom (C := K) ⟨t,k.unop⟩ ⟨s,l.unop⟩ at g; cases g; rfl
theorem split_gather {x y : Σ t, Total Y (e t)} (f : x ⟶ y) :
    splitHom Y e ((gather Y e).map f) = f := by cases f; rfl
instance full : (gather Y e).Full where map_surjective f := ⟨_,gather_split Y e f⟩
instance faithful : (gather Y e).Faithful where
  map_injective h := (split_gather Y e _).symm.trans ((congrArg (splitHom Y e) h).trans (split_gather Y e _))
instance equivalence : (gather Y e).IsEquivalence where
  essSurj := ⟨fun y => by obtain ⟨x,h⟩ := obj_surj Y e y; exact ⟨x,⟨eqToIso h⟩⟩⟩
end Distribute
def compare : (Σ t, Total Y (leg p d A t)) ⥤ Total Y (wholeLeg p d A) :=
  Distribute.gather Y _ ⋙ weightedPack p d A Y
instance compareEquivalence : (compare p d A Y).IsEquivalence := by unfold compare; infer_instance
theorem gather_payload {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z) (e : ∀ t, K t ⥤ B) :
    Distribute.gather Y e ⋙ ChainPayload.fibreMap T _ =
      ZeroPower.Sum.map (fun t => ChainPayload.fibreMap T (e t)) ⋙ Distribute.gather Z e := by
  fapply Functor.ext
  · rintro ⟨t,x⟩; rfl
  · rintro ⟨t,x⟩ ⟨_,y⟩ ⟨f⟩
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    rw [Category.id_comp]; exact (Category.comp_id _).symm

theorem compare_payload {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z) :
    compare p d A Y ⋙ ChainPayload.fibreMap T _ =
      ZeroPower.Sum.map (fun t => ChainPayload.fibreMap T (leg p d A t)) ⋙ compare p d A Z := by
  exact (EvalPayload.pasteEq _ _ _ _ _ _ _ (gather_payload Y T (leg p d A)).symm (payloadSquare p d A Y T).symm).symm

open SpanApex
variable {P : Endpoints.{b,w,u,v} B} (S : P.Split)
noncomputable def positive (A : B) :
    Total Y (wholeLeg (fun n => (positivePowers P S n).source) (fun n => (positivePowers P S n).dest) A) ≌
      (Σ n, (Iterates.layer P S Y (n+1)).obj (op A)) :=
  (compare (fun n => (positivePowers P S n).source) (fun n => (positivePowers P S n).dest) A Y).asEquivalence.symm.trans
    (ZeroPower.Sum.equiv fun n => (FibreValue.eval S Y n A).asEquivalence)

/- With common base/grade sizes the identity apex and the positive apices form one
honest homogeneous family, without any universe-changing equivalence. -/
namespace All
variable {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (X : Bᵒᵖ ⥤ Cat.{w,b})
def span : Nat → TwoLegs.{b,w,b,w} B
  | 0 => ⟨Cat.of B,𝟭 B,𝟭 B⟩
  | n+1 => positivePowers Q R n
abbrev src (n : Nat) := (span R n).source
abbrev dst (n : Nat) := (span R n).dest
noncomputable def component (A : B) : (n : Nat) →
    Total X (leg (src R) (dst R) A n) ≌ (Iterates.layer Q R X n).obj (op A)
  | 0 => (ZeroPower.eval X A).asEquivalence
  | n+1 => (FibreValue.eval R X n A).asEquivalence
noncomputable def evaluation (A : B) :
    Total X (wholeLeg (src R) (dst R) A) ≌ Iterates.Packed Q R X (op A) :=
  (compare (src R) (dst R) A X).asEquivalence.symm.trans (ZeroPower.Sum.equiv (component R X A))
end All
end ContextualComposition.GrothendieckStep.CoproductSpan
