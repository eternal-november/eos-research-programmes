import ContextualComposition.TelescopeInterpretation
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedFree
namespace IndependentTargetProbe
set_option backward.isDefEq.respectTransparency false
abbrev B := Discrete Unit
abbrev b : B := ⟨()⟩
abbrev C := Bᵒᵖ ⥤ Cat.{0,0}
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of B)
  extend _ := 𝟭 B
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def toFibre (Y : C) (A : B) : Total Y (𝟭 B) ⥤ (FibreValue.proj Y).Fiber A where
  obj x := ⟨x,Subsingleton.elim _ _⟩
  map f := ⟨f,IsHomLift.of_fac' _ _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
abbrev collapse (Y : C) (A : B) := toFibre Y A ⋙ FibreValue.value Y A
def atValue (Y : C) : (step S).obj Y ⟶ Y where
  app A := (collapse Y A.unop).toCatHom
  naturality A D f := by
    obtain rfl : A = D := Subsingleton.elim _ _
    obtain rfl : f = 𝟙 A := Subsingleton.elim _ _
    simp only [Functor.map_id,Category.id_comp,Category.comp_id]
abbrev M := CategoryTheory.Monad.id C
def q : step S ⟶ M.toFunctor where
  app := atValue
  naturality X Y f := by
    apply NatTrans.ext; funext A; apply congrArg Functor.toCatHom
    apply EvalPayload.pasteEq (toFibre X A.unop) (FibreValue.value X A.unop) (ChainPayload.fibreMap f (𝟭 B))
      (PayloadLift.action f (𝟭 B) (𝟭 B) A.unop) (f.app A).toFunctor (toFibre Y A.unop) (FibreValue.value Y A.unop)
    · apply EvalPayload.cancelInclusion; rfl
    · exact (EvalPayload.valueSquare f A.unop)
abbrev α := TelescopeInterpretation.extend S M q
theorem atZero (Y : C) : inc S Y 0 ≫ α.app Y = 𝟙 Y := α.app_η Y
theorem atOne (Y : C) : inc S Y 1 ≫ α.app Y = atValue Y := TelescopeInterpretation.singleton S M q Y
inductive K | pt
instance : Category K where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev Y : C := (Functor.const _).obj (Cat.of K)
abbrev a : K := .pt
def f : a ⟶ a := fun _ => false
def g : a ⟶ a := fun _ => true
abbrev E := ((α.app Y).app (op b)).toFunctor
abbrev I₀ := ((inc S Y 0).app (op b)).toFunctor
abbrev I₁ := ((inc S Y 1).app (op b)).toFunctor
abbrev one := FibreValue.incl Y b
theorem same₀ : I₀ ⋙ E = 𝟭 (Y.obj (op b)) :=
  congrArg Cat.Hom.toFunctor (NatTrans.congr_app (atZero Y) (op b))
theorem same₁ : one ⋙ I₁ ⋙ E = 𝟭 (Y.obj (op b)) := by
  have h := congrArg Cat.Hom.toFunctor (NatTrans.congr_app (atOne Y) (op b))
  change I₁ ⋙ E = collapse Y b at h
  rw [h]
  exact FibreValue.embed_value Y b
example : (one ⋙ I₁ ⋙ E).map f ≠ (one ⋙ I₁ ⋙ E).map g := by
  rw [same₁]
  exact fun h => Bool.noConfusion (congrFun h false)
example : (I₀.obj a).1 ≠ ((one ⋙ I₁).obj a).1 := by decide
theorem endpoints : (I₀ ⋙ E).obj a = (one ⋙ I₁ ⋙ E).obj a := by rw [same₀,same₁]
theorem notFull : ¬ E.Full := by
  intro h
  have targetArrow : E.obj (I₀.obj a) ⟶ E.obj ((one ⋙ I₁).obj a) := eqToHom endpoints
  obtain ⟨t,_⟩ := E.map_surjective targetArrow
  exact (by decide : 0 ≠ 1) (Iterates.length_preserved P S Y t)
end IndependentTargetProbe
