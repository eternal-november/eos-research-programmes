module
public import ContextualComposition.RelativeTensorCommaTransport
public import ContextualComposition.RelativeTensorGeneratorComparison

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Opposite Factorization
open scoped CategoryTheory.Bicategory
universe vK vL vC uK uL uC
variable {K K' : Type uK} {L L' : Type uL} {C : Type uC}
variable [Category.{vK} K] [Category.{vK} K'] [Category.{vL} L] [Category.{vL} L'] [Category.{vC} C]
variable {e : K ⥤ C} {d : L ⥤ C} {e' : K' ⥤ C} {d' : L' ⥤ C}
set_option backward.isDefEq.respectTransparency false

theorem decode_balance_grades {i j : C} (u : i ⟶ j) (x : CostructuredArrow e i) (y : StructuredArrow j d) :
    ((decode e d).map (balancing (input e) (output d) u x y).hom).left = 𝟙 x.left ∧
    ((decode e d).map (balancing (input e) (output d) u x y).hom).right = 𝟙 y.right := by
  have h := ((commaPresentation e d _).functor.obj (𝟭 _)).extend_generator
    (Edge.balance (F := input e) (G := output d) u x y)
  exact ⟨congrArg CommaMorphism.left h, congrArg CommaMorphism.right h⟩

variable (T : Endpoint.Data e d e' d')

noncomputable def normalizationComponent (s : Carrier e d) :
    (tensorTransport T ⋙ decode e' d').obj s ≅ (decode e d ⋙ Endpoint.commaFunctor T).obj s :=
  Comma.isoMk (Iso.refl _) (Iso.refl _) (by
    obtain ⟨⟨i,x,y⟩⟩ := s
    change e'.map (𝟙 _) ≫ (T.inputLift.app x.left ≫ (x.hom ≫ y.hom) ≫ T.outputLift.app y.right) =
      ((T.inputLift.app x.left ≫ x.hom) ≫ (y.hom ≫ T.outputLift.app y.right)) ≫ d'.map (𝟙 _)
    simp [Category.assoc])

theorem transported_native {i : C} {x x' : CostructuredArrow e i} {y y' : StructuredArrow i d}
    (α : x ⟶ x') (β : y ⟶ y') :
    let f := (tensorTransport T ⋙ decode e' d').map ((insertion (input e) (output d) i).map (productMap α β))
    f.left = T.input.map α.left ∧ f.right = T.output.map β.right := by
  dsimp only [Functor.comp_map,tensorTransport]
  rw [mapBoth_native]
  exact decode_grades e' d' ((inputAt T i).map α) ((outputAt T i).map β)

theorem transported_balance {i j : C} (u : i ⟶ j) (x : CostructuredArrow e i) (y : StructuredArrow j d) :
    let f := (tensorTransport T ⋙ decode e' d').map (balancing (input e) (output d) u x y).hom
    f.left = 𝟙 (T.input.obj x.left) ∧ f.right = 𝟙 (T.output.obj y.right) := by
  dsimp only [Functor.comp_map,tensorTransport]
  rw [mapBoth_balance, Functor.map_comp, Functor.map_comp]
  let p := First.port (inputComparison T) u x
  let q := Second.port (outputComparison T) u y
  have h₁ := decode_grades e' d' (𝟙 ((inputAt T i).obj x)) q.hom
  have h₂ := decode_balance_grades u ((inputAt T i).obj x) ((outputAt T j).obj y)
  have h₃ := decode_grades e' d' p.hom (𝟙 ((outputAt T j).obj y))
  constructor
  · change _ ≫ _ ≫ _ = _
    refine (congrArg₂ (· ≫ ·) h₁.1 (congrArg₂ (· ≫ ·) h₂.1 h₃.1)).trans ?_
    exact (Category.id_comp _).trans (Category.id_comp _)
  · change _ ≫ _ ≫ _ = _
    refine (congrArg₂ (· ≫ ·) h₁.2 (congrArg₂ (· ≫ ·) h₂.2 h₃.2)).trans ?_
    exact (Category.id_comp _).trans (Category.id_comp _)

/-- The generic tensor changes both comma factors via their strong endpoint maps, and its normalization commutes with the original two-sided native comma action. -/
noncomputable def normalizationSquare :
    tensorTransport T ⋙ decode e' d' ≅ decode e d ⋙ Endpoint.commaFunctor T :=
  isoOfGenerators (normalizationComponent T) (by
    intro i x x' y y' α β
    have h := transported_native T α β
    have k := decode_grades e d α β
    apply Comma.hom_ext
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ T.input.map _
      erw [Category.comp_id,Category.id_comp,h.1,k.1]
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ T.output.map _
      erw [Category.comp_id,Category.id_comp,h.2,k.2]) (by
    intro i j u x y
    have h := transported_balance T u x y
    have k := decode_balance_grades u x y
    apply Comma.hom_ext
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ T.input.map _
      erw [Category.comp_id,Category.id_comp,h.1,k.1,Functor.map_id]
      rfl
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ T.output.map _
      erw [Category.comp_id,Category.id_comp,h.2,k.2,Functor.map_id]
      rfl)

end ContextualComposition.RelativeTensor.Presented
