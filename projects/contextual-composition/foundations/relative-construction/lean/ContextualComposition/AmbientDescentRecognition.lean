module
public import ContextualComposition.AmbientBlockCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientDescentRecognition
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite NativeCleavage FibreValue TelescopeSquares
open ContextadModification ContextadAmbientPayload ContextadPayloadModification
set_option backward.isDefEq.respectTransparency false
universe u v
theorem trim {C : Type*} [Category* C] {x y z w : C}
    (p : x ⟶ y) (q : y ⟶ z) (r : z ⟶ w) (h : Pure p) (k : Pure r) : Aligned (p ≫ q ≫ r) q := by
  obtain ⟨rfl,rfl⟩ := h; obtain ⟨rfl,rfl⟩ := k; simp; exact Aligned.refl _
variable {B : Type*} [Category* B] (Y Z : Bᵒᵖ ⥤ Cat.{v,u})
theorem chosen (G : Bᵒᵖ ⥤ Cat.{v,u}) {A D : B} (f : A ⟶ D) (x : (proj G).Fiber D) :
    Aligned (Reindex.lift (choice G) f x) (FibreValue.arrow G f ((value G D).obj x)) := by
  obtain ⟨z,rfl⟩ := obj_surj G D x
  let t := (square G f).hom.app z
  have h := Change.fac (cone G f) (Change.before (embed G D) (Route.ofChoice (choice G) f)) z
  change t.val ≫ _ = FibreValue.arrow G f z at h
  have pure : Pure t.val := by
    change Pure (Fiber.fiberInclusion.map ((square G f).hom.app z))
    exact pureMap Fiber.fiberInclusion ⟨_,squareApp G f z⟩
  let l := Reindex.lift (choice G) f ((embed G D).obj z)
  change Aligned l (FibreValue.arrow G f z)
  have ht : Aligned (t.val ≫ l) l := (NativeCube.ofEq (by rw [Category.comp_id] : t.val ≫ l = t.val ≫ l ≫ 𝟙 _)).trans (trim _ _ _ pure (pureId _))
  exact ht.symm.trans (NativeCube.ofEq h)
variable {F : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)} (h : F ⋙ proj Z = proj Y) (p : Pres F (proj Y) (proj Z))
noncomputable abbrev D := decodedStrong Y Z F h p
theorem decodedMiddle {A E : B} (f : A ⟶ E) (x : Y.obj (op E)) :
    Aligned ((incl Z A).map ((ContextadTotal.valueSquare Y Z F h p f).hom.app x))
        (((ContextadCoherence.middle Y Z F h p f).hom.app ((embed Y E).obj x)).val) := by
  let m := (ContextadCoherence.middle Y Z F h p f).hom.app ((embed Y E).obj x)
  let J := SpanPayload.fibreFunctor F (proj Z) h A
  have k := (NativeCube.functorAlign (value_embed Z A) m).map Fiber.fiberInclusion
  change Aligned ((incl Z A).map ((J ⋙ value Z A).map ((square Y f).hom.app x) ≫
    (value Z A).map m ≫ (valueSquare Z f).hom.app _)) m.val
  rw [Functor.map_comp,Functor.map_comp]
  apply (trim _ _ _ (pureMap _ (pureMap _ ⟨_,squareApp Y f x⟩)) (pureMap _ ⟨_,valueApp Z f _⟩)).trans
  exact k
theorem decodedFac {A E : B} (f : A ⟶ E) (x : Y.obj (op E)) :
    Aligned ((incl Z A).map ((ContextadTotal.valueSquare Y Z F h p f).hom.app x) ≫
      FibreValue.arrow Z f ((ContextadTotal.localValue Y Z F h E).obj x)) (F.map (FibreValue.arrow Y f x)) := by
  let R := Route.ofChoice (choice Y) f
  let Q := Route.ofChoice (choice Z) f
  let z := (embed Y E).obj x
  apply ((decodedMiddle Y Z h p f x).comp (chosen Z f ((SpanPayload.fibreFunctor F _ h E).obj z)).symm).trans
  exact (NativeCube.changeFac F h R Q p z).trans ((chosen Y f z).map F)
end ContextualComposition.GrothendieckStep.AmbientDescentRecognition
