module

public import ContextualComposition.DirectedStateSlideInterchange

/-! A state isomorphism induces an invertible slide for an arbitrary weak diagram. Its two splittings use the two separate state inverse equations. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.DirectedStateIsoSlides

open CategoryTheory Opposite DirectedStateBalance DirectedStateSlideInterchange
universe u v w d
variable {S : Type u} [Category.{v} S] (F : Diagram.{v,u,w,d} S) {i j k : S}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def LeftInverse {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) : Prop := ∃ r, f ≫ r = 𝟙 X
def RightInverse {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) : Prop := ∃ r, r ≫ f = 𝟙 Y

theorem splits {C : Type*} [Category* C] {A B D E X Y : C}
    (a : A ≅ B) (f : B ⟶ D) (m : D ≅ E) (g : E ⟶ X) (b : X ≅ Y)
    (t : A ≅ Y) (eq : a.hom ≫ f ≫ m.hom ≫ g ≫ b.hom = t.hom) :
    LeftInverse f ∧ RightInverse g := by
  constructor
  · refine ⟨m.hom ≫ g ≫ b.hom ≫ t.inv ≫ a.hom,?_⟩
    apply (cancel_epi a.hom).mp
    simpa [Category.assoc] using congrArg (· ≫ t.inv ≫ a.hom) eq
  · refine ⟨b.hom ≫ t.inv ≫ a.hom ≫ f ≫ m.hom,?_⟩
    apply (cancel_mono b.hom).mp
    simp [Category.assoc,eq]

theorem composed (h : i ⟶ j) (g : j ⟶ k) (x : atPair F k i) [IsIso ((slide F (h≫g)).app x)] :
    LeftInverse ((slide F h).app ((action F g (𝟙 i)).obj x)) ∧
    RightInverse ((slide F g).app ((action F (𝟙 k) h).obj x)) :=
  splits ((insertion F i).mapIso ((preComp F h g).app x)) _
    ((insertion F j).mapIso ((middle F h g).app x)) _ ((insertion F k).mapIso ((postComp F h g).app x).symm)
    (asIso ((slide F (h≫g)).app x)) (expand_slide F h g x)

theorem transport_left {C D : Type*} [Category* C] [Category* D] {P Q : C ⥤ D}
    (α : P ⟶ Q) {x y : C} (e : y ≅ x) (l : LeftInverse (α.app y)) : LeftInverse (α.app x) := by
  obtain ⟨r,hr⟩ := l
  refine ⟨Q.map e.inv ≫ r ≫ P.map e.hom,?_⟩
  rw [← α.naturality_assoc,← Category.assoc (α.app y) r,hr,Category.id_comp,← P.map_comp,e.inv_hom_id,P.map_id]

theorem transport_right {C D : Type*} [Category* C] [Category* D] {P Q : C ⥤ D}
    (α : P ⟶ Q) {x y : C} (e : y ≅ x) (l : RightInverse (α.app y)) : RightInverse (α.app x) := by
  obtain ⟨r,hr⟩ := l
  refine ⟨Q.map e.inv ≫ r ≫ P.map e.hom,?_⟩
  simp only [Category.assoc,α.naturality]
  rw [← Category.assoc r,hr,Category.id_comp,← Q.map_comp,e.inv_hom_id,Q.map_id]

def idAction (i j : S) : action F (𝟙 i) (𝟙 j) ≅ 𝟭 _ := Cat.Hom.toNatIso (F.mapId ⟨(op i,j)⟩)

theorem state_iso (h : i ≅ j) (x : atPair F j i) : IsIso ((slide F h.hom).app x) := by
  have isoId (s : S) (z : atPair F s s) : IsIso ((slide F (𝟙 s)).app z) := by
    have eq : (slide F (𝟙 s)).app z = 𝟙 _ := (restrict (𝟭 _)).unit z
    rw [eq]; infer_instance
  let src := (action F h.hom (𝟙 i)).obj x
  let dst := (action F (𝟙 j) h.hom).obj x
  have h₁ : IsIso ((slide F (h.hom≫h.inv)).app src) := by rw [h.hom_inv_id]; exact isoId _ _
  have h₂ : IsIso ((slide F (h.inv≫h.hom)).app dst) := by rw [h.inv_hom_id]; exact isoId _ _
  let pre : (action F h.inv (𝟙 i)).obj src ≅ x :=
    ((actionComp F h.hom h.inv (𝟙 i) (𝟙 i)).app x).symm ≪≫
      (eqToIso (by simp) : (action F (h.inv ≫ h.hom) (𝟙 i ≫ 𝟙 i)).obj x ≅ (action F (𝟙 j) (𝟙 i)).obj x) ≪≫ (idAction F j i).app x
  let post : (action F (𝟙 j) h.inv).obj dst ≅ x :=
    ((actionComp F (𝟙 j) (𝟙 j) h.hom h.inv).app x).symm ≪≫
      (eqToIso (by simp) : (action F (𝟙 j ≫ 𝟙 j) (h.hom ≫ h.inv)).obj x ≅ (action F (𝟙 j) (𝟙 i)).obj x) ≪≫ (idAction F j i).app x
  obtain ⟨l,hl⟩ := transport_left (slide F h.hom) pre (composed F h.hom h.inv src).1
  obtain ⟨r,hr⟩ := transport_right (slide F h.hom) post (composed F h.inv h.hom dst).2
  have lr : l=r := (Category.id_comp l).symm.trans
    ((congrArg (· ≫ l) hr.symm).trans ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hl).trans (Category.comp_id _))))
  exact ⟨l,hl,lr ▸ hr⟩

end ContextualComposition.DirectedStateIsoSlides
