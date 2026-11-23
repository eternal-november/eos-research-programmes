module

public import ContextualComposition.DirectedStateDiagramMap

/-! Changing the state category maps its actual arrows and the directed slides they label. Boundary identifications come from the state functor's identity and composition laws. -/

@[expose] public section
namespace ContextualComposition.DirectedStateReindex

open CategoryTheory Opposite DirectedStateBalance DirectedStateDiagramMap DirectedStateNativeFaithfulness DirectedStateIntertwiners
universe u v u' v' w d
variable {S : Type u} [Category.{v} S] {T : Type u'} [Category.{v'} T]
  (J : S ⥤ T) (G : Tᵒᵖ × T ⥤ Cat.{w,d})
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev pull := (J.op.prod J) ⋙ G

theorem pre {i j : S} (h : i ⟶ j) (s : S) :
    action (strict (pull J G)) h (𝟙 s) = action (strict G) (J.map h) (𝟙 (J.obj s)) :=
  congrArg (action (strict G) (J.map h)) (J.map_id s)

theorem post (s : S) {i j : S} (h : i ⟶ j) :
    action (strict (pull J G)) (𝟙 s) h = action (strict G) (𝟙 (J.obj s)) (J.map h) :=
  congrArg (fun f => action (strict G) f (J.map h)) (J.map_id s)

def liftSlide {i j : S} (h : i ⟶ j) (x : atPair (strict (pull J G)) j i) :
    (insertion (strict G) (J.obj i)).obj ((action (strict (pull J G)) h (𝟙 i)).obj x) ⟶
    (insertion (strict G) (J.obj j)).obj ((action (strict (pull J G)) (𝟙 j) h).obj x) :=
  eqToHom (congrArg (insertion (strict G) _).obj (Functor.congr_obj (pre J G h _) x)) ≫
    (slide (strict G) (J.map h)).app x ≫ eqToHom (congrArg (insertion (strict G) _).obj (Functor.congr_obj (post J G _ h) x).symm)

theorem projected {i j : S} (h : i ⟶ j) (x : atPair (strict (pull J G)) j i) :
    Conjugate (liftSlide J G h x) ((slide (strict G) (J.map h)).app x) :=
  (Conjugate.trimLeft _ ⟨_,rfl⟩).trans (Conjugate.trimRight _ ⟨_,rfl⟩)

theorem slide_change_state {A : Type*} [Category* A] (B : Diagram A) {i j : A} {h g : i ⟶ j}
    (e : h=g) (x : atPair B j i) : Conjugate ((slide B h).app x) ((slide B g).app x) := by subst g; exact Conjugate.refl _

private theorem same_id {A : Type*} [Category* A] {a b : A} {f : a ⟶ a} (h : Conjugate f (𝟙 b)) : f=𝟙 a := by
  obtain ⟨rfl,_,e⟩ := h; simpa only [eqToHom_refl,Category.id_comp,Category.comp_id] using e

def data : DirectedStateBalance.Cocone (strict (pull J G)) (Balance (strict G)) where
  fiber i := insertion (strict G) (J.obj i)
  bal {i j} h := {
    app := liftSlide J G h
    naturality := by
      intro x y f
      have a := comp_conjugate (map_conjugate (insertion (strict G) _) (Conjugate.actions (pre J G h i) f)) (projected J G h y)
      have b := comp_conjugate (projected J G h x) (map_conjugate (insertion (strict G) _) (Conjugate.actions (post J G j h) f))
      exact (a.trans (((slide (strict G) (J.map h)).naturality f) ▸ b.symm)).eq }
  unit {i} x := by
    have h := (projected J G (𝟙 i) x).trans (slide_change_state (strict G) (J.map_id i) x)
    have e : (slide (strict G) (𝟙 (J.obj i))).app x = 𝟙 _ := (restrict (𝟭 (Balance (strict G)))).unit x
    rw [e] at h
    exact same_id h
  comp {i j k} h g x := by
    have left := (projected J G (h ≫ g) x).trans (slide_change_state (strict G) (J.map_comp h g) x)
    have target := (restrict (𝟭 (Balance (strict G)))).comp (J.map h) (J.map g) x
    obtain ⟨u,source⟩ := trim ((structural_pre (pull J G) h g x).map (insertion (strict G) _))
      ((structural_middle (pull J G) h g x).map (insertion (strict G) _))
      ((structural_post (pull J G) h g x).map (insertion (strict G) _))
      (liftSlide J G h ((action (strict (pull J G)) g (𝟙 i)).obj x)) (liftSlide J G g ((action (strict (pull J G)) (𝟙 k) h).obj x))
    obtain ⟨v,dest⟩ := trim ((structural_pre G (J.map h) (J.map g) x).map (insertion (strict G) _))
      ((structural_middle G (J.map h) (J.map g) x).map (insertion (strict G) _))
      ((structural_post G (J.map h) (J.map g) x).map (insertion (strict G) _))
      ((slide (strict G) (J.map h)).app ((action (strict G) (J.map g) (𝟙 (J.obj i))).obj x))
      ((slide (strict G) (J.map g)).app ((action (strict G) (𝟙 (J.obj k)) (J.map h)).obj x))
    have a := (projected J G h _).trans (equal_args (slide (strict G) (J.map h)) (Functor.congr_obj (pre J G g i) x))
    have b := (projected J G g _).trans (equal_args (slide (strict G) (J.map g)) (Functor.congr_obj (post J G k h) x))
    exact (left.trans ((target ▸ dest).trans ((middle_splice a b u v).symm.trans source.symm))).eq

def reindex : Balance (strict (pull J G)) ⥤ Balance (strict G) := (data J G).descend

theorem reindex_native {i} {x y : atPair (strict (pull J G)) i i} (f : x ⟶ y) :
    (reindex J G).map ((insertion _ i).map f) = (insertion (strict G) _).map f := (data J G).descend_generator (.native f)
theorem reindex_slide {i j} (h : i ⟶ j) (x : atPair (strict (pull J G)) j i) :
    (reindex J G).map ((slide _ h).app x) = liftSlide J G h x := (data J G).descend_generator (.slide h x)

end ContextualComposition.DirectedStateReindex
