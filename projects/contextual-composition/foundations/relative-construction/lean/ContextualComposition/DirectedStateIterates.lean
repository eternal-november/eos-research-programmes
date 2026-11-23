module

public import ContextualComposition.DirectedStateModifications

/-! Actual iterated contractions of two mixed state coordinates. Native insertions in the inner contraction are natural over the remaining coordinate. -/

@[expose] public section
namespace ContextualComposition.DirectedStateIterates

open CategoryTheory Opposite DirectedStateBalance DirectedStateNativeFaithfulness DirectedStateIntertwiners DirectedStateDiagramMap DirectedStateModifications
universe u
-- Both iterated presentations and the coefficient categories inhabit the same fixed small universe.
variable {S T : Type u} [Category.{u} S] [Category.{u} T]
abbrev Index (S : Type*) := Sᵒᵖ × S
variable (A : Index T ⥤ Index S ⥤ Cat.{u,u})
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev outer := A ⋙ contraction
abbrev Iterated := Balance (strict (outer A))

/-- Insert a fixed T-state on every S-fibre. Naturality is equality on all arrows, including noninvertible native cells. -/
def unitFamily (t : T) : A.obj (op t,t) ⟶ outer A.flip where
  app p := (insertion (strict (A.flip.obj p)) t).toCatHom
  naturality _ _ f := congrArg Functor.toCatHom (insertion_natural (A.flip.map f) t).symm

abbrev row (t : T) : Balance (strict (A.obj (op t,t))) ⥤ Iterated A.flip := map (unitFamily A t)

/-- Sliding a T-state defines a modification over the S diagram. Its naturality is exactly the formula for how a diagram map carries an inner slide. -/
def changeOuter {t t' : T} (h : t ⟶ t') :
    Modification (A.map (pairMap h (𝟙 t)) ≫ unitFamily A t) (A.map (pairMap (𝟙 t') h) ≫ unitFamily A t') where
  cell i j := slide (strict (A.flip.obj (op i,j))) h
  natural {i i' j j'} f g x := by
    let n := A.flip.map (pairMap f g)
    have e := map_slide n h x
    change Conjugate ((slide (strict (A.flip.obj (op i',j'))) h).app ((component n t' t).obj x))
      ((map n).map ((slide (strict (A.flip.obj (op i,j))) h).app x))
    exact ((e ▸ move_conjugate n h x)).symm

/-- The induced T-slide acts on the entire inner contraction, including all its quotient arrows. -/
def outerSlide {t t' : T} (h : t ⟶ t') :
    action (strict (outer A)) h (𝟙 t) ⋙ row A t ⟶ action (strict (outer A)) (𝟙 t') h ⋙ row A t' :=
  eqToHom (map_comp (A.map (pairMap h (𝟙 t))) (unitFamily A t)).symm ≫
  DirectedStateModifications.descend (changeOuter A h) ≫
  eqToHom (map_comp (A.map (pairMap (𝟙 t') h)) (unitFamily A t'))

theorem outerSlide_on_vertex {t t' : T} (h : t ⟶ t') (s : S) (x : (A.obj (op t',t)).obj (op s,s)) :
    Conjugate ((outerSlide A h).app ((insertion (strict (A.obj (op t',t))) s).obj x))
      ((insertion (strict (outer A.flip)) s).map ((slide (strict (A.flip.obj (op s,s))) h).app x)) := by
  unfold outerSlide
  simp only [NatTrans.comp_app,eqToHom_app]
  exact (Conjugate.trimLeft _ ⟨_,rfl⟩).trans (Conjugate.trimRight _ ⟨_,rfl⟩)

private theorem cast_id {C : Type*} [Category* C] {a b : C} {f : a ⟶ a} (h : Conjugate f (𝟙 b)) : f=𝟙 a := by
  obtain ⟨rfl,_,h⟩ := h; simpa only [eqToHom_refl,Category.comp_id,Category.id_comp] using h

def swapData : DirectedStateBalance.Cocone (strict (outer A)) (Iterated A.flip) where
  fiber := row A
  bal := outerSlide A
  unit {t} x := by
    obtain ⟨⟨s,x⟩⟩ := x
    have eq : (slide (strict (A.flip.obj (op s,s))) (𝟙 t)).app x = 𝟙 _ :=
      (restrict (𝟭 (Balance (strict (A.flip.obj (op s,s)))))).unit x
    apply cast_id
    have a := outerSlide_on_vertex A (𝟙 t) s x
    rw [eq,Functor.map_id] at a
    exact a
  comp {i j k} h g x := by
    obtain ⟨⟨s,x⟩⟩ := x
    let M := A.flip.obj (op s,s)
    let U := insertion (strict (outer A.flip)) s
    have e := (restrict (𝟭 (Balance (strict M)))).comp h g x
    have em := congrArg U.map e
    simp only [Functor.map_comp] at em
    let z := (insertion (strict (A.obj (op k,i))) s).obj x
    obtain ⟨v,src⟩ := trim ((structural_pre (outer A) h g z).map (row A i))
      ((structural_middle (outer A) h g z).map (row A j)) ((structural_post (outer A) h g z).map (row A k))
      ((outerSlide A h).app _) ((outerSlide A g).app _)
    obtain ⟨v',dst⟩ := trim (((structural_pre M h g x).map (insertion (strict M) i)).map U)
      (((structural_middle M h g x).map (insertion (strict M) j)).map U) (((structural_post M h g x).map (insertion (strict M) k)).map U)
      (U.map ((slide (strict M) h).app ((action (strict M) g (𝟙 i)).obj x)))
      (U.map ((slide (strict M) g).app ((action (strict M) (𝟙 k) h).obj x)))
    have l := outerSlide_on_vertex A h s ((action (strict M) g (𝟙 i)).obj x)
    have r := outerSlide_on_vertex A g s ((action (strict M) (𝟙 k) h).obj x)
    exact ((outerSlide_on_vertex A (h ≫ g) s x).trans
      ((em ▸ dst).trans ((middle_splice l r v v').symm.trans src.symm))).eq

def swap : Iterated A ⥤ Iterated A.flip := (swapData A).descend

abbrev outerInsert (t : T) := insertion (strict (outer A)) t
abbrev innerInsert (t t' : T) (s : S) := insertion (strict (A.obj (op t,t'))) s

theorem swap_inner {t : T} {x y : Balance (strict (A.obj (op t,t)))} (f : x ⟶ y) :
    (swap A).map ((outerInsert A t).map f) = (row A t).map f :=
  (swapData A).descend_generator (.native f)

theorem swap_native {t : T} {s : S} {x y : (A.obj (op t,t)).obj (op s,s)} (f : x ⟶ y) :
    (swap A).map ((outerInsert A t).map ((innerInsert A t t s).map f)) =
    (outerInsert A.flip s).map ((innerInsert A.flip s s t).map f) :=
  (swap_inner A _).trans (map_native _ _)

theorem conjugate_eq {C : Type*} [Category* C] {x y : C} {f g : x ⟶ y} (e : f=g) : Conjugate f g :=
  e ▸ Conjugate.refl _

theorem swap_inner_slide (t : T) {i j : S} (h : i ⟶ j) (x : (A.obj (op t,t)).obj (op j,i)) :
    Conjugate ((swap A).map ((outerInsert A t).map ((slide (strict (A.obj (op t,t))) h).app x)))
      ((slide (strict (outer A.flip)) h).app ((innerInsert A.flip j i t).obj x)) :=
  (conjugate_eq (swap_inner A _)).trans ((conjugate_eq (map_slide (unitFamily A t) h x)).trans (move_conjugate _ _ _))

set_option backward.isDefEq.respectTransparency true in
theorem swap_outer {i j : T} (h : i ⟶ j) (z : Balance (strict (A.obj (op j,i)))) :
    (swap A).map ((slide (strict (outer A)) h).app z) = (outerSlide A h).app z :=
  applied_slide (F := strict (outer A)) (D := Iterated A.flip) (swapData A) (i:=i) (j:=j) h z

theorem swap_outer_slide {i j : T} (h : i ⟶ j) (s : S) (x : (A.obj (op j,i)).obj (op s,s)) :
    Conjugate ((swap A).map ((slide (strict (outer A)) h).app ((innerInsert A j i s).obj x)))
      ((outerInsert A.flip s).map ((slide (strict (A.flip.obj (op s,s))) h).app x)) :=
    by
      rw [swap_outer]
      exact outerSlide_on_vertex A h s x

theorem swap_twice_row (t : T) : outerInsert A t ⋙ swap A ⋙ swap A.flip = outerInsert A t := by
  apply functor_ext (P := outerInsert A t ⋙ swap A ⋙ swap A.flip) (Q := outerInsert A t) (fun _ _ => rfl)
  · intro _ _ _ f
    exact heq_of_eq ((congrArg (swap A.flip).map (swap_native A f)).trans (swap_native A.flip f))
  · intro i j h x
    exact conjugate_heq ((map_conjugate (swap A.flip) (swap_inner_slide A t h x)).trans (swap_outer_slide A.flip h t x))

theorem swap_twice : swap A ⋙ swap A.flip = 𝟭 (Iterated A) := by
  apply functor_ext (P:=swap A ⋙ swap A.flip) (Q:=𝟭 _)
  · intro t x; obtain ⟨⟨s,x⟩⟩ := x; rfl
  · intro t x y f
    exact conjugate_heq (Conjugate.actions (swap_twice_row A t) f)
  · intro i j h x
    obtain ⟨⟨s,x⟩⟩ := x
    exact conjugate_heq ((map_conjugate (swap A.flip) (swap_outer_slide A h s x)).trans (swap_inner_slide A.flip s h x))

/-- Exact directed Fubini between the two independently built iterated categories, with its action on native arrows and both directed generators recorded above. -/
def iso : IsoCat (Iterated A) (Iterated A.flip) where
  functor := swap A
  inverse := swap A.flip
  unit_eq := (swap_twice A).symm
  counit_eq := swap_twice A.flip

end ContextualComposition.DirectedStateIterates
