module

public import ContextualComposition.DirectedStateIntertwiners

/-! A natural transformation of strict mixed diagrams induces an ordinary functor on directed contractions. Target slides are surrounded only by the identifying changes of their endpoints. -/

@[expose] public section
namespace ContextualComposition.DirectedStateDiagramMap

open CategoryTheory Opposite DirectedStateBalance DirectedStateNativeFaithfulness DirectedStateIntertwiners
universe v u w d
variable {S : Type u} [Category.{v} S] {G H K : Sᵒᵖ × S ⥤ Cat.{w,d}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev component (n : G ⟶ H) (i j : S) := (n.app (op i,j)).toFunctor

theorem equivariant (n : G ⟶ H) {i i' j j' : S} (h : i' ⟶ i) (g : j ⟶ j') :
    action (strict G) h g ⋙ component n i' j' = component n i j ⋙ action (strict H) h g :=
  congrArg Cat.Hom.toFunctor (n.naturality (pairMap h g))

def fiber (n : G ⟶ H) (i : S) := component n i i ⋙ insertion (strict H) i

theorem endpoints (n : G ⟶ H) {i i' j j' : S} (h : i' ⟶ i) (g : j ⟶ j') (x : atPair (strict G) i j) :
    (component n i' j').obj ((action (strict G) h g).obj x) = (action (strict H) h g).obj ((component n i j).obj x) :=
  congrArg (fun T => T.obj x) (equivariant n h g)

def move (n : G ⟶ H) {i j : S} (h : i ⟶ j) (x : atPair (strict G) j i) :
    (fiber n i).obj ((action (strict G) h (𝟙 i)).obj x) ⟶ (fiber n j).obj ((action (strict G) (𝟙 j) h).obj x) :=
  eqToHom (congrArg (insertion (strict H) i).obj (endpoints n h (𝟙 i) x)) ≫
    (slide (strict H) h).app ((component n j i).obj x) ≫
    eqToHom (congrArg (insertion (strict H) j).obj (endpoints n (𝟙 j) h x).symm)

theorem move_conjugate (n : G ⟶ H) {i j : S} (h : i ⟶ j) (x : atPair (strict G) j i) :
    Conjugate (move n h x) ((slide (strict H) h).app ((component n j i).obj x)) :=
  (Conjugate.trimLeft _ ⟨_,rfl⟩).trans (Conjugate.trimRight _ ⟨_,rfl⟩)

theorem equal_args {C D : Type*} [Category* C] [Category* D] {L R : C ⥤ D} (f : L ⟶ R) {x y : C} (e : x=y) :
    Conjugate (f.app x) (f.app y) := by subst y; exact Conjugate.refl _

theorem move_natural (n : G ⟶ H) {i j : S} (h : i ⟶ j) {x y : atPair (strict G) j i} (f : x ⟶ y) :
    (fiber n i).map ((action (strict G) h (𝟙 i)).map f) ≫ move n h y =
    move n h x ≫ (fiber n j).map ((action (strict G) (𝟙 j) h).map f) := by
  have a := comp_conjugate (map_conjugate (insertion (strict H) i) (Conjugate.actions (equivariant n h (𝟙 i)) f)) (move_conjugate n h y)
  have b := comp_conjugate (move_conjugate n h x) (map_conjugate (insertion (strict H) j) (Conjugate.actions (equivariant n (𝟙 j) h) f))
  have e := (slide (strict H) h).naturality ((component n j i).map f)
  exact (a.trans (e ▸ b.symm)).eq

theorem trim {C : Type*} [Category* C] {A B D E X Y : C} {i : A ⟶ B} {m : D ⟶ E} {j : X ⟶ Y}
    (ci : IsCast i) (cm : IsCast m) (cj : IsCast j) (f : B ⟶ D) (g : E ⟶ X) :
    ∃ e : D=E, Conjugate (i ≫ f ≫ m ≫ g ≫ j) (f ≫ eqToHom e ≫ g) := by
  rcases cm with ⟨e,rfl⟩
  exact ⟨e,(Conjugate.trimLeft _ ci).trans (comp_conjugate (Conjugate.refl _) (comp_conjugate (Conjugate.refl _) (Conjugate.trimRight _ cj)))⟩

theorem middle_splice {C : Type*} [Category* C] {U V W X U' V' W' X' : C}
    {f : U ⟶ V} {f' : U' ⟶ V'} {g : W ⟶ X} {g' : W' ⟶ X'} (h : Conjugate f f') (k : Conjugate g g')
    (e : V=W) (e' : V'=W') : Conjugate (f ≫ eqToHom e ≫ g) (f' ≫ eqToHom e' ≫ g') := by
  exact comp_conjugate h (comp_conjugate (by
    rcases h with ⟨_,v,_⟩; rcases k with ⟨w,_,_⟩
    exact ⟨v,w,by simp⟩) k)

def data (n : G ⟶ H) : DirectedStateBalance.Cocone (strict G) (Balance (strict H)) where
  fiber := fiber n
  bal h := ⟨move n h,fun _ _ f => move_natural n h f⟩
  unit {i} x := by
    have e : (slide (strict H) (𝟙 i)).app ((component n i i).obj x) = 𝟙 _ :=
      (restrict (𝟭 (Balance (strict H)))).unit ((component n _ _).obj x)
    change move n (𝟙 i) x = 𝟙 _
    unfold move
    rw [e]
    have undo {A B : Balance (strict H)} (p : A=B) : eqToHom p ≫ 𝟙 B ≫ eqToHom p.symm = 𝟙 A := by cases p; simp
    exact undo _
  comp h g x := by
    have left := move_conjugate n (h ≫ g) x
    let z := (component n _ _).obj x
    have target := (restrict (𝟭 (Balance (strict H)))).comp h g z
    obtain ⟨e,route⟩ := trim ((structural_pre H h g z).map (insertion _ _))
      ((structural_middle H h g z).map (insertion _ _)) ((structural_post H h g z).map (insertion _ _))
      ((slide (strict H) h).app ((action (strict H) g (𝟙 _)).obj z))
      ((slide (strict H) g).app ((action (strict H) (𝟙 _) h).obj z))
    obtain ⟨e',route'⟩ := trim ((structural_pre G h g x).map (fiber n _))
      ((structural_middle G h g x).map (fiber n _)) ((structural_post G h g x).map (fiber n _))
      (move n h ((action (strict G) g (𝟙 _)).obj x)) (move n g ((action (strict G) (𝟙 _) h).obj x))
    have f := (move_conjugate n h _).trans (equal_args (slide (strict H) h) (endpoints n g (𝟙 _) x))
    have k := (move_conjugate n g _).trans (equal_args (slide (strict H) g) (endpoints n (𝟙 _) h x))
    exact (left.trans ((target ▸ route).trans ((middle_splice f k e' e).symm.trans route'.symm))).eq

def map (n : G ⟶ H) : Balance (strict G) ⥤ Balance (strict H) := (data n).descend

theorem map_native (n : G ⟶ H) {i : S} {x y : atPair (strict G) i i} (f : x ⟶ y) :
    (map n).map ((insertion _ i).map f) = (insertion _ i).map ((component n i i).map f) :=
  (data n).descend_generator (.native f)

theorem map_slide (n : G ⟶ H) {i j : S} (h : i ⟶ j) (x : atPair (strict G) j i) :
    (map n).map ((slide _ h).app x) = move n h x := (data n).descend_generator (.slide h x)

theorem conjugate_heq {C : Type*} [Category* C] {a b c d : C} {f : a ⟶ b} {g : c ⟶ d} :
    Conjugate f g → f ≍ g := by
  rintro ⟨rfl,rfl,h⟩; exact heq_of_eq (by simpa only [eqToHom_refl,Category.id_comp,Category.comp_id] using h)

theorem functor_ext {D : Type*} [Category* D] {P Q : Balance (strict G) ⥤ D}
    (ho : ∀ i (x : atPair (strict G) i i), P.obj ((insertion _ i).obj x) = Q.obj ((insertion _ i).obj x))
    (hn : ∀ {i} {x y : atPair (strict G) i i} (f : x ⟶ y), P.map ((insertion _ i).map f) ≍ Q.map ((insertion _ i).map f))
    (hs : ∀ {i j} (h : i ⟶ j) (x : atPair (strict G) j i), P.map ((slide _ h).app x) ≍ Q.map ((slide _ h).app x)) : P=Q := by
  have e : restrict P = restrict Q := Cocone.ext (funext fun i => Functor.hext (ho i) (fun _ _ => hn)) hs
  exact (descend_restrict P).symm.trans ((congrArg Cocone.descend e).trans (descend_restrict Q))

theorem map_id (G : Sᵒᵖ × S ⥤ Cat.{w,d}) : map (𝟙 G) = 𝟭 _ := by
  apply functor_ext (P := map (𝟙 G)) (Q := 𝟭 _) (fun _ _ => rfl)
  · intro i x y f
    exact heq_of_eq (map_native (𝟙 G) f)
  · intro i j h x
    exact heq_of_eq ((map_slide (𝟙 G) h x).trans (move_conjugate (𝟙 G) h x).eq)

theorem map_comp (n : G ⟶ H) (m : H ⟶ K) : map (n ≫ m) = map n ⋙ map m := by
  apply functor_ext (P := map (n ≫ m)) (Q := map n ⋙ map m) (fun _ _ => rfl)
  · intro i x y f
    exact heq_of_eq ((map_native (n ≫ m) f).trans
      (((congrArg (map m).map (map_native n f)).trans (map_native m _)).symm))
  · intro i j h x
    have a := move_conjugate (n ≫ m) h x
    have b := (map_conjugate (map m) (move_conjugate n h x)).trans (show Conjugate _ _ from
      (map_slide m h ((component n j i).obj x)) ▸ move_conjugate m h ((component n j i).obj x))
    exact heq_of_eq ((map_slide _ h x).trans ((a.trans b.symm).eq.trans (congrArg (map m).map (map_slide n h x)).symm))

/-- Directed contraction acts on actual strict diagrams and their natural transformations. -/
def contraction : (Sᵒᵖ × S ⥤ Cat.{w,d}) ⥤ Cat where
  obj G := Cat.of (Balance (strict G))
  map t := (map t).toCatHom
  map_id G := congrArg Functor.toCatHom (map_id G)
  map_comp n m := congrArg Functor.toCatHom (map_comp n m)

end ContextualComposition.DirectedStateDiagramMap
