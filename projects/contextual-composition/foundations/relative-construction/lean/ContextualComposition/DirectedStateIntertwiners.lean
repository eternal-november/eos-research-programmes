module

public import ContextualComposition.DirectedStateNativeFaithfulness

/-! All mixed-fibre intertwiners for a strict state bifunctor. Their central cell is genuine data; a directed slide has only the comparison forced by functoriality. -/

@[expose] public section
namespace ContextualComposition.DirectedStateIntertwiners

open CategoryTheory Opposite DirectedStateBalance DirectedStateNativeFaithfulness StateWindowCategory
universe v u w d
variable {S : Type u} [Category.{v} S] (G : Sᵒᵖ × S ⥤ Cat.{w,d})
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Comparison
variable {C D : Type*} [Category* C] [Category* D] {A B A' B' C₁ C₂ : C}
theorem map_conjugate (K : C ⥤ D) {f : A ⟶ B} {g : A' ⟶ B'} : Conjugate f g → Conjugate (K.map f) (K.map g) := by
  rintro ⟨rfl,rfl,e⟩; simp only [eqToHom_refl,Category.comp_id,Category.id_comp] at e; subst g; exact Conjugate.refl _

theorem comp_conjugate {f : A ⟶ B} {g : A' ⟶ B'} {f' : B ⟶ C₁} {g' : B' ⟶ C₂} :
    Conjugate f g → Conjugate f' g' → Conjugate (f ≫ f') (g ≫ g') := by
  rintro ⟨rfl,rfl,e⟩ ⟨_,rfl,e'⟩
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id] at e e'
  subst g; subst g'; exact Conjugate.refl _
end Comparison

structure Point where
  state : S
  val : atPair (strict G) state state

def Point.window (X : Point G) (a b : S) := observe G a b X.state X.val

structure Arrow (X Y : Point G) where
  label : X.state ⟶ Y.state
  cell : (action (strict G) (𝟙 _) label).obj X.val ⟶ (action (strict G) label (𝟙 _)).obj Y.val

variable {G} {X Y Z V : Point G}

def evaluate (f : Arrow G X Y) (a b : S) : X.window G a b ⟶ Y.window G a b where
  state := f.label
  cell p q l r := by
    have dom : action (strict G) p.1 p.2 = action (strict G) (𝟙 X.state) f.label ⋙ action (strict G) p.1 q.2 := by
      rw [← strictComp,Category.comp_id,r]
    have cod : action (strict G) f.label (𝟙 Y.state) ⋙ action (strict G) p.1 q.2 = action (strict G) q.1 q.2 := by
      rw [← strictComp,Category.id_comp,l]
    exact eqToHom (congrArg (fun H => H.obj X.val) dom) ≫
      (action (strict G) p.1 q.2).map f.cell ≫ eqToHom (congrArg (fun H => H.obj Y.val) cod)

theorem reduced (f : Arrow G X Y) (a b : S) (p q) (l r) :
    Conjugate ((evaluate f a b).cell p q l r) ((action (strict G) p.1 q.2).map f.cell) := by
  dsimp only [evaluate]
  exact (Conjugate.trimLeft _ ⟨_,rfl⟩).trans (Conjugate.trimRight _ ⟨_,rfl⟩)

def identity (X : Point G) : Arrow G X X := ⟨𝟙 _,𝟙 _⟩

theorem eval_identity (X : Point G) (a b : S) : evaluate (identity X) a b = 𝟙 _ := by
  apply Hom.ext (f := evaluate (identity X) a b) (g := Hom.id (X.window G a b)) rfl
  intro p q l r l' r'
  apply IsCast.unique
  · change IsCast (eqToHom _ ≫ (action (strict G) p.1 q.2).map (𝟙 _) ≫ eqToHom _)
    exact IsCast.comp ⟨_,rfl⟩ (IsCast.comp (IsCast.map _ ⟨rfl,rfl⟩) ⟨_,rfl⟩)
  · exact ⟨congrArg (X.window G a b).observe (unchanged a b p q l' r'),rfl⟩

def compose (f : Arrow G X Y) (g : Arrow G Y Z) : Arrow G X Z where
  label := f.label ≫ g.label
  cell := (evaluate f X.state Z.state).cell (𝟙 _,f.label ≫ g.label) (f.label,g.label) (Category.id_comp _) rfl ≫
    (evaluate g X.state Z.state).cell (f.label,g.label) (f.label ≫ g.label,𝟙 _) rfl (Category.comp_id _)

/-- Whiskering a central comparison and then testing it equals pasting the tested cells at the uniquely forced intermediate state window. -/
theorem eval_compose (f : Arrow G X Y) (g : Arrow G Y Z) (a b : S) :
    evaluate (compose f g) a b = evaluate f a b ≫ evaluate g a b := by
  apply Hom.ext (f := evaluate (compose f g) a b) (g := evaluate f a b ≫ evaluate g a b) rfl
  intro p q l r l' r'
  let m : Window a b Y.state := (p.1 ≫ f.label, g.label ≫ q.2)
  have r₁ : f.label ≫ m.2 = p.2 := (Category.assoc _ _ _).symm.trans r
  have l₂ : m.1 ≫ g.label = q.1 := (Category.assoc _ _ _).trans l
  let K := action (strict G) p.1 q.2
  let f₀ := (evaluate f X.state Z.state).cell (𝟙 _,f.label ≫ g.label) (f.label,g.label) (Category.id_comp _) rfl
  let g₀ := (evaluate g X.state Z.state).cell (f.label,g.label) (f.label ≫ g.label,𝟙 _) rfl (Category.comp_id _)
  have df : Conjugate (K.map f₀) ((evaluate f a b).cell p m rfl r₁) := by
    apply (map_conjugate K (reduced f _ _ _ _ _ _)).trans
    apply Conjugate.trans _ (reduced f a b p m rfl r₁).symm
    exact Conjugate.actions ((strictComp G (𝟙 _) p.1 g.label q.2).symm.trans
      (congrArg (fun z => action (strict G) z m.2) (Category.comp_id _))) f.cell
  have dg : Conjugate (K.map g₀) ((evaluate g a b).cell m q l₂ rfl) := by
    apply (map_conjugate K (reduced g _ _ _ _ _ _)).trans
    apply Conjugate.trans _ (reduced g a b m q l₂ rfl).symm
    exact Conjugate.actions ((strictComp G f.label p.1 (𝟙 _) q.2).symm.trans
      (congrArg (action (strict G) m.1) (Category.id_comp _))) g.cell
  have h := reduced (compose f g) a b p q l r
  change Conjugate _ (K.map (f₀ ≫ g₀)) at h
  rw [K.map_comp] at h
  exact (h.trans (comp_conjugate df dg)).eq

theorem arrow_ext {f g : Arrow G X Y} (label : f.label = g.label)
    (tested : ∀ a b, evaluate f a b = evaluate g a b) : f=g := by
  cases f with | mk h f =>
    cases g with | mk k g =>
      cases label
      let p : Window X.state Y.state X.state := (𝟙 _,h)
      let q : Window X.state Y.state Y.state := (h,𝟙 _)
      have eqCells (s t : X.window G X.state Y.state ⟶ Y.window G X.state Y.state) (e : s=t)
          (hs : s.state=h) (ht : t.state=h) :
          s.cell p q (by rw [hs]; exact Category.id_comp _) (by rw [hs]; exact Category.comp_id _) =
          t.cell p q (by rw [ht]; exact Category.id_comp _) (by rw [ht]; exact Category.comp_id _) := by
        subst t; rfl
      have e := eqCells _ _ (tested X.state Y.state) rfl rfl
      have identityAct : action (strict G) (𝟙 X.state) (𝟙 Y.state) = 𝟭 _ :=
        congrArg Cat.Hom.toFunctor (G.map_id (op X.state,Y.state))
      have a := reduced (show Arrow G X Y from ⟨h,f⟩) _ _ p q (Category.id_comp _) (Category.comp_id _)
      have b := reduced (show Arrow G X Y from ⟨h,g⟩) _ _ p q (Category.id_comp _) (Category.comp_id _)
      have fg : f=g := (((Conjugate.actions identityAct f).symm.trans a.symm).trans
        ((e ▸ b).trans (Conjugate.actions identityAct g))).eq
      cases fg; rfl

instance : Category (Point G) where
  Hom := Arrow G
  id := identity
  comp := compose
  id_comp f := arrow_ext (Category.id_comp _) (fun a b => by rw [eval_compose,eval_identity,Category.id_comp])
  comp_id f := arrow_ext (Category.comp_id _) (fun a b => by rw [eval_compose,eval_identity,Category.comp_id])
  assoc f g h := arrow_ext (Category.assoc _ _ _) (fun a b => by simp only [eval_compose,Category.assoc])

def native {i : S} {x y : atPair (strict G) i i} (f : x ⟶ y) : (⟨i,x⟩ : Point G) ⟶ ⟨i,y⟩ :=
  ⟨𝟙 _,(action (strict G) (𝟙 _) (𝟙 _)).map f⟩

theorem evaluate_native {i : S} {x y : atPair (strict G) i i} (f : x ⟶ y) (a b : S) :
    evaluate (native f) a b = localMap G a b f := by
  apply Hom.ext (f := evaluate (native f) a b) (g := localMap G a b f) rfl
  intro p q l r l' r'
  obtain rfl := unchanged a b p q l r
  have e : action (strict G) (𝟙 i) (𝟙 i) = 𝟭 _ := congrArg Cat.Hom.toFunctor (G.map_id (op i,i))
  exact ((reduced (native f) a b p p l r).trans ((map_conjugate (action (strict G) p.1 p.2) (Conjugate.actions e f)).trans
    (local_source G a b f p p l' r').symm)).eq

def nativeFunctor (G : Sᵒᵖ × S ⥤ Cat.{w,d}) (i : S) : atPair (strict G) i i ⥤ Point G where
  obj x := ⟨i,x⟩
  map f := native f
  map_id x := arrow_ext rfl (fun a b => (evaluate_native (𝟙 x) a b).trans
    (((fiber G a b i).map_id x).trans (eval_identity (⟨i,x⟩ : Point G) a b).symm))
  map_comp f g := arrow_ext (Category.id_comp _).symm (fun a b => by
    change evaluate (native (f ≫ g)) a b = evaluate (compose (native f) (native g)) a b
    rw [eval_compose,evaluate_native,evaluate_native,evaluate_native]
    exact (fiber G a b i).map_comp f g)

def sliding {i j : S} (h : i ⟶ j) (x : atPair (strict G) j i) :
    (nativeFunctor G i).obj ((action (strict G) h (𝟙 i)).obj x) ⟶
      (nativeFunctor G j).obj ((action (strict G) (𝟙 j) h).obj x) :=
  ⟨h,eqToHom (congrArg (fun T => T.obj x) (common_action G i j h (𝟙 i,h) (h,𝟙 j) (Category.id_comp h) (Category.comp_id h)))⟩

theorem evaluate_sliding {i j : S} (h : i ⟶ j) (x : atPair (strict G) j i) (a b : S) :
    evaluate (sliding h x) a b = slip G a b h x := by
  apply structural_eq G a b (f := evaluate (sliding h x) a b) (g := slip G a b h x) rfl _ (structural_slide G a b h x)
  intro p q l r
  have hcast : IsCast (sliding h x).cell := ⟨congrArg (fun T => T.obj x)
    (common_action G i j h (𝟙 i,h) (h,𝟙 j) (Category.id_comp h) (Category.comp_id h)),rfl⟩
  dsimp only [evaluate]
  exact IsCast.comp ⟨_,rfl⟩ (IsCast.comp (IsCast.map _ hcast) ⟨_,rfl⟩)

def data (G : Sᵒᵖ × S ⥤ Cat.{w,d}) : DirectedStateBalance.Cocone (strict G) (Point G) where
  fiber := nativeFunctor G
  bal h := { app := sliding h
             naturality := by
               intro x y f
               apply arrow_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
               intro a b
               change evaluate (compose (native _) (sliding _ _)) _ _ = evaluate (compose (sliding _ _) (native _)) _ _
               rw [eval_compose,eval_compose,evaluate_native,evaluate_native,evaluate_sliding,evaluate_sliding]
               exact slide_natural G a b h f }
  unit {i} x := arrow_ext rfl (fun a b => (evaluate_sliding (𝟙 i) x a b).trans
    (((detectorData G a b).unit x).trans (eval_identity (⟨i,(action (strict G) (𝟙 i) (𝟙 i)).obj x⟩ : Point G) a b).symm))
  comp h g x := by
    apply arrow_ext
    · change h ≫ g = 𝟙 _ ≫ h ≫ 𝟙 _ ≫ g ≫ 𝟙 _; simp
    · intro a b
      change evaluate (sliding _ _) _ _ = evaluate (compose (native _) (compose (sliding _ _) (compose (native _) (compose (sliding _ _) (native _))))) _ _
      simp only [eval_compose,evaluate_native,evaluate_sliding]
      exact (detectorData G a b).comp h g x

def detector (G : Sᵒᵖ × S ⥤ Cat.{w,d}) : Balance (strict G) ⥤ Point G := (data G).descend

theorem detector_native {i : S} {x y : atPair (strict G) i i} (f : x ⟶ y) : (detector G).map ((insertion _ i).map f) = native f :=
  (data G).descend_generator (.native f)

theorem detector_slide {i j : S} (h : i ⟶ j) (x : atPair (strict G) j i) : (detector G).map ((slide (strict G) h).app x) = sliding h x :=
  (data G).descend_generator (.slide h x)

end ContextualComposition.DirectedStateIntertwiners
