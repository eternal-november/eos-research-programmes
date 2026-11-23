module

public import ContextualComposition.DisplaySpanRecovery

/-! Codisplay cospans are directed from their first endpoint to their second. The admitted leg is the second injection. Reversing apex maps once in the opposite base and once in its span hom recovers forward native cells. -/

@[expose] public section

namespace ContextualComposition.CodisplayCospanRecovery

open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)
  {A B D A' B' D' : C}

abbrev Ext (B : C) := MorphismProperty.Under.forget P ⊤ B ⋙ CategoryTheory.Under.forget B
abbrev Native (A B : C) := StructuredArrow A (Ext P B)
abbrev H (A B : C) := (Span (⊤ : MorphismProperty Cᵒᵖ) P.op (op A) (op B))ᵒᵖ

def readObj (x : Native P A B) : H P A B :=
  op ⟨op x.right.right, x.hom.op, x.right.hom.op, trivial, x.right.prop⟩

def read : Native P A B ⥤ H P A B where
  obj := readObj P
  map {x y} f := Quiver.Hom.op (X := (readObj P y).unop) (Y := (readObj P x).unop)
    (Span.Hom.mk f.right.right.op (congrArg Quiver.Hom.op (StructuredArrow.w f)) (congrArg Quiver.Hom.op (MorphismProperty.Under.w f.right)))

def write : H P A B ⥤ Native P A B where
  obj S := StructuredArrow.mk (Y := MorphismProperty.Under.mk ⊤ S.unop.r.unop S.unop.wr) S.unop.l.unop
  map f := StructuredArrow.homMk (MorphismProperty.Under.homMk f.unop.hom.unop (congrArg Quiver.Hom.unop f.unop.hom_r))
    (congrArg Quiver.Hom.unop f.unop.hom_l)

set_option backward.isDefEq.respectTransparency false in
def nativeEquivalence : Native P A B ≌ H P A B where
  functor := read P
  inverse := write P
  unitIso := NatIso.ofComponents (fun x =>
    StructuredArrow.isoMk (MorphismProperty.Under.isoMk (Iso.refl _) (Category.comp_id _)) (Category.comp_id x.hom))
    (by intro x y f; apply StructuredArrow.hom_ext; apply MorphismProperty.Under.Hom.ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun _ => (Span.mkIso (Iso.refl _) (Category.id_comp _) (Category.id_comp _)).op)
    (by intro x y f; apply Quiver.Hom.unop_inj; apply Span.hom_ext; exact (Category.id_comp _).trans (Category.comp_id _).symm)
  functor_unitIso_comp x := by apply Quiver.Hom.unop_inj; apply Span.hom_ext; exact Category.id_comp _

structure Square (S : H P A B) (T : H P A' B') (u : A ⟶ A') (v : B ⟶ B') where
  apex : S.unop.apex.unop ⟶ T.unop.apex.unop
  source_comm : S.unop.l.unop ≫ apex = u ≫ T.unop.l.unop
  target_comm : S.unop.r.unop ≫ apex = v ≫ T.unop.r.unop

@[ext] theorem Square.ext {S : H P A B} {T : H P A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    {f g : Square P S T u v} (h : f.apex = g.apex) : f = g := by cases f; cases g; cases h; rfl

variable [P.HasPushouts]

local instance legPushout (S : H P A B) (v : B ⟶ B') : HasPushout S.unop.r.unop v :=
  P.hasPushout v S.unop.wr

local instance nativePushout (x : Native P A B) (y : Native P B D) : HasPushout x.right.hom y.hom :=
  P.hasPushout y.hom x.right.prop

/-- The opposite-base span model needs pullbacks only against admitted right legs. -/
instance oppositeAdmitted : (⊤ : MorphismProperty Cᵒᵖ).HasPullbacksAgainst P.op where
  hasPullbacksAlong _ _ f hf := {
    hasPullback := fun {_} g _ => by
      let := P.hasPushout g.unop hf
      exact (hasPushout_unop_iff_hasPullback g f).mp (hasPushout_symmetry _ _) }

/-- Forward content-grade map from the pushed-out old codisplay to the new apex. -/
structure Reindexed (S : H P A B) (T : H P A' B') (u : A ⟶ A') (v : B ⟶ B') where
  grade : pushout S.unop.r.unop v ⟶ T.unop.apex.unop
  under : pushout.inr _ _ ≫ grade = T.unop.r.unop
  body : S.unop.l.unop ≫ pushout.inl _ _ ≫ grade = u ≫ T.unop.l.unop

@[ext] theorem Reindexed.ext {S : H P A B} {T : H P A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    {f g : Reindexed P S T u v} (h : f.grade = g.grade) : f = g := by cases f; cases g; cases h; rfl

theorem reindexed_admitted [P.IsStableUnderCobaseChange] (S : H P A B) (v : B ⟶ B') :
    P (pushout.inr S.unop.r.unop v) := P.pushout_inr _ _ S.unop.wr

noncomputable def squareEquiv (S : H P A B) (T : H P A' B') (u : A ⟶ A') (v : B ⟶ B') :
    Reindexed P S T u v ≃ Square P S T u v where
  toFun f := {
    apex := pushout.inl _ _ ≫ f.grade
    source_comm := f.body
    target_comm := by rw [← Category.assoc, pushout.condition, Category.assoc, f.under] }
  invFun g := {
    grade := pushout.desc g.apex T.unop.r.unop g.target_comm
    under := by simp
    body := by simp [g.source_comm] }
  left_inv f := by apply Reindexed.ext; apply pushout.hom_ext <;> simp [f.under]
  right_inv g := Square.ext P (by simp)

variable [P.IsMultiplicative] [P.IsStableUnderCobaseChange]

noncomputable def nativeComp (x : Native P A B) (y : Native P B D) : Native P A D :=
  StructuredArrow.mk (Y := MorphismProperty.Under.mk ⊤ (y.right.hom ≫ pushout.inr x.right.hom y.hom)
    (P.comp_mem _ _ y.right.prop (P.pushout_inr (show B ⟶ x.right.right from x.right.hom)
      (show B ⟶ y.right.right from y.hom) x.right.prop))) (x.hom ≫ pushout.inl x.right.hom y.hom)

def nativeId (A : C) : Native P A A :=
  StructuredArrow.mk (Y := MorphismProperty.Under.mk ⊤ (𝟙 A) (P.id_mem _)) (𝟙 A)

/-- Horizontal pasting with changing endpoints is induced by the actual pushout map. -/
noncomputable def paste {x : Native P A B} {y : Native P B D} {x' : Native P A' B'} {y' : Native P B' D'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'}
    (f : Square P (readObj P x) (readObj P x') u v) (g : Square P (readObj P y) (readObj P y') v w) :
    Square P (readObj P (nativeComp P x y)) (readObj P (nativeComp P x' y')) u w := by
  let eq₁ : x.right.hom ≫ f.apex = v ≫ x'.right.hom := f.target_comm
  let eq₂ : y.hom ≫ g.apex = v ≫ y'.hom := g.source_comm
  have hs : x.hom ≫ f.apex = u ≫ x'.hom := f.source_comm
  have ht : y.right.hom ≫ g.apex = w ≫ y'.right.hom := g.target_comm
  let α := pushout.desc (f := x.right.hom) (g := y.hom) (f.apex ≫ pushout.inl x'.right.hom y'.hom) (g.apex ≫ pushout.inr x'.right.hom y'.hom) (by
    rw [← Category.assoc, eq₁, Category.assoc, pushout.condition, ← Category.assoc, ← eq₂, Category.assoc])
  refine ⟨α, ?_, ?_⟩
  · change (x.hom ≫ pushout.inl _ _) ≫ α = u ≫ x'.hom ≫ pushout.inl _ _
    rw [Category.assoc, pushout.inl_desc, ← Category.assoc, hs, Category.assoc]
  · change (y.right.hom ≫ pushout.inr _ _) ≫ α = w ≫ y'.right.hom ≫ pushout.inr _ _
    rw [Category.assoc, pushout.inr_desc, ← Category.assoc, ht, Category.assoc]

/-- The inherited span composite uses the opposite-base pullback. The comparison identifies its apex with the independent direct pushout construction and both outer legs. -/
noncomputable def compositionIso (x : Native P A B) (y : Native P B D) :
    (read P).obj (nativeComp P x y) ≅ op (Span.comp ((read P).obj x).unop ((read P).obj y).unop) := by
  let e := pushoutIsoUnopPullback x.right.hom y.hom
  refine (Span.mkIso e.op ?_ ?_).op
  · apply Quiver.Hom.unop_inj
    change (x.hom ≫ pushout.inl _ _) ≫ e.hom = x.hom ≫ (pullback.fst _ _).unop
    exact (Category.assoc _ _ _).trans (congrArg (fun k => x.hom ≫ k) (pushoutIsoUnopPullback_inl_hom _ _))
  · apply Quiver.Hom.unop_inj
    change (y.right.hom ≫ pushout.inr _ _) ≫ e.hom = y.right.hom ≫ (pullback.snd _ _).unop
    exact (Category.assoc _ _ _).trans (congrArg (fun k => y.right.hom ≫ k) (pushoutIsoUnopPullback_inr_hom _ _))

/-- The induced apex arrow in the opposite-base pullback model, unopped to its forward direction. -/
noncomputable def modelPaste {x : Native P A B} {y : Native P B D} {x' : Native P A' B'} {y' : Native P B' D'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'}
    (f : Square P (readObj P x) (readObj P x') u v) (g : Square P (readObj P y) (readObj P y') v w) :
    unop (pullback x.right.hom.op y.hom.op) ⟶ unop (pullback x'.right.hom.op y'.hom.op) := by
  have hf : f.apex.op ≫ x.right.hom.op = x'.right.hom.op ≫ v.op := congrArg Quiver.Hom.op f.target_comm
  have hg : g.apex.op ≫ y.hom.op = y'.hom.op ≫ v.op := congrArg Quiver.Hom.op g.source_comm
  exact (pullback.lift (f := x.right.hom.op) (g := y.hom.op)
    (pullback.fst x'.right.hom.op y'.hom.op ≫ f.apex.op)
    (pullback.snd x'.right.hom.op y'.hom.op ≫ g.apex.op)
    (by rw [Category.assoc, Category.assoc, hf, hg, ← Category.assoc, ← Category.assoc, pullback.condition])).unop

/-- Naturality of the canonical comparison on horizontally pasted squares, including changing endpoints. -/
theorem compositionIso_paste {x : Native P A B} {y : Native P B D} {x' : Native P A' B'} {y' : Native P B' D'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'}
    (f : Square P (readObj P x) (readObj P x') u v) (g : Square P (readObj P y) (readObj P y') v w) :
    (paste P f g).apex ≫ (pushoutIsoUnopPullback x'.right.hom y'.hom).hom =
      (pushoutIsoUnopPullback x.right.hom y.hom).hom ≫ modelPaste P f g := by
  apply pushout.hom_ext
  · rw [← Category.assoc, ← Category.assoc, pushoutIsoUnopPullback_inl_hom]
    change (pushout.inl _ _ ≫ pushout.desc _ _ _) ≫ _ = _
    rw [pushout.inl_desc, Category.assoc, pushoutIsoUnopPullback_inl_hom]
    apply Quiver.Hom.op_inj
    simp [modelPaste]
  · rw [← Category.assoc, ← Category.assoc, pushoutIsoUnopPullback_inr_hom]
    change (pushout.inr _ _ ≫ pushout.desc _ _ _) ≫ _ = _
    rw [pushout.inr_desc, Category.assoc, pushoutIsoUnopPullback_inr_hom]
    apply Quiver.Hom.op_inj
    simp [modelPaste]

/-- Reversing the two-cell direction supplies forward cospan apex maps in the opposite-base span model. -/
structure LocallyOpposite (B : Type*) where
  obj : B

namespace LocallyOpposite

open CategoryTheory.Bicategory
variable {M : Type*} [Bicategory M]

instance : CategoryStruct (LocallyOpposite M) where
  Hom X Y := (X.obj ⟶ Y.obj)ᵒᵖ
  id X := op (𝟙 X.obj)
  comp f g := op (f.unop ≫ g.unop)

instance (X Y : LocallyOpposite M) : Category (X ⟶ Y) :=
  inferInstanceAs (Category (X.obj ⟶ Y.obj)ᵒᵖ)

instance : Bicategory (LocallyOpposite M) := by
  refine {
    toCategoryStruct := inferInstance
    homCategory := fun X Y => inferInstanceAs (Category (X.obj ⟶ Y.obj)ᵒᵖ)
    whiskerLeft := fun {_ _ _} f {_ _} η => (Opposite.unop f ◁ Quiver.Hom.unop η).op
    whiskerRight := fun {_ _ _} {_ _} η h => (Quiver.Hom.unop η ▷ Opposite.unop h).op
    associator := fun f g h => (α_ (Opposite.unop f) (Opposite.unop g) (Opposite.unop h)).symm.op
    leftUnitor := fun f => (λ_ (Opposite.unop f)).symm.op
    rightUnitor := fun f => (ρ_ (Opposite.unop f)).symm.op
    whiskerLeft_id := ?_, whiskerLeft_comp := ?_, id_whiskerLeft := ?_, comp_whiskerLeft := ?_
    id_whiskerRight := ?_, comp_whiskerRight := ?_, whiskerRight_id := ?_, whiskerRight_comp := ?_
    whisker_assoc := ?_, whisker_exchange := ?_, pentagon := ?_, triangle := ?_ }
  all_goals intros; apply Quiver.Hom.unop_inj
  · exact Bicategory.whiskerLeft_id _ _
  · exact Bicategory.whiskerLeft_comp _ _ _
  · exact (Bicategory.id_whiskerLeft _).trans (Category.assoc _ _ _).symm
  · exact (Bicategory.comp_whiskerLeft _ _ _).trans (Category.assoc _ _ _).symm
  · exact Bicategory.id_whiskerRight _ _
  · exact Bicategory.comp_whiskerRight _ _ _
  · exact (Bicategory.whiskerRight_id _).trans (Category.assoc _ _ _).symm
  · exact (Bicategory.whiskerRight_comp _ _ _).trans (Category.assoc _ _ _).symm
  · exact (Bicategory.whisker_assoc _ _ _).trans (Category.assoc _ _ _).symm
  · exact (Bicategory.whisker_exchange _ _).symm
  · exact (Category.assoc _ _ _).trans (Bicategory.pentagon_inv _ _ _ _)
  · exact Bicategory.triangle_assoc_comp_left_inv _ _

end LocallyOpposite

/-- Objects and horizontal cells of the coherent cospan model. Its hom category has the arrows of the forward structured-arrow presentation. -/
abbrev Model := LocallyOpposite (Span.SpanBicat Cᵒᵖ ⊤ P.op)

noncomputable abbrev coherent : Bicategory (Model P) := inferInstance

def object (A : C) : Model P := ⟨⟨op A⟩⟩

theorem hom_model : (object P A ⟶ object P B) = H P A B := rfl

omit [P.HasPushouts] [P.IsStableUnderCobaseChange] in
theorem read_nativeId (A : C) :
    (read P).obj (nativeId P A) = op (Span.id (Wₗ := ⊤) (Wᵣ := P.op) (op A)) := rfl

open Bicategory

/-- Composites with their chosen parentheses and identity insertions. -/
inductive Expression (P : MorphismProperty C) : C → C → Type (max u v) where
  | arrow {A B : C} (x : Native P A B) : Expression P A B
  | unit (A : C) : Expression P A A
  | join {A B D : C} (x : Expression P A B) (y : Expression P B D) : Expression P A D

namespace Expression

noncomputable def eval : {A B : C} → Expression P A B → Native P A B
  | _, _, .arrow x => x
  | _, _, .unit A => nativeId P A
  | _, _, .join x y => nativeComp P (eval x) (eval y)

noncomputable def interpret : {A B : C} → Expression P A B → (object P A ⟶ object P B)
  | _, _, .arrow x => readObj P x
  | _, _, .unit A => 𝟙 (object P A)
  | _, _, .join x y => interpret x ≫ interpret y

/-- Every parenthesized native composite compares by the canonical binary pushout isomorphisms and their whiskerings. -/
noncomputable def comparison : {A B : C} → (x : Expression P A B) → readObj P (eval P x) ≅ interpret P x
  | _, _, .arrow _ => Iso.refl _
  | _, _, .unit _ => Iso.refl _
  | A, D, .join (B := B) x y => by
    let l : object P A ⟶ object P B := readObj P (eval P x)
    let r : object P B ⟶ object P D := readObj P (eval P y)
    have i : readObj P (nativeComp P (eval P x) (eval P y)) ≅ l ≫ r := compositionIso P _ _
    have j : l ≅ interpret P x := comparison x
    have k : r ≅ interpret P y := comparison y
    exact i ≪≫ whiskerRightIso j r ≪≫ whiskerLeftIso (interpret P x) k

/-- Decode a model two-cell as a genuine native structured-arrow morphism between the direct pushout composites. -/
noncomputable def realize (x y : Expression P A B) (θ : interpret P x ⟶ interpret P y) :
    eval P x ⟶ eval P y := (nativeEquivalence P).fullyFaithfulFunctor.preimage
      ((comparison P x).hom ≫ θ ≫ (comparison P y).inv)

theorem read_realize (x y : Expression P A B) (θ : interpret P x ⟶ interpret P y) :
    (read P).map (realize P x y θ) = (comparison P x).hom ≫ θ ≫ (comparison P y).inv :=
  (nativeEquivalence P).fullyFaithfulFunctor.map_preimage _

theorem realize_comp (x y z : Expression P A B) (f : interpret P x ⟶ interpret P y) (g : interpret P y ⟶ interpret P z) :
    realize P x y f ≫ realize P y z g = realize P x z (f ≫ g) := by
  apply (nativeEquivalence P).fullyFaithfulFunctor.map_injective
  change (read P).map _ = (read P).map _
  simp only [Functor.map_comp, read_realize, Category.assoc, Iso.inv_hom_id_assoc]

theorem realize_id (x : Expression P A B) : realize P x x (𝟙 _) = 𝟙 _ := by
  apply (nativeEquivalence P).fullyFaithfulFunctor.map_injective
  change (read P).map _ = (read P).map _
  exact (read_realize P x x (𝟙 _)).trans ((congrArg ((comparison P x).hom ≫ ·)
    (Category.id_comp (comparison P x).inv)).trans ((comparison P x).hom_inv_id.trans ((read P).map_id _).symm))

/-- The two triangle routes agree as native apex morphisms on the independently evaluated pushouts. -/
theorem native_triangle (x : Expression P A B) (y : Expression P B D) :
    realize P ((x.join (unit (P := P) B)).join y) (x.join ((unit (P := P) B).join y)) (α_ (interpret P x) (𝟙 (object P B)) (interpret P y)).hom ≫
      realize P (x.join ((unit (P := P) B).join y)) (x.join y) ((interpret P x) ◁ (λ_ (interpret P y)).hom) =
    realize P ((x.join (unit (P := P) B)).join y) (x.join y) ((ρ_ (interpret P x)).hom ▷ (interpret P y)) := by
  rw [realize_comp]
  exact congrArg (realize P _ _) (Bicategory.triangle (interpret P x) (interpret P y))

/-- All five parentheses in the pentagon are independently evaluated by the direct pushout recipe. -/
theorem native_pentagon {E F : C} (x : Expression P A B) (y : Expression P B D)
    (z : Expression P D E) (w : Expression P E F) :
    realize P (((x.join y).join z).join w) ((x.join (y.join z)).join w) ((α_ _ _ _).hom ▷ interpret P w) ≫
      realize P ((x.join (y.join z)).join w) (x.join ((y.join z).join w)) (α_ _ _ _).hom ≫
      realize P (x.join ((y.join z).join w)) (x.join (y.join (z.join w))) (interpret P x ◁ (α_ _ _ _).hom) =
    realize P (((x.join y).join z).join w) ((x.join y).join (z.join w)) (α_ _ _ _).hom ≫
      realize P ((x.join y).join (z.join w)) (x.join (y.join (z.join w))) (α_ _ _ _).hom := by
  simp only [realize_comp]
  exact congrArg (realize P _ _) (Bicategory.pentagon (interpret P x) (interpret P y) (interpret P z) (interpret P w))

end Expression

end ContextualComposition.CodisplayCospanRecovery
