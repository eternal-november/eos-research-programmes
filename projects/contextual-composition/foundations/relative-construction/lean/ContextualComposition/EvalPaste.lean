module
public import ContextualComposition.ValueConstraints
/-! Positive telescope evaluation: paste both chosen constraint diagrams. The middle square is moved using its naturality on the actual inner comparison component. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.FibreValue
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage SpanPayload.Power SpanApex
namespace Paste
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem unit (V : C ⥤ D) {x y z : C} {w : D}
    (f : x ⟶ y) (c : y ⟶ z) (d : x ⟶ z)
    (g : V.obj y ⟶ w) (u : w ⟶ V.obj z)
    (k : f ≫ c = d) (h : g ≫ u = V.map c) :
    (V.map f ≫ g) ≫ u = V.map d := by
  rw [Category.assoc,h,← V.map_comp,k]

theorem comp (V : C ⥤ D) (T : E ⥤ D)
    {x y z p q : C} {s t e : E} {w : D}
    (f : x ⟶ y) (c : y ⟶ z) (d : x ⟶ p) (i : p ⟶ q) (j : q ⟶ z)
    (g : V.obj y ⟶ w) (u : w ⟶ T.obj t)
    (l : V.obj z ⟶ T.obj s) (m : s ⟶ t)
    (v : V.obj q ⟶ T.obj e) (k : e ⟶ s)
    (inner : f ≫ c = d ≫ i ≫ j)
    (outer : g ≫ u = V.map c ≫ l ≫ T.map m)
    (middle : V.map j ≫ l = v ≫ T.map k) :
    (V.map f ≫ g) ≫ u = V.map d ≫ (V.map i ≫ v) ≫ T.map (k ≫ m) := by
  rw [Category.assoc,outer,← Category.assoc,← V.map_comp,inner]
  simp only [Functor.map_comp,Category.assoc]
  rw [reassoc_of% middle]
end Paste
namespace Paste
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
def UnitLaw {X : A ⥤ A} {Y : B ⥤ B} {F : A ⥤ B}
    (s : X ⋙ F ≅ F ⋙ Y) (u : X ⟶ 𝟭 _) (v : Y ⟶ 𝟭 _) : Prop :=
  ∀ x, s.hom.app x ≫ v.app (F.obj x) = F.map (u.app x)
theorem unitDiagram_iff {X : A ⥤ A} {Y : B ⥤ B} {F : A ⥤ B}
    (s : X ⋙ F ≅ F ⋙ Y) (u : X ⟶ 𝟭 _) (v : Y ⟶ 𝟭 _) :
    UnitLaw s u v ↔ s.hom ≫ whiskerLeft F v = whiskerRight u F :=
  ⟨fun h => NatTrans.ext (funext h),fun h x => NatTrans.congr_app h x⟩
theorem unitLaw {X : A ⥤ A} {Y : B ⥤ B} {Z : C ⥤ C}
    {F : A ⥤ B} {G : B ⥤ C}
    (s : X ⋙ F ≅ F ⋙ Y) (t : Y ⋙ G ≅ G ⋙ Z)
    (u : X ⟶ 𝟭 _) (v : Y ⟶ 𝟭 _) (w : Z ⟶ 𝟭 _)
    (hf : UnitLaw s u v) (hg : UnitLaw t v w) :
    UnitLaw (SpanPayload.pasteIso s.symm t.symm).symm u w := by
  intro x
  have e : ((SpanPayload.pasteIso s.symm t.symm).symm.hom.app x) =
      G.map (s.hom.app x) ≫ t.hom.app (F.obj x) := by simp [SpanPayload.pasteIso]
  rw [e]; exact unit G _ _ _ _ _ (hf x) (hg (F.obj x))
variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*}
    [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₁] [Category* B₂] [Category* B₃]
def CompLaw {X : A₂ ⥤ A₁} {Y : A₃ ⥤ A₂} {W : A₃ ⥤ A₁}
    {X' : B₂ ⥤ B₁} {Y' : B₃ ⥤ B₂} {W' : B₃ ⥤ B₁}
    {F : A₁ ⥤ B₁} {G : A₂ ⥤ B₂} {H : A₃ ⥤ B₃}
    (s : W ⋙ F ≅ H ⋙ W') (i : X ⋙ F ≅ G ⋙ X') (j : Y ⋙ G ≅ H ⋙ Y')
    (u : W ⟶ Y ⋙ X) (v : W' ⟶ Y' ⋙ X') : Prop :=
  ∀ z, s.hom.app z ≫ v.app (H.obj z) =
    F.map (u.app z) ≫ i.hom.app (Y.obj z) ≫ X'.map (j.hom.app z)
theorem compDiagram_iff {X : A₂ ⥤ A₁} {Y : A₃ ⥤ A₂} {W : A₃ ⥤ A₁}
    {X' : B₂ ⥤ B₁} {Y' : B₃ ⥤ B₂} {W' : B₃ ⥤ B₁}
    {F : A₁ ⥤ B₁} {G : A₂ ⥤ B₂} {H : A₃ ⥤ B₃}
    (s : W ⋙ F ≅ H ⋙ W') (i : X ⋙ F ≅ G ⋙ X') (j : Y ⋙ G ≅ H ⋙ Y')
    (u : W ⟶ Y ⋙ X) (v : W' ⟶ Y' ⋙ X') :
    CompLaw s i j u v ↔ s.hom ≫ whiskerLeft H v =
      whiskerRight u F ≫ whiskerLeft Y i.hom ≫ whiskerRight j.hom X' :=
  ⟨fun h => NatTrans.ext (funext h),fun h z => NatTrans.congr_app h z⟩
variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
theorem compLaw {X : A₂ ⥤ A₁} {Y : A₃ ⥤ A₂} {W : A₃ ⥤ A₁}
    {X' : B₂ ⥤ B₁} {Y' : B₃ ⥤ B₂} {W' : B₃ ⥤ B₁}
    {X'' : C₂ ⥤ C₁} {Y'' : C₃ ⥤ C₂} {W'' : C₃ ⥤ C₁}
    {F : A₁ ⥤ B₁} {G : A₂ ⥤ B₂} {H : A₃ ⥤ B₃}
    {J : B₁ ⥤ C₁} {K : B₂ ⥤ C₂} {L : B₃ ⥤ C₃}
    (s : W ⋙ F ≅ H ⋙ W') (i : X ⋙ F ≅ G ⋙ X') (j : Y ⋙ G ≅ H ⋙ Y')
    (t : W' ⋙ J ≅ L ⋙ W'') (p : X' ⋙ J ≅ K ⋙ X'') (q : Y' ⋙ K ≅ L ⋙ Y'')
    (u : W ⟶ Y ⋙ X) (v : W' ⟶ Y' ⋙ X') (w : W'' ⟶ Y'' ⋙ X'')
    (hf : CompLaw s i j u v) (hg : CompLaw t p q v w) :
    CompLaw (SpanPayload.pasteIso s.symm t.symm).symm
      (SpanPayload.pasteIso i.symm p.symm).symm (SpanPayload.pasteIso j.symm q.symm).symm u w := by
  intro z
  simp only [SpanPayload.pasteIso,Iso.symm_hom,Iso.trans_inv,NatTrans.comp_app,associator_inv_app,associator_hom_app,isoWhiskerRight_inv,isoWhiskerLeft_inv,Iso.symm_inv,whiskerRight_app,whiskerLeft_app,Category.id_comp,Category.comp_id]
  exact comp J X'' _ _ _ _ _ _ _ _ _ _ _ (hf z) (hg (H.obj z)) (p.hom.naturality (j.hom.app z))
end Paste
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (S : P.Split) (Y : Bᵒᵖ ⥤ Cat.{v,u})
theorem evalUnit (n : Nat) (A : B) :
    Paste.UnitLaw (X := nativeReindex Y S n (𝟙 A)) (F := eval S Y n A)
      (Y := ((Evaluation.G S Y n).map (𝟙 A).op).toFunctor)
      (evalSquare S Y n (𝟙 A)) (nativeId Y S n A).hom (eqToHom (strictUnit (Evaluation.G S Y n) A)) :=
  Paste.unitLaw (Evaluation.fibreSquare S Y n (𝟙 A)) (valueSquare (Evaluation.G S Y n) (𝟙 A))
    _ (Route.unitIso (Evaluation.iterateChoice S Y n) A).hom _ (fun x => NatTrans.congr_app (fibreUnit S Y n A) x)
    (fun x => NatTrans.congr_app (valueUnit (Evaluation.G S Y n) A) x)
theorem evalComp (n : Nat) {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (X := nativeReindex Y S n a) (Y := nativeReindex Y S n b)
      (W := nativeReindex Y S n (a ≫ b)) (F := eval S Y n A) (G := eval S Y n D) (H := eval S Y n E)
      (X' := ((Evaluation.G S Y n).map a.op).toFunctor)
      (Y' := ((Evaluation.G S Y n).map b.op).toFunctor)
      (W' := ((Evaluation.G S Y n).map (a ≫ b).op).toFunctor)
      (evalSquare S Y n (a ≫ b)) (evalSquare S Y n a) (evalSquare S Y n b)
      (nativeComp Y S n a b).hom (eqToHom (strictComp (Evaluation.G S Y n) a b)) :=
  Paste.compLaw (Evaluation.fibreSquare S Y n (a ≫ b)) (Evaluation.fibreSquare S Y n a) (Evaluation.fibreSquare S Y n b)
    (valueSquare (Evaluation.G S Y n) (a ≫ b)) (valueSquare (Evaluation.G S Y n) a) (valueSquare (Evaluation.G S Y n) b)
    _ (Route.compIso (Evaluation.iterateChoice S Y n) a b).hom _ (fun x => NatTrans.congr_app (fibreComp S Y n a b) x)
    (fun x => NatTrans.congr_app (valueComp (Evaluation.G S Y n) a b) x)
end ContextualComposition.GrothendieckStep.FibreValue
