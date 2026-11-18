module
public import ContextualComposition.TaggedBaseLaws
/-! Base coherence of the all-length evaluation. A forward square is given in
the orientation comparing then pulling; its inverse mate is the particular
one built by SumChange.inverseSquare, not an independently chosen square. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MateLaws
open CategoryTheory CategoryTheory.Functor Opposite FibreValue SumChange
variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]

/-- Decode an arrow into the inverse by using the actual counit. -/
def decode (M : E ≌ F) {a : E} {b : F} (f : a ⟶ M.inverse.obj b) :
    M.functor.obj a ⟶ b := M.functor.map f ≫ M.counit.app b
theorem decode_inj (M : E ≌ F) {a : E} {b : F} {f g : a ⟶ M.inverse.obj b}
    (h : decode M f = decode M g) : f = g :=
  M.functor.map_injective ((cancel_mono (M.counit.app b)).mp h)
theorem decode_left (M : E ≌ F) {a a' : E} {b : F} (f : a ⟶ a') (g : a' ⟶ M.inverse.obj b) :
    decode M (f ≫ g) = M.functor.map f ≫ decode M g := by simp [decode]
theorem decode_right (M : E ≌ F) {a : E} {b b' : F} (f : a ⟶ M.inverse.obj b) (g : b ⟶ b') :
    decode M (f ≫ M.inverse.map g) = decode M f ≫ g := by
  simp [decode, Category.assoc]
/-- The mate factors, after applying the equivalence functor and counit,
through the given forward cell at the inverse object and the starting counit. -/
theorem mate_fac (L : C ≌ D) (M : E ≌ F) {s : C ⥤ E} {t : D ⥤ F}
    (h : L.functor ⋙ t ≅ s ⋙ M.functor) (x : D) :
    decode M ((inverseSquare L M h).hom.app x) =
      h.inv.app (L.inverse.obj x) ≫ t.map (L.counit.app x) := by
  simp [inverseSquare, Iso.inverseCompIso, Iso.compInverseIso, decode, Category.assoc]
theorem unit (L : C ≌ D) {s : C ⥤ C} {t : D ⥤ D} (h : L.functor ⋙ t ≅ s ⋙ L.functor)
    (u : s ⟶ 𝟭 _) (v : t ⟶ 𝟭 _) (forward : Paste.UnitLaw h.symm u v) :
    Paste.UnitLaw (inverseSquare L L h).symm v u := by
  intro x
  apply (cancel_epi ((inverseSquare L L h).hom.app x)).mp
  rw [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply decode_inj L
  rw [decode_right,mate_fac]
  change L.functor.map (u.app (L.inverse.obj x)) ≫ L.counit.app x = _
  rw [← forward (L.inverse.obj x), Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (v.naturality (L.counit.app x)).symm

private theorem flip {A : Type*} [Category* A] {a b c d : A}
    (i : a ≅ b) (j : c ≅ d) (u : a ⟶ c) (v : b ⟶ d)
    (h : u ≫ j.hom = i.hom ≫ v) : i.inv ≫ u = v ≫ j.inv := by
  calc
    _ = i.inv ≫ (u ≫ j.hom) ≫ j.inv := by simp
    _ = _ := by rw [h]; simp
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃]
theorem comp (M : C₁ ≌ D₁) (N : C₂ ≌ D₂) (L : C₃ ≌ D₃)
    {X : C₂ ⥤ C₁} {Y : C₃ ⥤ C₂} {W : C₃ ⥤ C₁}
    {X' : D₂ ⥤ D₁} {Y' : D₃ ⥤ D₂} {W' : D₃ ⥤ D₁}
    (d : L.functor ⋙ W' ≅ W ⋙ M.functor) (a : N.functor ⋙ X' ≅ X ⋙ M.functor)
    (b : L.functor ⋙ Y' ≅ Y ⋙ N.functor) (u : W ⟶ Y ⋙ X) (v : W' ⟶ Y' ⋙ X')
    (forward : Paste.CompLaw d.symm a.symm b.symm u v) :
    Paste.CompLaw (inverseSquare L M d).symm (inverseSquare N M a).symm (inverseSquare L N b).symm v u := by
  intro x
  let ma := inverseSquare N M a
  let mb := inverseSquare L N b
  let md := inverseSquare L M d
  let k := X.mapIso (mb.app x) ≪≫ ma.app (Y'.obj x)
  apply flip (md.app x) k (u.app (L.inverse.obj x)) (M.inverse.map (v.app x))
  apply decode_inj M
  change decode M (u.app _ ≫ X.map (mb.hom.app x) ≫ ma.hom.app _) = decode M (md.hom.app x ≫ M.inverse.map (v.app x))
  rw [decode_left,decode_left,decode_right,mate_fac,mate_fac]
  rw [Category.assoc]
  have nat := a.inv.naturality (mb.hom.app x)
  change M.functor.map (X.map (mb.hom.app x)) ≫ a.inv.app _ =
    a.inv.app _ ≫ X'.map (N.functor.map (mb.hom.app x)) at nat
  rw [reassoc_of% nat, ← X'.map_comp]
  change _ ≫ _ ≫ X'.map (decode N (mb.hom.app x)) = _
  rw [mate_fac,X'.map_comp]
  have h := forward (L.inverse.obj x)
  simp only [Iso.symm_hom] at h
  have nv := v.naturality (L.counit.app x)
  change W'.map (L.counit.app x) ≫ v.app x =
    v.app _ ≫ X'.map (Y'.map (L.counit.app x)) at nv
  rw [nv]
  exact ((reassoc_of% h) _).symm
/-- Change the presentation of the source pull; the comparison gets the
same endpoint transport as the functor on which the constraint is evaluated. -/
def adjust {H : C ⥤ D} {J : E ⥤ F} {U V : C ⥤ E} {T : D ⥤ F}
    (h : H ⋙ T ≅ U ⋙ J) (e : U = V) : H ⋙ T ≅ V ⋙ J :=
  h ≪≫ eqToIso (congrArg (· ⋙ J) e)
theorem adjustUnit {U V : C ⥤ C} {T : D ⥤ D} {J : C ⥤ D}
    (h : J ⋙ T ≅ U ⋙ J) (e : U = V) (u : U ⟶ 𝟭 _) (v : V ⟶ 𝟭 _) (w : T ⟶ 𝟭 _)
    (bridge : eqToHom e ≫ v = u) (law : Paste.UnitLaw h.symm u w) :
    Paste.UnitLaw (adjust h e).symm v w := by
  subst V; simp only [eqToHom_refl,Category.id_comp] at bridge
  subst u; simpa [adjust] using law
theorem adjustComp {M : C₁ ⥤ D₁} {N : C₂ ⥤ D₂} {L : C₃ ⥤ D₃}
    {X XX : C₂ ⥤ C₁} {Y YY : C₃ ⥤ C₂} {W WW : C₃ ⥤ C₁}
    {X' : D₂ ⥤ D₁} {Y' : D₃ ⥤ D₂} {W' : D₃ ⥤ D₁}
    (d : L ⋙ W' ≅ W ⋙ M) (a : N ⋙ X' ≅ X ⋙ M) (b : L ⋙ Y' ≅ Y ⋙ N)
    (ed : W = WW) (ea : X = XX) (eb : Y = YY) (u : W ⟶ Y ⋙ X) (v : WW ⟶ YY ⋙ XX) (w : W' ⟶ Y' ⋙ X')
    (bridge : eqToHom ed ≫ v = u ≫ eqToHom (congrArg₂ (· ⋙ ·) eb ea))
    (law : Paste.CompLaw d.symm a.symm b.symm u w) :
    Paste.CompLaw (adjust d ed).symm (adjust a ea).symm (adjust b eb).symm v w := by
  subst WW; subst XX; subst YY
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id] at bridge
  subst u; simpa [adjust] using law

end ContextualComposition.GrothendieckStep.MateLaws


namespace ContextualComposition.GrothendieckStep.MateLaws.All
open CategoryTheory CategoryTheory.Functor Opposite FibreValue SumChange CoproductSpan CoproductSpan.All
open SpanPull SpanPull.All TaggedBaseLaws
universe b w
variable {B : Type b} [Category.{w} B] {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (Y : Bᵒᵖ ⥤ Cat.{w,b})
noncomputable abbrev presentation (A : B) := (compare (src R) (dst R) A Y).asEquivalence
noncomputable abbrev taggedPull {A D : B} (a : A ⟶ D) := ZeroPower.Sum.map (leafPull R Y a)
noncomputable abbrev wholeUnit (A : B) := (PullLaws.wholeUnit (src R) (dst R) (parts R) Y A).hom
noncomputable abbrev wholeComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :=
  (PullLaws.wholeComp (src R) (dst R) (parts R) Y a b).hom

theorem comparisonUnit (A : B) : Paste.UnitLaw (F := (presentation R Y A).functor)
    (X := taggedPull R Y (𝟙 A)) (Y := pull R Y (𝟙 A))
    (comparison R Y (𝟙 A)).symm (sourceUnit R Y A) (wholeUnit R Y A) :=
  adjustUnit (forward (src R) (dst R) (parts R) Y (𝟙 A)) (sourceEq R Y (𝟙 A)) _ _ _
    (sourceEq_unit R Y A) (PullLaws.forwardUnit (src R) (dst R) (parts R) Y A)
theorem comparisonComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (F := (presentation R Y A).functor) (G := (presentation R Y D).functor) (H := (presentation R Y E).functor)
      (X := taggedPull R Y a) (Y := taggedPull R Y b) (W := taggedPull R Y (a ≫ b))
      (X' := pull R Y a) (Y' := pull R Y b) (W' := pull R Y (a ≫ b))
      (comparison R Y (a ≫ b)).symm (comparison R Y a).symm (comparison R Y b).symm
      (sourceComp R Y a b) (wholeComp R Y a b) :=
  adjustComp (forward (src R) (dst R) (parts R) Y (a ≫ b)) (forward (src R) (dst R) (parts R) Y a)
    (forward (src R) (dst R) (parts R) Y b) (sourceEq R Y (a ≫ b)) (sourceEq R Y a) (sourceEq R Y b)
    _ _ _ (sourceEq_comp R Y a b) (PullLaws.forwardComp (src R) (dst R) (parts R) Y a b)
noncomputable abbrev mate {A D : B} (a : A ⟶ D) :=
  inverseSquare (presentation R Y D) (presentation R Y A) (comparison R Y a)
theorem mateUnit (A : B) : Paste.UnitLaw (F := (presentation R Y A).inverse)
    (X := pull R Y (𝟙 A)) (Y := taggedPull R Y (𝟙 A))
    (mate R Y (𝟙 A)).symm (wholeUnit R Y A) (sourceUnit R Y A) :=
  unit (presentation R Y A) _ _ _ (comparisonUnit R Y A)
theorem mateComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (F := (presentation R Y A).inverse) (G := (presentation R Y D).inverse) (H := (presentation R Y E).inverse)
      (X := pull R Y a) (Y := pull R Y b) (W := pull R Y (a ≫ b))
      (X' := taggedPull R Y a) (Y' := taggedPull R Y b) (W' := taggedPull R Y (a ≫ b))
      (mate R Y (a ≫ b)).symm (mate R Y a).symm (mate R Y b).symm (wholeComp R Y a b) (sourceComp R Y a b) :=
  comp (presentation R Y A) (presentation R Y D) (presentation R Y E) _ _ _ _ _ (comparisonComp R Y a b)
theorem evaluationUnit (A : B) : Paste.UnitLaw (F := (evaluation R Y A).functor)
    (X := pull R Y (𝟙 A)) (Y := Iterates.packedMap Q R Y (𝟙 A).op)
    (evaluationBase R Y (𝟙 A)) (wholeUnit R Y A) (eqToHom (Iterates.packedMap_id Q R Y (op A))) :=
  Paste.unitLaw (mate R Y (𝟙 A)).symm (taggedBase R Y (𝟙 A)) _ _ _ (mateUnit R Y A) (taggedUnitLaw R Y A)
theorem evaluationComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (F := (evaluation R Y A).functor) (G := (evaluation R Y D).functor) (H := (evaluation R Y E).functor)
      (X := pull R Y a) (Y := pull R Y b) (W := pull R Y (a ≫ b))
      (X' := Iterates.packedMap Q R Y a.op) (Y' := Iterates.packedMap Q R Y b.op)
      (W' := Iterates.packedMap Q R Y (a ≫ b).op)
      (evaluationBase R Y (a ≫ b)) (evaluationBase R Y a) (evaluationBase R Y b)
      (wholeComp R Y a b) (eqToHom (Iterates.packedMap_comp Q R Y b.op a.op)) :=
  Paste.compLaw (mate R Y (a ≫ b)).symm (mate R Y a).symm (mate R Y b).symm
    (taggedBase R Y (a ≫ b)) (taggedBase R Y a) (taggedBase R Y b)
    _ _ _ (mateComp R Y a b) (taggedCompLaw R Y a b)
/-- Transformation-level form of the fixed-payload identity diagram. -/
theorem evaluationUnitDiagram (A : B) :
    (evaluationBase R Y (𝟙 A)).hom ≫ whiskerLeft (evaluation R Y A).functor (eqToHom (Iterates.packedMap_id Q R Y (op A))) =
      whiskerRight (wholeUnit R Y A) (evaluation R Y A).functor :=
  (Paste.unitDiagram_iff _ _ _).mp (evaluationUnit R Y A)
/-- Transformation-level form: the single pull of the composite is compared
with pulling along the second arrow and then along the first. -/
theorem evaluationCompDiagram {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    (evaluationBase R Y (a ≫ b)).hom ≫
      whiskerLeft (evaluation R Y E).functor (eqToHom (Iterates.packedMap_comp Q R Y b.op a.op)) =
    whiskerRight (wholeComp R Y a b) (evaluation R Y A).functor ≫
      whiskerLeft (pull R Y b) (evaluationBase R Y a).hom ≫
      whiskerRight (evaluationBase R Y b).hom (Iterates.packedMap Q R Y a.op) :=
  (Paste.compDiagram_iff _ _ _ _ _).mp (evaluationComp R Y a b)
end ContextualComposition.GrothendieckStep.MateLaws.All
