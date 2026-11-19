module
public import ContextualComposition.ContextadFinal
public import ContextualComposition.EvalPaste
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadCoherence
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage ContextadTotal FibreValue
set_option backward.isDefEq.respectTransparency false
universe u v
section Embed
variable {B : Type*} [Category* B] (G : Bᵒᵖ ⥤ Cat.{v,u})
theorem fibrePure {A : B} {x y : (proj G).Fiber A} (f : x ⟶ y)
    (h : Pure (payloadMap f.val)) : Pure f := by
  obtain ⟨e,he⟩ := valuePure G f h
  refine ⟨(represent G x).symm.trans ((congrArg (embed G A).obj e).trans (represent G y)), ?_⟩
  let : (value G A).IsEquivalence := (valueEquiv G A).isEquivalence_functor
  apply (value G A).map_injective
  rw [he,eqToHom_map]
theorem embedUnit (A : B) :
    Paste.UnitLaw (square G (𝟙 A)) (eqToHom (strictUnit G A)) (Route.unitIso (choice G) A).hom := by
  intro x
  apply pureEq
  · exact pureComp ⟨_,squareApp G _ _⟩ (fibrePure G _ (unitPure G _ _))
  · exact pureMap _ ⟨_,eqToHom_app _ _⟩
theorem embedComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (square G (a ≫ b)) (square G a) (square G b)
      (eqToHom (strictComp G a b)) (Route.compIso (choice G) a b).hom := by
  intro x
  apply pureEq
  · exact pureComp ⟨_,squareApp G _ _⟩ (fibrePure G _ (compPure G a b _))
  · exact pureComp (pureMap _ ⟨_,eqToHom_app _ _⟩)
      (pureComp ⟨_,squareApp G _ _⟩ (pureMap _ ⟨_,squareApp G _ _⟩))
end Embed
section Decoded
variable {B : Type*} [Category* B] (G H : Bᵒᵖ ⥤ Cat.{v,u})
variable (F : Total G (𝟭 B) ⥤ Total H (𝟭 B))
  (over : F ⋙ proj H = proj G)
  (pres : ∀ {x y : Total G (𝟭 B)} (f : x ⟶ y), Cartesian (proj G) f → Cartesian (proj H) (F.map f))
noncomputable abbrev middle {A D : B} (a : D ⟶ A) :=
  Change.square F over (Route.ofChoice (choice G) a) (Route.ofChoice (choice H) a) pres
noncomputable abbrev paste {A D : B} (a : D ⟶ A) :=
  (SpanPayload.pasteIso ((SpanPayload.pasteIso (square G a).symm (middle G H F over pres a).symm).symm).symm
    (valueSquare H a).symm).symm
theorem pasteHom {A D : B} (a : D ⟶ A) :
    (ContextadTotal.valueSquare G H F over pres a).hom = (paste G H F over pres a).hom := by
  ext x : 2
  simp [ContextadTotal.valueSquare,SpanPayload.pasteIso]
theorem decodedUnit (A : B) :
    Paste.UnitLaw (ContextadTotal.valueSquare G H F over pres (𝟙 A))
      (eqToHom (strictUnit G A)) (eqToHom (strictUnit H A)) := by
  have J := Paste.unitLaw _ (middle G H F over pres (𝟙 A)) _ _ _ (embedUnit G A)
    ((Paste.unitDiagram_iff _ _ _).mpr (Laws.unitDiagram _ _ over pres (choice G) (choice H) A))
  have K := Paste.unitLaw _ _ _ _ _ J ((Paste.unitDiagram_iff _ _ _).mpr (valueUnit H A))
  intro x
  rw [pasteHom]
  exact K x
theorem decodedComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (ContextadTotal.valueSquare G H F over pres (a ≫ b))
      (ContextadTotal.valueSquare G H F over pres a) (ContextadTotal.valueSquare G H F over pres b)
      (eqToHom (strictComp G a b)) (eqToHom (strictComp H a b)) := by
  have J := Paste.compLaw _ _ _ (middle G H F over pres (a ≫ b)) (middle G H F over pres a)
    (middle G H F over pres b) _ _ _ (embedComp G a b)
    ((Paste.compDiagram_iff _ _ _ _ _).mpr (Laws.compDiagram _ _ over pres (choice G) (choice H) a b))
  have K := Paste.compLaw _ _ _ _ _ _ _ _ _ J ((Paste.compDiagram_iff _ _ _ _ _).mpr (valueComp H a b))
  intro x
  rw [pasteHom,pasteHom,pasteHom]
  exact K x
end Decoded
section Transport
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]
noncomputable def transportIso {X : C₂ ⥤ C₁} {Y : D₂ ⥤ D₁}
    {F F' : C₁ ⥤ D₁} {G G' : C₂ ⥤ D₂} (f : F' = F) (g : G' = G)
    (i : X ⋙ F ≅ G ⋙ Y) : X ⋙ F' ≅ G' ⋙ Y :=
  eqToIso (congrArg (X ⋙ ·) f) ≪≫ i ≪≫ eqToIso (congrArg (· ⋙ Y) g.symm)
theorem transportUnit {X : C₁ ⥤ C₁} {Y : D₁ ⥤ D₁} {F F' : C₁ ⥤ D₁}
    (f : F' = F) (i : X ⋙ F ≅ F ⋙ Y) (s : X ⟶ 𝟭 _) (t : Y ⟶ 𝟭 _)
    (h : Paste.UnitLaw i s t) : Paste.UnitLaw (transportIso f f i) s t := by
  subst F'
  intro x
  simpa [transportIso] using h x
theorem transportComp {X : C₂ ⥤ C₁} {Y : C₃ ⥤ C₂} {W : C₃ ⥤ C₁}
    {X' : D₂ ⥤ D₁} {Y' : D₃ ⥤ D₂} {W' : D₃ ⥤ D₁}
    {F F' : C₁ ⥤ D₁} {G G' : C₂ ⥤ D₂} {H H' : C₃ ⥤ D₃}
    (f : F' = F) (g : G' = G) (h : H' = H)
    (i : W ⋙ F ≅ H ⋙ W') (j : X ⋙ F ≅ G ⋙ X') (k : Y ⋙ G ≅ H ⋙ Y')
    (s : W ⟶ Y ⋙ X) (t : W' ⟶ Y' ⋙ X') (e : Paste.CompLaw i j k s t) :
    Paste.CompLaw (transportIso f h i) (transportIso f g j) (transportIso g h k) s t := by
  subst F'; subst G'; subst H'
  intro x
  simpa [transportIso] using e x
end Transport
section Native
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (m : ContextadTotal.Native S) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev source := PackedFree.pow S Y 2
abbrev target := PackedFree.pow S Y 1
noncomputable abbrev actual := ContextadTensor.binary (ContextadSpecialize.data m) Y
noncomputable abbrev exterior {A D : B} (a : D ⟶ A) := ContextadFinal.nativeExterior m Y a
theorem unit (A : B) :
    Paste.UnitLaw (exterior m Y (𝟙 A))
      (eqToHom (strictUnit (source (S := S) Y) A)) (eqToHom (strictUnit (target (S := S) Y) A)) :=
  transportUnit (ContextadFinal.identify m _ Y A (ContextadSpecialize.agrees m A)) _ _ _
    (decodedUnit _ _ (total m Y) (totalOver m Y) (totalCart m Y) A)
theorem comp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (exterior m Y (a ≫ b)) (exterior m Y a) (exterior m Y b)
      (eqToHom (strictComp (source (S := S) Y) a b)) (eqToHom (strictComp (target (S := S) Y) a b)) :=
  transportComp (ContextadFinal.identify m _ Y A (ContextadSpecialize.agrees m A))
    (ContextadFinal.identify m _ Y D (ContextadSpecialize.agrees m D))
    (ContextadFinal.identify m _ Y E (ContextadSpecialize.agrees m E)) _ _ _ _ _
    (decodedComp _ _ (total m Y) (totalOver m Y) (totalCart m Y) a b)
end Native
end ContextualComposition.GrothendieckStep.ContextadCoherence
