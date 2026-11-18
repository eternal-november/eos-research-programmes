module
public import ContextualComposition.ForwardMixed
/-! A mixed square transfers through four chosen equivalences by mating both
paths against one common diagonal. The two mixed cells need not be invertible. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MixedMates
open CategoryTheory CategoryTheory.Functor Opposite FinalCube TaggedMixed SumChange
/-- Chosen equivalences at all four vertices with the four invertible edge
comparisons oriented as inputs to the existing inverseSquare construction. -/
structure Frame (X Y : Mix.Grid) where
  f : X.A ≌ Y.A
  g : X.D ≌ Y.D
  f' : X.A' ≌ Y.A'
  g' : X.D' ≌ Y.D'
  s : g.functor ⋙ Y.b ≅ X.b ⋙ f.functor
  t : g'.functor ⋙ Y.b' ≅ X.b' ⋙ f'.functor
  l : f.functor ⋙ Y.p ≅ X.p ⋙ f'.functor
  r : g.functor ⋙ Y.q ≅ X.q ⋙ g'.functor
namespace Frame
variable {X Y : Mix.Grid} (M : Frame X Y)
def forward : Cube.Map X Y :=
  ⟨M.f.functor,M.g.functor,M.f'.functor,M.g'.functor,M.s.inv,M.t.inv,M.l.inv,M.r.inv⟩
def reverse : Frame Y X :=
  ⟨M.f.symm,M.g.symm,M.f'.symm,M.g'.symm,
   inverseSquare M.g M.f M.s,inverseSquare M.g' M.f' M.t,
   inverseSquare M.f M.f' M.l,inverseSquare M.g M.g' M.r⟩
/-- The before-payload route fixes a single diagonal; the other route is
tested against that same diagonal using the mixed cell. -/
def diagonal : M.g.functor ⋙ (Y.b ⋙ Y.p) ≅ (X.b ⋙ X.p) ⋙ M.f'.functor :=
  isoWhiskerRight M.s Y.p ≪≫ isoWhiskerLeft X.b M.l
theorem first : FibreValue.Paste.CompLaw M.diagonal.symm M.l.symm M.s.symm (𝟙 _) (𝟙 _) := by
  intro x
  simp [diagonal]
theorem second (h : Cube.Law M.forward) :
    FibreValue.Paste.CompLaw M.diagonal.symm M.t.symm M.r.symm X.cell Y.cell := by
  intro x
  have e := h x
  change (M.f'.functor.map (X.cell.app x) ≫ M.t.inv.app _) ≫ Y.b'.map (M.r.inv.app _) =
    M.l.inv.app _ ≫ Y.p.map (M.s.inv.app _) ≫ Y.cell.app _ at e
  simpa [diagonal,Category.assoc] using e.symm
/-- Both path laws must use the same diagonal. Its component then cancels
by substitution; neither mixed cell needs an inverse. -/
theorem ofPaths (d : M.g.functor ⋙ (Y.b ⋙ Y.p) ≅ (X.b ⋙ X.p) ⋙ M.f'.functor)
    (i : FibreValue.Paste.CompLaw d.symm M.l.symm M.s.symm (𝟙 _) (𝟙 _))
    (j : FibreValue.Paste.CompLaw d.symm M.t.symm M.r.symm X.cell Y.cell) : Cube.Law M.forward := by
  intro x
  have firstPath := i x
  simp only [Iso.symm_hom,NatTrans.id_app,Functor.map_id,Category.id_comp] at firstPath
  have e := (Category.comp_id (d.inv.app x)).symm.trans firstPath
  have secondPath := j x
  simp only [Iso.symm_hom] at secondPath
  rw [e] at secondPath
  simpa only [forward,Category.assoc] using secondPath.symm
theorem backLaw (h : Cube.Law M.forward) : Cube.Law M.reverse.forward :=
  M.reverse.ofPaths (inverseSquare M.g M.f' M.diagonal)
    (MateLaws.comp M.f' M.f M.g M.diagonal M.l M.s (𝟙 _) (𝟙 _) M.first)
    (MateLaws.comp M.f' M.g' M.g M.diagonal M.t M.r X.cell Y.cell (M.second h))
variable {Z : Mix.Grid} (N : Frame Y Z)
def compose : Frame X Z :=
  ⟨M.f.trans N.f,M.g.trans N.g,M.f'.trans N.f',M.g'.trans N.g',
   SpanPayload.pasteIso M.s N.s,SpanPayload.pasteIso M.t N.t,
   SpanPayload.pasteIso M.l N.l,SpanPayload.pasteIso M.r N.r⟩
theorem composeLaw (h : Cube.Law M.forward) (k : Cube.Law N.forward) : Cube.Law (M.compose N).forward :=
  (M.compose N).ofPaths (SpanPayload.pasteIso M.diagonal N.diagonal)
    (FibreValue.Paste.compLaw M.diagonal.symm M.l.symm M.s.symm N.diagonal.symm N.l.symm N.s.symm
      (𝟙 _) (𝟙 _) (𝟙 _) M.first N.first)
    (FibreValue.Paste.compLaw M.diagonal.symm M.t.symm M.r.symm N.diagonal.symm N.t.symm N.r.symm
      X.cell Y.cell Z.cell (M.second h) (N.second k))
end Frame
namespace All
open CoproductSpan CoproductSpan.All SpanPull.All
universe b w
variable {B : Type b} [Category.{w} B] {Q : Endpoints.{b,w,b,w} B} (R : Q.Split)
  {Y Z : Bᵒᵖ ⥤ Cat.{w,b}} (T : Y ⟶ Z)
noncomputable def presentation {A D : B} (a : A ⟶ D) :
    Frame (TaggedMixed.All.taggedGrid R T a) (ForwardMixed.All.wholeGrid R T a) where
  f := (compare (src R) (dst R) A Y).asEquivalence
  g := (compare (src R) (dst R) D Y).asEquivalence
  f' := (compare (src R) (dst R) A Z).asEquivalence
  g' := (compare (src R) (dst R) D Z).asEquivalence
  s := comparison R Y a
  t := comparison R Z a
  l := eqToIso (compare_payload (src R) (dst R) A Y T)
  r := eqToIso (compare_payload (src R) (dst R) D Y T)
noncomputable def tagged {A D : B} (a : A ⟶ D) :
    Frame (TaggedMixed.All.taggedGrid R T a) (values (ChainPayload.allIterateMap T R) a) where
  f := ZeroPower.Sum.equiv (component R Y A)
  g := ZeroPower.Sum.equiv (component R Y D)
  f' := ZeroPower.Sum.equiv (component R Z A)
  g' := ZeroPower.Sum.equiv (component R Z D)
  s := (taggedBase R Y a).symm
  t := (taggedBase R Z a).symm
  l := taggedPayload R T A
  r := taggedPayload R T D
theorem inverseLaw {A D : B} (a : A ⟶ D) : Cube.Law (presentation R T a).reverse.forward :=
  (presentation R T a).backLaw (ForwardMixed.All.law R T a)
theorem inverseDiagram {A D : B} (a : A ⟶ D) : ForwardMixed.Commuting (presentation R T a).reverse.forward :=
  ForwardMixed.commuting _ (inverseLaw R T a)
/-- The four faces here are the previously defined *final* comparison isomorphisms. -/
noncomputable def evaluationCube {A D : B} (a : A ⟶ D) :
    Cube.Map (ForwardMixed.All.wholeGrid R T a) (values (ChainPayload.allIterateMap T R) a) where
  f := (evaluation R Y A).functor
  g := (evaluation R Y D).functor
  f' := (evaluation R Z A).functor
  g' := (evaluation R Z D).functor
  s := (evaluationBase R Y a).hom
  t := (evaluationBase R Z a).hom
  l := (evaluationPayload R T A).inv
  r := (evaluationPayload R T D).inv
theorem evaluationLaw {A D : B} (a : A ⟶ D) : Cube.Law (evaluationCube R T a) :=
  (presentation R T a).reverse.composeLaw (tagged R T a) (inverseLaw R T a) (TaggedMixed.All.taggedLaw R T a)
/-- Equality of the full natural transformations, with the whole-span source
mixed comparison and the naturality face of the actual packed iterate map. -/
theorem evaluationDiagram {A D : B} (a : A ⟶ D) : ForwardMixed.Commuting (evaluationCube R T a) :=
  ForwardMixed.commuting _ (evaluationLaw R T a)
end All
end ContextualComposition.GrothendieckStep.MixedMates
