module
public import ContextualComposition.NativeCube
/-! Mixed base/payload coherence of the actual positive evaluation. A grid keeps the two comparison arrows and the two independent endpoint corrections. Pasting uses the middle payload transformation and actual inner comparisons. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.FinalCube
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage TelescopeSquares
namespace Align
variable {C D : Type*} [Category* C] [Category* D]
theorem uncorrect {E : Type*} [Category* E] (F : E ⥤ C)
    {a a' : C} {b b' : E} {f : a ⟶ F.obj b} {g : a' ⟶ F.obj b'}
    (hs : a = a') (ht : b = b') (h : f ≫ F.map (eqToHom ht) = eqToHom hs ≫ g) : Aligned f g := by
  rw [eqToHom_map] at h; exact ⟨hs,_,h⟩
theorem atEq {F G : C ⥤ D} (s : F ⟶ G) {x y : C} (e : x = y) : Aligned (s.app x) (s.app y) := by subst y; exact Aligned.refl _
theorem stripPresent {X V V' W W' Z : Type*} [Category* X] [Category* V] [Category* V'] [Category* W] [Category* W'] [Category* Z]
    (I : X ⥤ V) (O : W' ⥤ Z) (U : V ⥤ W) (R : V' ⥤ W') (L : W ⥤ W') (H : V ⥤ V')
    (U' : W ⥤ Z) (R' : X ⥤ V') (s : U ⋙ L ≅ H ⋙ R)
    (h : U' = L ⋙ O) (k : I ⋙ H = R') (x : X) :
    Aligned ((NativeCube.present I O U R L H U' R' s h k).hom.app x) (O.map (s.hom.app (I.obj x))) := by
  subst U'; subst R'
  exact NativeCube.ofEq (by simp [NativeCube.present])
end Align
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (S : P.Split) {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
open SpanApex SpanPayload.Power
theorem sourceAlign (n : Nat) {A D : B} (a : A ⟶ D) (x : Total Y (nativeEndpoint S n D)) :
    Aligned ((FibreTotal.into Z _ _ A).map ((NativeCube.presentedSquare S T n a).hom.app x))
      ((PayloadLift.nativeSquare T S n a).hom.app ((FibreTotal.into Y _ _ D).obj x)) :=
  (Align.stripPresent _ _ _ _ _ _ _ _ _ _ _ x).map (FibreTotal.into Z _ _ A)
namespace Mix
structure Grid where
  A : Type*
  D : Type*
  A' : Type*
  D' : Type*
  [ca : Category* A]
  [cd : Category* D]
  [ca' : Category* A']
  [cd' : Category* D']
  b : D ⥤ A
  b' : D' ⥤ A'
  p : A ⥤ A'
  q : D ⥤ D'
  cell : b ⋙ p ⟶ q ⋙ b'
attribute [instance] Grid.ca Grid.cd Grid.ca' Grid.cd'
structure Map (X : Grid) (Y : Grid) where
  f : X.A ⥤ Y.A
  g : X.D ⥤ Y.D
  f' : X.A' ⥤ Y.A'
  g' : X.D' ⥤ Y.D'
  s : X.b ⋙ f ⟶ g ⋙ Y.b
  t : X.b' ⋙ f' ⟶ g' ⋙ Y.b'
  pa : X.p ⋙ f' = f ⋙ Y.p
  pd : X.q ⋙ g' = g ⋙ Y.q
variable {X : Grid} {Y : Grid} {Z : Grid}
def Law (F : Map X Y) : Prop :=
  ∀ x, Aligned (F.f'.map (X.cell.app x) ≫ F.t.app (X.q.obj x))
    (Y.p.map (F.s.app x) ≫ Y.cell.app (F.g.obj x))
def Diagram (F : Map X Y) : Prop :=
  ∀ x, (F.f'.map (X.cell.app x) ≫ F.t.app (X.q.obj x)) ≫ Y.b'.map (eqToHom (Functor.congr_obj F.pd x)) =
    eqToHom (Functor.congr_obj F.pa (X.b.obj x)) ≫ (Y.p.map (F.s.app x) ≫ Y.cell.app (F.g.obj x))
theorem equation (F : Map X Y) (hf : Law F) (x : X.D) :
    (F.f'.map (X.cell.app x) ≫ F.t.app (X.q.obj x)) ≫ Y.b'.map (eqToHom (Functor.congr_obj F.pd x)) =
      eqToHom (Functor.congr_obj F.pa (X.b.obj x)) ≫ (Y.p.map (F.s.app x) ≫ Y.cell.app (F.g.obj x)) := by
  rw [eqToHom_map]; exact (hf x).comm
theorem lawOfEquation (F : Map X Y) (h : ∀ x, (F.f'.map (X.cell.app x) ≫ F.t.app (X.q.obj x)) ≫ Y.b'.map (eqToHom (Functor.congr_obj F.pd x)) =
      eqToHom (Functor.congr_obj F.pa (X.b.obj x)) ≫ (Y.p.map (F.s.app x) ≫ Y.cell.app (F.g.obj x))) : Law F :=
  fun x => Align.uncorrect Y.b' (Functor.congr_obj F.pa (X.b.obj x)) (Functor.congr_obj F.pd x) (h x)
def join (F : Map X Y) (G : Map Y Z) : Map X Z where
  f := F.f ⋙ G.f
  g := F.g ⋙ G.g
  f' := F.f' ⋙ G.f'
  g' := F.g' ⋙ G.g'
  s := whiskerRight F.s G.f ≫ whiskerLeft F.g G.s
  t := whiskerRight F.t G.f' ≫ whiskerLeft F.g' G.t
  pa := EvalPayload.pasteEq _ _ _ _ _ _ _ F.pa G.pa
  pd := EvalPayload.pasteEq _ _ _ _ _ _ _ F.pd G.pd
theorem joinLaw (F : Map X Y) (G : Map Y Z) (hf : Law F) (hg : Law G) : Law (join F G) := by
  intro x
  change Aligned (G.f'.map (F.f'.map _) ≫ G.f'.map (F.t.app _) ≫ G.t.app (F.g'.obj (X.q.obj x)))
    (Z.p.map (G.f.map (F.s.app x) ≫ G.s.app (F.g.obj x)) ≫ Z.cell.app (G.g.obj (F.g.obj x)))
  apply (NativeCube.ofEq (by rw [← Category.assoc,← Functor.map_comp])).trans
  apply ((hf x).map G.f' |>.comp (Align.atEq G.t (Functor.congr_obj F.pd x))).trans
  apply (NativeCube.ofEq (by rw [Functor.map_comp,Category.assoc])).trans
  apply ((NativeCube.functorAlign G.pa (F.s.app x)).comp (hg (F.g.obj x))).trans
  exact NativeCube.ofEq (by simp [Functor.map_comp,Category.assoc])
theorem replaceLaw (F : Map X Y) (hs ht pa pd) (s : ∀ x, F.s.app x = NatTrans.app hs x) (t : ∀ x, F.t.app x = NatTrans.app ht x) (h : Law F) :
    Law { F with s := hs, t := ht, pa := pa, pd := pd } := by
  intro x
  exact (NativeCube.ofEq (congrArg (_ ≫ ·) (t _).symm)).trans ((h x).trans
    (NativeCube.ofEq (congrArg (fun k => Y.p.map k ≫ _) (s _))))
end Mix
noncomputable def native (n : Nat) {A D : B} (a : A ⟶ D) : Mix.Grid where
  A := Total Y (nativeEndpoint S n A)
  D := Total Y (nativeEndpoint S n D)
  A' := Total Z (nativeEndpoint S n A)
  D' := Total Z (nativeEndpoint S n D)
  b := nativeReindex Y S n a
  b' := nativeReindex Z S n a
  p := ChainPayload.fibreMap T _
  q := ChainPayload.fibreMap T _
  cell := (NativeCube.presentedSquare S T n a).hom
def faceGrid {B K L : Type*} [Category* B] [Category* K] [Category* L] {p : K ⥤ B} {q : L ⥤ B} {A D : B} {a : A ⟶ D}
    {R : Route p a} {Q : Route q a} {F : K ⥤ L} {h : F ⋙ q = p} (i : NativeCube.Face R Q F h) : Mix.Grid where
  A := p.Fiber A
  D := p.Fiber D
  A' := q.Fiber A
  D' := q.Fiber D
  b := R.act
  b' := Q.act
  p := SpanPayload.fibreFunctor F q h A
  q := SpanPayload.fibreFunctor F q h D
  cell := i.sq.hom
noncomputable abbrev fibres {K : Type*} [Category* K] (e p : K ⥤ B) (C : Cleavage p) {A D : B} (a : A ⟶ D) :=
  faceGrid (NativeCube.payload T e p C a)
noncomputable abbrev source (n : Nat) {A D : B} (a : A ⟶ D) :=
  fibres T (positivePowers P S n).dest (positivePowers P S n).source (powerChoice S n) a
noncomputable abbrev target (n : Nat) {A D : B} (a : A ⟶ D) :=
  fibres (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) baseChoice a
def values {A D : B} (a : A ⟶ D) : Mix.Grid where
  A := Y.obj (op A)
  D := Y.obj (op D)
  A' := Z.obj (op A)
  D' := Z.obj (op D)
  b := (Y.map a.op).toFunctor
  b' := (Z.map a.op).toFunctor
  p := (T.app (op A)).toFunctor
  q := (T.app (op D)).toFunctor
  cell := eqToHom (DecoderCube.natural T a)
noncomputable def into (n : Nat) {A D : B} (a : A ⟶ D) : Mix.Map (native S T n a) (source S T n a) where
  f := FibreTotal.into Y _ _ A
  g := FibreTotal.into Y _ _ D
  f' := FibreTotal.into Z _ _ A
  g' := FibreTotal.into Z _ _ D
  s := 𝟙 _
  t := 𝟙 _
  pa := EvalPayload.intoSquare T _ _ A
  pd := EvalPayload.intoSquare T _ _ D
theorem intoLaw (n : Nat) {A D : B} (a : A ⟶ D) : Mix.Law (into S T n a) := by
  intro x
  exact (NativeCube.ofEq (Category.comp_id _)).trans ((sourceAlign S T n a x).trans
    (NativeCube.ofEq (((Category.id_comp _).symm).trans (congrArg (· ≫ _) ((PayloadLift.action T (positivePowers P S n).dest (positivePowers P S n).source A).map_id _).symm))))
section Convert
open NativeCube
variable {BB K L L' M : Type*} [Category* BB] [Category* K] [Category* L] [Category* L'] [Category* M]
    {p : K ⥤ BB} {q : L ⥤ BB} {q' : L' ⥤ BB} {r : M ⥤ BB} {A D : BB} {a : A ⟶ D}
    {R : Route p a} {Q : Route q a} {Q' : Route q' a} {U : Route r a}
    {F : K ⥤ L} {G : L ⥤ M} {F' : K ⥤ L'} {G' : L' ⥤ M}
    {h : F ⋙ q = p} {k : G ⋙ r = q} {h' : F' ⋙ q' = p} {k' : G' ⋙ r = q'}
theorem strictAlign (i : Face R Q F h) (j : Face Q U G k) (i' : Face R Q' F' h') (j' : Face Q' U G' k')
    (ea ed) (law : Face.Law i j i' j' ea ed) (x : p.Fiber D) :
    Aligned (Face.path i j x) (Face.path i' j' x) :=
  Align.uncorrect U.act (Functor.congr_obj ea (R.act.obj x)) (Functor.congr_obj ed x) (law x)
def faceMap (i : Face R Q F h) (j : Face Q U G k) (i' : Face R Q' F' h') (j' : Face Q' U G' k')
    (ea : SpanPayload.fibreFunctor F q h A ⋙ SpanPayload.fibreFunctor G r k A =
      SpanPayload.fibreFunctor F' q' h' A ⋙ SpanPayload.fibreFunctor G' r k' A)
    (ed : SpanPayload.fibreFunctor F q h D ⋙ SpanPayload.fibreFunctor G r k D =
      SpanPayload.fibreFunctor F' q' h' D ⋙ SpanPayload.fibreFunctor G' r k' D) : Mix.Map (faceGrid i) (faceGrid j') where
  f := SpanPayload.fibreFunctor F' q' h' A
  g := SpanPayload.fibreFunctor F' q' h' D
  f' := SpanPayload.fibreFunctor G r k A
  g' := SpanPayload.fibreFunctor G r k D
  s := i'.sq.hom
  t := j.sq.hom
  pa := ea
  pd := ed
theorem faceLaw (i : Face R Q F h) (j : Face Q U G k) (i' : Face R Q' F' h') (j' : Face Q' U G' k')
    (ea ed) (h : Face.Law i j i' j' ea ed) : Mix.Law (faceMap i j i' j' ea ed) :=
  fun x => strictAlign i j i' j' ea ed h x
end Convert
noncomputable abbrev inner (n : Nat) {A D : B} (a : A ⟶ D) :=
  faceMap (NativeCube.sourceFace S T n a) (NativeCube.evaluation S Z n a) (NativeCube.evaluation S Y n a)
    (NativeCube.targetFace S T n a) (EvalPayload.strictSquare T S n A) (EvalPayload.strictSquare T S n D)
theorem innerLaw (n : Nat) {A D : B} (a : A ⟶ D) : Mix.Law (inner S T n a) :=
  faceLaw _ _ _ _ _ _ (NativeCube.strictCube S T n a)
noncomputable def decode {A D : B} (a : A ⟶ D) : Mix.Map (fibres T (𝟭 B) (𝟭 B) baseChoice a) (values T a) where
  f := FibreValue.value Y A
  g := FibreValue.value Y D
  f' := FibreValue.value Z A
  g' := FibreValue.value Z D
  s := (FibreValue.valueSquare Y a).hom
  t := (FibreValue.valueSquare Z a).hom
  pa := EvalPayload.valueSquare T A
  pd := EvalPayload.valueSquare T D
theorem decodeLaw {A D : B} (a : A ⟶ D) : Mix.Law (decode T a) := by
  apply Mix.lawOfEquation
  intro x
  refine (Category.assoc ..).trans ((DecoderCube.mixed T a x).trans ?_)
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (eqToHom_app (DecoderCube.natural T a) ((FibreValue.value Y D).obj x)).symm)
theorem whiskeredBaseY (n : Nat) {A D : B} (a : A ⟶ D) : whiskerLeft (into S T n a).g (inner S T n a).s = (Evaluation.fibreSquare S Y n a).hom := rfl
theorem identityWhisker {X V Y : Type*} [Category* X] [Category* V] [Category* Y] (J : X ⥤ V) (F : V ⥤ Y) {H : X ⥤ Y} (s : J ⋙ F ⟶ H) :
    whiskerRight (𝟙 J) F ≫ s = s := (congrArg (· ≫ s) (whiskerRight_id F)).trans (Category.id_comp s)
theorem presentedBaseY (n : Nat) {A D : B} (a : A ⟶ D) : (Mix.join (into S T n a) (inner S T n a)).s = (Evaluation.fibreSquare S Y n a).hom :=
  (identityWhisker ((into S T n a).g ⋙ (source S T n a).b) (inner S T n a).f
    (whiskerLeft (into S T n a).g (inner S T n a).s)).trans (whiskeredBaseY S T n a)
theorem whiskeredBaseZ (n : Nat) {A D : B} (a : A ⟶ D) : whiskerLeft (into S T n a).g' (inner S T n a).t = (Evaluation.fibreSquare S Z n a).hom := rfl
theorem presentedBaseZ (n : Nat) {A D : B} (a : A ⟶ D) : (Mix.join (into S T n a) (inner S T n a)).t = (Evaluation.fibreSquare S Z n a).hom :=
  (identityWhisker ((into S T n a).g' ⋙ (source S T n a).b') (inner S T n a).f'
    (whiskerLeft (into S T n a).g' (inner S T n a).t)).trans (whiskeredBaseZ S T n a)
namespace Mix
variable {X : Grid} {Y : Grid} {Z : Grid}
theorem pasteComponent {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃] {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃}
    {F' : D₁ ⥤ D₂} {G' : D₂ ⥤ D₃} {U : C₁ ⥤ D₁} {V : C₂ ⥤ D₂} {W : C₃ ⥤ D₃}
    (i : U ⋙ F' ≅ F ⋙ V) (j : V ⋙ G' ≅ G ⋙ W) (x : C₁) :
    G'.map (i.hom.app x) ≫ j.hom.app (F.obj x) = (SpanPayload.pasteIso i.symm j.symm).symm.hom.app x := by
  simp [SpanPayload.pasteIso]
theorem isoJoinLaw (F : Map X Y) (G : Map Y Z)
    (i : X.b ⋙ F.f ≅ F.g ⋙ Y.b) (j : Y.b ⋙ G.f ≅ G.g ⋙ Z.b)
    (i' : X.b' ⋙ F.f' ≅ F.g' ⋙ Y.b') (j' : Y.b' ⋙ G.f' ≅ G.g' ⋙ Z.b')
    (h : F.s = i.hom) (k : G.s = j.hom) (h' : F.t = i'.hom) (k' : G.t = j'.hom)
    (pa pd) (hf : Law F) (hg : Law G) :
    Law { join F G with
      s := (SpanPayload.pasteIso i.symm j.symm).symm.hom
      t := (SpanPayload.pasteIso i'.symm j'.symm).symm.hom
      pa := pa
      pd := pd } := by
  apply replaceLaw _ _ _ _ _ _ _ (joinLaw F G hf hg)
  · intro x; change G.f.map (F.s.app x) ≫ G.s.app (F.g.obj x) = _
    rw [h,k]; exact pasteComponent i j x
  · intro x; change G.f'.map (F.t.app x) ≫ G.t.app (F.g'.obj x) = _
    rw [h',k']; exact pasteComponent i' j' x
end Mix
noncomputable def full (n : Nat) {A D : B} (a : A ⟶ D) : Mix.Map (native S T n a) (values (ChainPayload.layerMap T S (n+1)) a) where
  f := FibreValue.eval S Y n A
  g := FibreValue.eval S Y n D
  f' := FibreValue.eval S Z n A
  g' := FibreValue.eval S Z n D
  s := (FibreValue.evalSquare S Y n a).hom
  t := (FibreValue.evalSquare S Z n a).hom
  pa := EvalPayload.evalSquare T S n A
  pd := EvalPayload.evalSquare T S n D
theorem fullLaw (n : Nat) {A D : B} (a : A ⟶ D) : Mix.Law (full S T n a) :=
  Mix.isoJoinLaw (Mix.join (into S T n a) (inner S T n a)) (decode (ChainPayload.layerMap T S (n+1)) a)
    (Evaluation.fibreSquare S Y n a) (FibreValue.valueSquare (Evaluation.G S Y n) a)
    (Evaluation.fibreSquare S Z n a) (FibreValue.valueSquare (Evaluation.G S Z n) a)
    (presentedBaseY S T n a) rfl (presentedBaseZ S T n a) rfl (EvalPayload.evalSquare T S n A) (EvalPayload.evalSquare T S n D)
    (Mix.joinLaw _ _ (intoLaw S T n a) (innerLaw S T n a)) (decodeLaw _ a)
/-- Both routes are equal after inserting the indicated payload endpoint corrections.
The four functors, both base squares, and both payload equalities are fixed by full. -/
theorem fullDiagram (n : Nat) {A D : B} (a : A ⟶ D) : Mix.Diagram (full S T n a) :=
  Mix.equation _ (fullLaw S T n a)
end ContextualComposition.GrothendieckStep.FinalCube
