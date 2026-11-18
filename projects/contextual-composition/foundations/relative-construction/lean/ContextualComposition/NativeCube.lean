module
public import ContextualComposition.DecoderCube
/-! The mixed cube for the native-to-iterate comparison on strict fibres. Both paths are tested at the same target cartesian lift. The presented source face is also constructed; the final decoder paste is separate. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeCube
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage TelescopeSquares
variable {B K L M : Type*} [Category* B] [Category* K] [Category* L] [Category* M]
variable {p : K ⥤ B} {q : L ⥤ B} {r : M ⥤ B} {A D : B} {a : A ⟶ D}
theorem ofEq {C : Type*} [Category* C] {x y : C} {f g : x ⟶ y} (h : f = g) : Aligned f g := h ▸ Aligned.refl f
theorem functorAlign {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D} (h : F = G) {x y : C} (f : x ⟶ y) :
    Aligned (F.map f) (G.map f) := by subst G; exact Aligned.refl _
theorem fibreMapAlign (F : K ⥤ L) (h : F ⋙ q = p) {x y : p.Fiber A} (f : x ⟶ y) :
    Aligned (((SpanPayload.fibreFunctor F q h A).map f).val) (F.map f.val) := by subst p; exact Aligned.refl _
theorem changeFac (F : K ⥤ L) (h : F ⋙ q = p) (R : Route p a) (Q : Route q a)
    (pres : ∀ {x y : K} (f : x ⟶ y), Cartesian p f → Cartesian q (F.map f)) (x : p.Fiber D) :
    Aligned (((Change.square F h R Q pres).hom.app x).val ≫ Q.lift ((SpanPayload.fibreFunctor F q h D).obj x))
      (F.map (R.lift x)) := by
  subst p; exact ofEq (FibreValue.Laws.fac q F R Q pres x)
theorem pasteFac (F : K ⥤ L) (G : L ⥤ M) (h : G ⋙ r = q)
    (R : Route p a) (Q : Route q a) (U : Route r a) (x : p.Fiber D)
    {s : q.Fiber A} {t : q.Fiber D} {z : r.Fiber D}
    (l : s ⟶ Q.act.obj t) (m : (SpanPayload.fibreFunctor G r h A).obj (Q.act.obj t) ⟶ U.act.obj z)
    (hl : Aligned (l.val ≫ Q.lift t) (F.map (R.lift x)))
    (hm : Aligned (m.val ≫ U.lift z) (G.map (Q.lift t))) :
    Aligned ((((SpanPayload.fibreFunctor G r h A).map l ≫ m).val) ≫ U.lift z)
      ((F ⋙ G).map (R.lift x)) := by
  change Aligned ((((SpanPayload.fibreFunctor G r h A).map l).val ≫ m.val) ≫ _) _
  apply (ofEq (Category.assoc ..)).trans
  apply ((fibreMapAlign G h l).comp hm).trans
  apply (ofEq (G.map_comp _ _).symm).trans
  exact hl.map G
theorem eqVal {p : M ⥤ B} {A : B} {x y : p.Fiber A} (h : x = y) :
    (eqToHom h).val = eqToHom (congrArg Subtype.val h) := by subst y; rfl
theorem cancelAligned (R : Route p a) {s s' : p.Fiber A} {t t' : p.Fiber D}
    (l : s ⟶ R.act.obj t) (m : s' ⟶ R.act.obj t') (hs : s = s') (ht : t = t')
    (h : Aligned (l.val ≫ R.lift t) (m.val ≫ R.lift t')) :
    l ≫ R.act.map (eqToHom ht) = eqToHom hs ≫ m := by
  apply DecoderCube.CommonLift.compare R l m _ _ _ _ rfl rfl
  rw [eqVal,eqVal]; exact h.comm
structure Face (R : Route p a) (Q : Route q a) (F : K ⥤ L) (h : F ⋙ q = p) where
  sq : R.act ⋙ SpanPayload.fibreFunctor F q h A ≅ SpanPayload.fibreFunctor F q h D ⋙ Q.act
  fac (x : p.Fiber D) : Aligned ((sq.hom.app x).val ≫ Q.lift ((SpanPayload.fibreFunctor F q h D).obj x)) (F.map (R.lift x))
namespace Face
variable {R : Route p a} {Q : Route q a} {U : Route r a} {F : K ⥤ L} {G : L ⥤ M} {h : F ⋙ q = p} {k : G ⋙ r = q}
def path (i : Face R Q F h) (j : Face Q U G k) (x : p.Fiber D) :=
  (SpanPayload.fibreFunctor G r k A).map (i.sq.hom.app x) ≫ j.sq.hom.app ((SpanPayload.fibreFunctor F q h D).obj x)
theorem pathFac (i : Face R Q F h) (j : Face Q U G k) (x : p.Fiber D) :
    Aligned ((path i j x).val ≫ U.lift ((SpanPayload.fibreFunctor G r k D).obj ((SpanPayload.fibreFunctor F q h D).obj x)))
      ((F ⋙ G).map (R.lift x)) :=
  pasteFac F G k R Q U x _ _ (i.fac x) (j.fac _)
variable {L' : Type*} [Category* L'] {q' : L' ⥤ B} {Q' : Route q' a} {F' : K ⥤ L'} {G' : L' ⥤ M}
    {h' : F' ⋙ q' = p} {k' : G' ⋙ r = q'}
theorem cube (i : Face R Q F h) (j : Face Q U G k) (i' : Face R Q' F' h') (j' : Face Q' U G' k')
    (e : F ⋙ G = F' ⋙ G') (x : p.Fiber D)
    (hs : (SpanPayload.fibreFunctor G r k A).obj ((SpanPayload.fibreFunctor F q h A).obj (R.act.obj x)) =
      (SpanPayload.fibreFunctor G' r k' A).obj ((SpanPayload.fibreFunctor F' q' h' A).obj (R.act.obj x)))
    (ht : (SpanPayload.fibreFunctor G r k D).obj ((SpanPayload.fibreFunctor F q h D).obj x) =
      (SpanPayload.fibreFunctor G' r k' D).obj ((SpanPayload.fibreFunctor F' q' h' D).obj x)) :
    path i j x ≫ U.act.map (eqToHom ht) = eqToHom hs ≫ path i' j' x :=
  cancelAligned U _ _ hs ht ((pathFac i j x).trans ((functorAlign e (R.lift x)).trans (pathFac i' j' x).symm))
def Law (i : Face R Q F h) (j : Face Q U G k) (i' : Face R Q' F' h') (j' : Face Q' U G' k')
    (ea : SpanPayload.fibreFunctor F q h A ⋙ SpanPayload.fibreFunctor G r k A =
      SpanPayload.fibreFunctor F' q' h' A ⋙ SpanPayload.fibreFunctor G' r k' A)
    (ed : SpanPayload.fibreFunctor F q h D ⋙ SpanPayload.fibreFunctor G r k D =
      SpanPayload.fibreFunctor F' q' h' D ⋙ SpanPayload.fibreFunctor G' r k' D) : Prop :=
  ∀ x, path i j x ≫ U.act.map (eqToHom (Functor.congr_obj ed x)) =
    eqToHom (Functor.congr_obj ea (R.act.obj x)) ≫ path i' j' x
theorem law (i : Face R Q F h) (j : Face Q U G k) (i' : Face R Q' F' h') (j' : Face Q' U G' k')
    (e : F ⋙ G = F' ⋙ G') (ea ed) : Law i j i' j' ea ed :=
  fun x => cube i j i' j' e x _ _
end Face
universe b w u v
section Actual
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (S : P.Split) (Y : Bᵒᵖ ⥤ Cat.{v,u})
open SpanApex SpanPayload.Power
noncomputable def evaluation (n : Nat) {A D : B} (a : A ⟶ D) :
    Face (Route.ofChoice (payloadChoice Y S n) a) (Route.ofChoice (Evaluation.iterateChoice S Y n) a)
      (Evaluation.nativeFunctor S Y n) (Evaluation.native_over S Y n) :=
  ⟨Evaluation.chosenSquare S Y n a,changeFac _ _ _ _ (Evaluation.native_pres S Y n)⟩
variable {Y} {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
noncomputable def payload {K : Type*} [Category* K] (e p : K ⥤ B) (C : Cleavage p) {A D : B} (a : A ⟶ D) :
    Face (Route.ofChoice (extendChoice Y e p C) a) (Route.ofChoice (extendChoice Z e p C) a)
      (ChainPayload.fibreMap T e) (PayloadLift.over T e p) :=
  ⟨PayloadLift.square T e p C a,fun x => ofEq (PayloadLift.square_fac T e p C a x)⟩
noncomputable abbrev sourceFace (n : Nat) {A D : B} (a : A ⟶ D) :=
  payload T (positivePowers P S n).dest (positivePowers P S n).source (powerChoice S n) a
noncomputable abbrev targetFace (n : Nat) {A D : B} (a : A ⟶ D) :=
  payload (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) baseChoice a
theorem strictCube (n : Nat) {A D : B} (a : A ⟶ D) :
    Face.Law (sourceFace S T n a) (evaluation S Z n a) (evaluation S Y n a) (targetFace S T n a)
      (EvalPayload.strictSquare T S n A) (EvalPayload.strictSquare T S n D) :=
  Face.law _ _ _ _ (EvalPayload.nativeSquare T S n) _ _
theorem outSquare {K : Type*} [Category* K] (e p : K ⥤ B) (A : B) :
    FibreTotal.out Y e p A ⋙ ChainPayload.fibreMap T (FibreTotal.endpoint e p A) =
      PayloadLift.action T e p A ⋙ FibreTotal.out Z e p A := by
  exact congrArg (fun f => FibreTotal.out Y e p A ⋙ f ⋙ FibreTotal.out Z e p A) (EvalPayload.intoSquare T e p A)
def present {X V V' W W' Z : Type*} [Category* X] [Category* V] [Category* V'] [Category* W] [Category* W'] [Category* Z]
    (I : X ⥤ V) (O : W' ⥤ Z) (U : V ⥤ W) (R : V' ⥤ W') (L : W ⥤ W') (H : V ⥤ V')
    (U' : W ⥤ Z) (R' : X ⥤ V') (s : U ⋙ L ≅ H ⋙ R)
    (h : U' = L ⋙ O) (k : I ⋙ H = R') : I ⋙ U ⋙ U' ≅ R' ⋙ R ⋙ O :=
  eqToIso (congrArg (fun f => I ⋙ U ⋙ f) h) ≪≫
    isoWhiskerLeft I (isoWhiskerRight s O) ≪≫ eqToIso (congrArg (fun f => f ⋙ R ⋙ O) k)
noncomputable def presentedSquare (n : Nat) {A D : B} (a : A ⟶ D) :
    nativeReindex Y S n a ⋙ ChainPayload.fibreMap T (nativeEndpoint S n A) ≅
      ChainPayload.fibreMap T (nativeEndpoint S n D) ⋙ nativeReindex Z S n a :=
  present (FibreTotal.into Y _ _ D) (FibreTotal.out Z _ _ A) (Reindex.functor (payloadChoice Y S n) a)
    (Reindex.functor (payloadChoice Z S n) a) (PayloadLift.action T _ _ A) (PayloadLift.action T _ _ D)
    (FibreTotal.out Y _ _ A ⋙ ChainPayload.fibreMap T _) (ChainPayload.fibreMap T _ ⋙ FibreTotal.into Z _ _ D)
    (PayloadLift.nativeSquare T S n a) (outSquare T _ _ A) (EvalPayload.intoSquare T _ _ D).symm
end Actual
end ContextualComposition.GrothendieckStep.NativeCube
