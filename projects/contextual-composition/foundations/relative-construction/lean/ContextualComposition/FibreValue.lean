module
public import ContextualComposition.NativeCleavage
/-! Decode the strict Grothendieck fibre to the actual presheaf value, and
verify the two constraint diagrams for the chosen strict-fibre evaluation.
These assertions do not identify the native cleavage with a strict splitting. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.FibreValue
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage
universe b w u v
variable {B : Type b} [Category.{w} B] (G : Bᵒᵖ ⥤ Cat.{v,u})
abbrev proj := gradeProjection (Y := G) (e := 𝟭 B)
def incl (A : B) : G.obj (op A) ⥤ Total G (𝟭 B) := (Grothendieck.ι (diagram G (𝟭 B)) (op A)).rightOp

def embed (A : B) : G.obj (op A) ⥤ (proj G).Fiber A where
  obj x := ⟨(incl G A).obj x,rfl⟩
  map f := ⟨(incl G A).map f,IsHomLift.map (proj G) ((incl G A).map f)⟩
  map_id x := Subtype.ext ((incl G A).map_id x)
  map_comp f g := Subtype.ext ((incl G A).map_comp f g)

set_option backward.isDefEq.respectTransparency false in
theorem embed_payload {A : B} {x y : G.obj (op A)} (f : x ⟶ y) :
    HEq (payloadMap ((embed G A).map f).val) f := by
  change HEq ((eqToHom _ ≫ f.op).unop) f
  rw [unop_comp]
  have aux {a c d : G.obj (op A)} (k : a ⟶ c) (h : op d = op c) : HEq (k ≫ (eqToHom h).unop) k := by
    cases unop_injective h; simp
  exact aux _ _

theorem obj_surj (A : B) : Function.Surjective (embed G A).obj := by
  rintro ⟨z,h⟩
  subst A; exact ⟨payload _ _ z,rfl⟩

theorem recoverGrade {A : B} {x y : G.obj (op A)} (f : (embed G A).obj x ⟶ (embed G A).obj y) :
    gradeMap f.val = 𝟙 A :=
  (@IsHomLift.eq_of_isHomLift _ _ _ _ (proj G) ((embed G A).obj x).val ((embed G A).obj y).val (𝟙 A) f.val f.property).symm

set_option backward.isDefEq.respectTransparency false in
def decodeHom {A : B} {x y : G.obj (op A)} (f : (embed G A).obj x ⟶ (embed G A).obj y) : x ⟶ y :=
  payloadMap f.val ≫ eqToHom (by change (G.map (gradeMap f.val).op).toFunctor.obj y = y; rw [recoverGrade G f]; exact Functor.congr_obj (congrArg Cat.Hom.toFunctor (G.map_id (op A))) y)

private theorem strip {C : Type*} [Category* C] {a b c : C} (f : a ⟶ b) (h : b = c) : HEq (f ≫ eqToHom h) f := by subst c; simp

theorem decode_heq {A : B} {x y : G.obj (op A)} (f : (embed G A).obj x ⟶ (embed G A).obj y) :
    HEq (decodeHom G f) (payloadMap f.val) := strip _ _

theorem decode_embed {A : B} {x y : G.obj (op A)} (f : x ⟶ y) : decodeHom G ((embed G A).map f) = f :=
  eq_of_heq ((decode_heq G _).trans (embed_payload G f))

theorem embed_decode {A : B} {x y : G.obj (op A)} (f : (embed G A).obj x ⟶ (embed G A).obj y) :
    (embed G A).map (decodeHom G f) = f :=
  Subtype.ext ((homEquiv _ _).injective (Sigma.ext (recoverGrade G f).symm ((embed_payload G _).trans (decode_heq G f))))

instance embedFull (A : B) : (embed G A).Full where
  map_surjective f := ⟨decodeHom G f,embed_decode G f⟩
instance embedFaithful (A : B) : (embed G A).Faithful where
  map_injective {_x _y} f g h := (decode_embed G f).symm.trans ((congrArg (decodeHom G) h).trans (decode_embed G g))
instance embedEssSurj (A : B) : (embed G A).EssSurj where
  mem_essImage z := by obtain ⟨x,h⟩ := obj_surj G A z; exact ⟨x,⟨eqToIso h⟩⟩
instance embedEquivalence (A : B) : (embed G A).IsEquivalence where

def transport {A D : B} (h : A = D) (x : G.obj (op A)) : G.obj (op D) := h ▸ x

def valObj {A : B} (x : (proj G).Fiber A) : G.obj (op A) := transport G x.property (payload _ _ x.val)

theorem represent {A : B} (x : (proj G).Fiber A) : (embed G A).obj (valObj G x) = x := by
  obtain ⟨z,h⟩ := x; subst A; rfl

def value (A : B) : (proj G).Fiber A ⥤ G.obj (op A) where
  obj := valObj G
  map {x y} f := decodeHom G (eqToHom (represent G x) ≫ f ≫ eqToHom (represent G y).symm)
  map_id x := by apply (embed G A).map_injective; rw [embed_decode,Functor.map_id]; simp
  map_comp {x y z} f g := by
    apply (embed G A).map_injective
    rw [Functor.map_comp,embed_decode,embed_decode,embed_decode]; simp

theorem embed_value (A : B) : embed G A ⋙ value G A = 𝟭 _ := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    change decodeHom G (𝟙 _ ≫ (embed G A).map f ≫ 𝟙 _) = 𝟙 _ ≫ f ≫ 𝟙 _
    simp only [Category.id_comp,Category.comp_id,decode_embed]

theorem value_embed (A : B) : value G A ⋙ embed G A = 𝟭 _ :=
  Functor.ext (represent G) (fun _ _ _ => embed_decode G _)

def valueEquiv (A : B) : (proj G).Fiber A ≌ G.obj (op A) :=
  CategoryTheory.Equivalence.mk (value G A) (embed G A) (eqToIso (value_embed G A).symm) (eqToIso (embed_value G A))

def choice : Cleavage (proj G) := extendChoice G (𝟭 B) (𝟭 B) baseChoice

def arrow {A D : B} (a : A ⟶ D) (y : G.obj (op D)) :
    ((embed G A).obj ((G.map a.op).toFunctor.obj y)).val ⟶ ((embed G D).obj y).val :=
  pullLift G (𝟭 B) ((embed G D).obj y).val a

def cone {A D : B} (a : A ⟶ D) : Change.Cone a (embed G D) where
  act := (G.map a.op).toFunctor ⋙ embed G A
  lift := arrow G a
  over _ := by change a = 𝟙 A ≫ a ≫ 𝟙 D; simp
  cart y := cartesianLift G (𝟭 B) ((embed G D).obj y).val a
  natural {x y} f := by
    apply Quiver.Hom.unop_inj
    exact ((Grothendieck.ιNatTrans (F := diagram G (𝟭 B)) a.op).naturality f.op).symm

noncomputable def square {A D : B} (a : A ⟶ D) :
    (G.map a.op).toFunctor ⋙ embed G A ≅ embed G D ⋙ Reindex.functor (choice G) a :=
  Change.iso (cone G a) (Change.before _ (Route.ofChoice _ a))

noncomputable def valueSquare {A D : B} (a : A ⟶ D) :
    Reindex.functor (choice G) a ⋙ value G A ≅ value G D ⋙ (G.map a.op).toFunctor :=
  calc
    _ ≅ value G D ⋙ ((embed G D ⋙ Reindex.functor (choice G) a) ⋙ value G A) :=
      eqToIso (by change _ = (value G D ⋙ embed G D) ⋙ (Reindex.functor (choice G) a ⋙ value G A); rw [value_embed]; rfl)
    _ ≅ value G D ⋙ (((G.map a.op).toFunctor ⋙ embed G A) ⋙ value G A) :=
      isoWhiskerLeft _ (isoWhiskerRight (square G a).symm _)
    _ ≅ _ := eqToIso (by change value G D ⋙ (G.map a.op).toFunctor ⋙ (embed G A ⋙ value G A) = _; rw [embed_value]; rfl)

open SpanPayload.Power SpanApex
variable {P : Endpoints.{b,w,u,v} B} (S : P.Split) (Y : Bᵒᵖ ⥤ Cat.{v,u})
def eval (n : Nat) (A : B) : Total Y (nativeEndpoint S n A) ⥤ (Evaluation.G S Y n).obj (op A) :=
  Evaluation.onFibre S Y n A ⋙ value _ A

instance evalEquivalence (n : Nat) (A : B) : (eval S Y n A).IsEquivalence :=
  @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ (Evaluation.onFibreEquivalence S Y n A) (valueEquiv (Evaluation.G S Y n) A).isEquivalence_functor

noncomputable def evalSquare (n : Nat) {A D : B} (a : A ⟶ D) :
    nativeReindex Y S n a ⋙ eval S Y n A ≅ eval S Y n D ⋙ ((Evaluation.G S Y n).map a.op).toFunctor :=
  (SpanPayload.pasteIso (Evaluation.fibreSquare S Y n a).symm (valueSquare _ a).symm).symm

namespace Laws
variable {K L : Type*} [Category* K] [Category* L] {p : K ⥤ B} (q : L ⥤ B)
    (F : K ⥤ L) (H : F ⋙ q = p)
    (pres : ∀ {x y : K} (f : x ⟶ y), Cartesian p f → Cartesian q (F.map f))
    {A D E : B} {a : A ⟶ D} {b : D ⟶ E}


theorem fac (R : Route (F ⋙ q) a) (Q : Route q a)
    (j : ∀ {x y : K} (f : x ⟶ y), Cartesian (F ⋙ q) f → Cartesian q (F.map f))
    (x : (F ⋙ q).Fiber D) :
    ((Change.square F rfl R Q j).hom.app x).val ≫ Q.lift ((SpanPayload.fibreFunctor F q rfl D).obj x) = F.map (R.lift x) :=
  Change.fac (Change.after F rfl R j) (Change.before _ Q) x

set_option backward.isDefEq.respectTransparency false in
theorem changeRoutes (R R' : Route p a) (Q Q' : Route q a) :
    whiskerRight (Route.compare R R') (SpanPayload.fibreFunctor F q H A) ≫ (Change.square F H R' Q' pres).hom =
      (Change.square F H R Q pres).hom ≫ whiskerLeft (SpanPayload.fibreFunctor F q H D) (Route.compare Q Q') := by
  subst p
  ext x : 2
  apply Q'.cancel
  change (F.map (Route.compareApp R R' x).val ≫ ((Change.square F rfl R' Q' pres).hom.app x).val) ≫ _ =
    (((Change.square F rfl R Q pres).hom.app x).val ≫ (Route.compareApp Q Q' _).val) ≫ _
  rw [Category.assoc,fac,← F.map_comp,Route.compare_fac,Category.assoc,Route.compare_fac,fac]

set_option backward.isDefEq.respectTransparency false in
theorem identity (A : B) : (Change.square F H (Route.id A) (Route.id A) pres).hom =
    𝟙 (SpanPayload.fibreFunctor F q H A) := by
  subst p
  ext x : 2
  apply (Route.id (p := q) A).cancel
  change ((Change.square F rfl (Route.id A) (Route.id A) pres).hom.app x).val ≫ (Route.id A).lift _ =
    𝟙 _ ≫ 𝟙 _
  refine (fac q F (Route.id A) (Route.id A) pres x).trans ?_
  exact (F.map_id _).trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
theorem horizontal (R : Route p a) (T : Route p b) (Q : Route q a) (U : Route q b) :
    (Change.square F H (Route.comp R T) (Route.comp Q U) pres).hom =
      whiskerLeft T.act (Change.square F H R Q pres).hom ≫ whiskerRight (Change.square F H T U pres).hom Q.act := by
  subst p
  ext x : 2
  apply (Route.comp Q U).cancel
  change ((Change.square F rfl (Route.comp R T) (Route.comp Q U) pres).hom.app x).val ≫ (Route.comp Q U).lift _ =
    (((Change.square F rfl R Q pres).hom.app (T.act.obj x)).val ≫
      (Q.act.map ((Change.square F rfl T U pres).hom.app x)).val) ≫ Q.lift _ ≫ U.lift _
  rw [fac,Category.assoc,← Category.assoc (Q.act.map _).val,Q.natural,Category.assoc,fac,
    ← Category.assoc]
  exact (F.map_comp _ _).trans (congrArg (· ≫ F.map (T.lift x)) (fac q F R Q pres (T.act.obj x)).symm)

set_option backward.isDefEq.respectTransparency false in
theorem unitDiagram (C : Cleavage p) (J : Cleavage q) (A : B) :
    (Change.square F H (Route.ofChoice C (𝟙 A)) (Route.ofChoice J (𝟙 A)) pres).hom ≫
      whiskerLeft (SpanPayload.fibreFunctor F q H A) (Route.unitIso J A).hom =
    whiskerRight (Route.unitIso C A).hom (SpanPayload.fibreFunctor F q H A) := by
  have h := changeRoutes q F H pres (Route.ofChoice C (𝟙 A)) (Route.id A) (Route.ofChoice J (𝟙 A)) (Route.id A)
  rw [identity] at h
  exact h.symm.trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
theorem compDiagram (C : Cleavage p) (J : Cleavage q) (a : A ⟶ D) (b : D ⟶ E) :
    (Change.square F H (Route.ofChoice C (a ≫ b)) (Route.ofChoice J (a ≫ b)) pres).hom ≫
      whiskerLeft (SpanPayload.fibreFunctor F q H E) (Route.compIso J a b).hom =
    whiskerRight (Route.compIso C a b).hom (SpanPayload.fibreFunctor F q H A) ≫
      (whiskerLeft (Reindex.functor C b) (Change.square F H (Route.ofChoice C a) (Route.ofChoice J a) pres).hom ≫
       whiskerRight (Change.square F H (Route.ofChoice C b) (Route.ofChoice J b) pres).hom (Reindex.functor J a)) := by
  have h := changeRoutes q F H pres (Route.ofChoice C (a ≫ b)) (Route.comp (Route.ofChoice C a) (Route.ofChoice C b))
    (Route.ofChoice J (a ≫ b)) (Route.comp (Route.ofChoice J a) (Route.ofChoice J b))
  rw [horizontal] at h
  exact h.symm
end Laws

theorem fibreUnit (n : Nat) (A : B) :
    (Evaluation.fibreSquare S Y n (𝟙 A)).hom ≫ whiskerLeft (Evaluation.onFibre S Y n A)
      (Route.unitIso (Evaluation.iterateChoice S Y n) A).hom =
    whiskerRight (nativeId Y S n A).hom (Evaluation.onFibre S Y n A) := by
  ext x : 2
  exact NatTrans.congr_app (Laws.unitDiagram _ _ (Evaluation.native_over S Y n) (Evaluation.native_pres S Y n)
    (payloadChoice Y S n) (Evaluation.iterateChoice S Y n) A) ((FibreTotal.into Y _ _ A).obj x)

theorem fibreComp (n : Nat) {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    (Evaluation.fibreSquare S Y n (a ≫ b)).hom ≫ whiskerLeft (Evaluation.onFibre S Y n E)
      (Route.compIso (Evaluation.iterateChoice S Y n) a b).hom =
    whiskerRight (nativeComp Y S n a b).hom (Evaluation.onFibre S Y n A) ≫
      (whiskerLeft (nativeReindex Y S n b) (Evaluation.fibreSquare S Y n a).hom ≫
        whiskerRight (Evaluation.fibreSquare S Y n b).hom (Reindex.functor (Evaluation.iterateChoice S Y n) a)) := by
  ext x : 2
  exact NatTrans.congr_app (Laws.compDiagram _ _ (Evaluation.native_over S Y n) (Evaluation.native_pres S Y n)
    (payloadChoice Y S n) (Evaluation.iterateChoice S Y n) a b) ((FibreTotal.into Y _ _ E).obj x)

end ContextualComposition.GrothendieckStep.FibreValue
