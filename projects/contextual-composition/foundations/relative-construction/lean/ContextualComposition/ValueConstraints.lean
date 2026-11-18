module
public import ContextualComposition.FibreValue
/-! Positive strict-fibre evaluation: compute the chosen presheaf-side constraints, not arbitrary cleavage comparisons. -/
@[expose] public section
open CategoryTheory CategoryTheory.Functor Opposite
namespace ContextualComposition.GrothendieckStep.FibreValue
open NativeCleavage
universe b w u v
variable {B : Type b} [Category.{w} B] (G : Bᵒᵖ ⥤ Cat.{v,u})
theorem squareObj {A D : B} (a : A ⟶ D) (x : G.obj (op D)) :
  ((G.map a.op).toFunctor ⋙ embed G A).obj x = (embed G D ⋙ Reindex.functor (choice G) a).obj x := by
  change _ = Reindex.object (choice G) a ((embed G D).obj x)
  let z := (embed G D).obj x
  have h : a ≫ eqToHom z.property.symm = a := Category.comp_id a
  change ((G.map a.op).toFunctor ⋙ embed G A).obj x = (⟨pullObj G (𝟭 B) z.val (a ≫ eqToHom z.property.symm),rfl⟩ : (proj G).Fiber A)
  exact congrArg (fun t : A ⟶ D => (⟨pullObj G (𝟭 B) z.val t,rfl⟩ : (proj G).Fiber A)) h.symm
set_option backward.isDefEq.respectTransparency false in
theorem squareApp {A D : B} (a : A ⟶ D) (x : G.obj (op D)) :
  (square G a).hom.app x = eqToHom (squareObj G a x) := by
  apply Change.cancel (Change.before (embed G D) (Route.ofChoice (choice G) a))
  rw [show ((square G a).hom.app x).val ≫ _ = _ from Change.fac (cone G a) (Change.before _ (Route.ofChoice _ a)) x]
  change arrow G a x = (eqToHom (squareObj G a x)).val ≫ Reindex.lift (choice G) a ((embed G D).obj x)
  let z := (embed G D).obj x
  let W (t : A ⟶ D) : (proj G).Fiber A := ⟨pullObj G (𝟭 B) z.val t,rfl⟩
  have aux (t : A ⟶ D) (h : a = t) : pullLift G (𝟭 B) z.val a =
      (eqToHom (congrArg W h)).val ≫ pullLift G (𝟭 B) z.val t := by
    subst t; exact (Category.id_comp _).symm
  exact aux _ (Category.comp_id a).symm
theorem squareInv {A D : B} (a : A ⟶ D) (x : G.obj (op D)) :
    (square G a).inv.app x = eqToHom (squareObj G a x).symm := by
  apply (cancel_epi ((square G a).hom.app x)).1
  rw [Iso.hom_inv_id_app,squareApp]; simp
theorem valueObj {A D : B} (a : A ⟶ D) (x : (proj G).Fiber D) :
    (Reindex.functor (choice G) a ⋙ value G A).obj x = (value G D ⋙ (G.map a.op).toFunctor).obj x := by
  obtain ⟨z,rfl⟩ := obj_surj G D x
  exact congrArg (value G A).obj (squareObj G a z).symm
theorem valueApp {A D : B} (a : A ⟶ D) (x : (proj G).Fiber D) :
    (valueSquare G a).hom.app x = eqToHom (valueObj G a x) := by
  simp only [valueSquare,Trans.trans,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,
    isoWhiskerLeft_hom,isoWhiskerRight_hom,whiskerLeft_app,whiskerRight_app,Iso.symm_hom,
    squareInv,eqToHom_map,eqToHom_trans]
def Pure {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) : Prop := ∃ h : X = Y, f = eqToHom h
theorem pureId {C : Type*} [Category* C] (X : C) : Pure (𝟙 X) := ⟨rfl,rfl⟩
theorem pureComp {C : Type*} [Category* C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (h : Pure f) (k : Pure g) : Pure (f ≫ g) := by
  obtain ⟨rfl,rfl⟩ := h; obtain ⟨rfl,rfl⟩ := k; exact ⟨rfl,Category.id_comp _⟩
theorem pureCancel {C : Type*} [Category* C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (h : Pure (f ≫ g)) (k : Pure g) : Pure f := by
  obtain ⟨rfl,rfl⟩ := k; simpa using h
theorem pureMap {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y : C} {f : X ⟶ Y} (h : Pure f) : Pure (F.map f) := by
  obtain ⟨rfl,rfl⟩ := h; simpa using pureId (F.obj X)
variable {G}
theorem payloadPureComp {x y z : Total G (𝟭 B)} {f : x ⟶ y} {g : y ⟶ z} (hf : Pure (payloadMap f)) (hg : Pure (payloadMap g)) : Pure (payloadMap (f ≫ g)) := by
  rw [payload_comp]; exact pureComp hf (pureComp (pureMap _ hg) ⟨_,rfl⟩)
theorem payloadPureCancel {x y z : Total G (𝟭 B)} {f : x ⟶ y} {g : y ⟶ z} (hf : Pure (payloadMap (f ≫ g))) (hg : Pure (payloadMap g)) : Pure (payloadMap f) := by
  rw [payload_comp] at hf; exact pureCancel hf (pureComp (pureMap _ hg) ⟨_,rfl⟩)
variable (G)
theorem chosenPure {A D : B} (a : A ⟶ D) (x : (proj G).Fiber D) : Pure (payloadMap (Reindex.lift (choice G) a x)) := pureId _
theorem identityPure (x : Total G (𝟭 B)) : Pure (payloadMap (𝟙 x)) := by
  unfold payloadMap; change Pure (Grothendieck.Hom.fiber (𝟙 x.unop)).unop; rw [Grothendieck.id_fiber]
  exact ⟨_,eqToHom_unop _⟩
theorem unitPure (A : B) (x : (proj G).Fiber A) :
    Pure (payloadMap (((Route.unitIso (choice G) A).hom.app x).val)) := by
  have h := Route.compare_fac (Route.ofChoice (choice G) (𝟙 A)) (Route.id A) x
  apply payloadPureCancel (g := (Route.id (p := proj G) A).lift x)
  · exact (congrArg (fun f => Pure (payloadMap f)) h).mpr (chosenPure _ _ _)
  · exact identityPure G _
theorem compPure {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (x : (proj G).Fiber E) :
    Pure (payloadMap (((Route.compIso (choice G) a b).hom.app x).val)) := by
  let Q := Route.comp (Route.ofChoice (choice G) a) (Route.ofChoice (choice G) b)
  have h := Route.compare_fac (Route.ofChoice (choice G) (a ≫ b)) Q x
  apply payloadPureCancel (g := Q.lift x)
  · exact (congrArg (fun f => Pure (payloadMap f)) h).mpr (chosenPure _ _ _)
  · exact payloadPureComp (chosenPure _ _ _) (chosenPure _ _ _)
theorem valuePure {A : B} {x y : (proj G).Fiber A} (f : x ⟶ y) (h : Pure (payloadMap f.val)) :
    Pure ((value G A).map f) := by
  obtain ⟨x,rfl⟩ := obj_surj G A x
  obtain ⟨y,rfl⟩ := obj_surj G A y
  change Pure (decodeHom G (𝟙 _ ≫ f ≫ 𝟙 _))
  simp only [Category.id_comp,Category.comp_id]
  exact pureComp h ⟨_,rfl⟩
theorem strictUnit (A : B) : (G.map (𝟙 A).op).toFunctor = 𝟭 _ := congrArg Cat.Hom.toFunctor (G.map_id _)
theorem strictComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) : (G.map (a ≫ b).op).toFunctor =
    (G.map b.op).toFunctor ⋙ (G.map a.op).toFunctor := congrArg Cat.Hom.toFunctor (G.map_comp _ _)
theorem pureEq {C : Type*} [Category* C] {X Y : C} {f g : X ⟶ Y} (h : Pure f) (k : Pure g) : f = g := by
  obtain ⟨e,rfl⟩ := h; obtain ⟨_,rfl⟩ := k; rfl
theorem valueUnit (A : B) : (valueSquare G (𝟙 A)).hom ≫ whiskerLeft (value G A) (eqToHom (strictUnit G A)) =
    whiskerRight (Route.unitIso (choice G) A).hom (value G A) := by
  ext x : 2
  apply pureEq
  · apply pureComp; exact ⟨_,valueApp G _ _⟩; exact ⟨_,eqToHom_app _ _⟩
  · exact valuePure G _ (unitPure G A x)
theorem valueComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    (valueSquare G (a ≫ b)).hom ≫ whiskerLeft (value G E) (eqToHom (strictComp G a b)) =
    whiskerRight (Route.compIso (choice G) a b).hom (value G A) ≫
      (whiskerLeft (Reindex.functor (choice G) b) (valueSquare G a).hom ≫
        whiskerRight (valueSquare G b).hom (G.map a.op).toFunctor) := by
  ext x : 2
  apply pureEq
  · apply pureComp; exact ⟨_,valueApp G _ _⟩; exact ⟨_,eqToHom_app _ _⟩
  · apply pureComp
    · exact valuePure G _ (compPure G a b x)
    · exact pureComp ⟨_,valueApp G _ _⟩ (pureMap _ ⟨_,valueApp G _ _⟩)
open SpanPayload.Power SpanApex
variable {P : Endpoints.{b,w,u,v} B} (S : P.Split) (Y : Bᵒᵖ ⥤ Cat.{v,u})
theorem evalApp (n : Nat) {A D : B} (a : A ⟶ D) (x : Total Y (nativeEndpoint S n D)) :
  (evalSquare S Y n a).hom.app x =
    (value _ A).map ((Evaluation.fibreSquare S Y n a).hom.app x) ≫
      (valueSquare _ a).hom.app ((Evaluation.onFibre S Y n D).obj x) := by
  simp [evalSquare,SpanPayload.pasteIso]; rfl
end ContextualComposition.GrothendieckStep.FibreValue
