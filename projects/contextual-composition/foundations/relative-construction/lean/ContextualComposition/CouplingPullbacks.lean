module
public import Mathlib.CategoryTheory.Types.Basic

/-! The exact uniqueness boundary for all-couplings composition. The terminal effect is retained in the compatibility condition on binary couplings. -/

@[expose] public section
namespace ContextualComposition.CouplingPullbacks
open CategoryTheory Function

universe u
variable (F : Type u ⥤ Type u) {X Y Z W S : Type u}

def push (f : X → Y) (x : F.obj X) : F.obj Y := F.map (TypeCat.ofHom f) x

theorem push_push (f : X → Y) (g : Y → Z) (x : F.obj X) :
    push F g (push F f x) = push F (g ∘ f) x :=
  (congrArg (fun (h : F.obj X ⟶ F.obj Z) => h x) (F.map_comp (TypeCat.ofHom f) (TypeCat.ofHom g))).symm

theorem push_id (x : F.obj X) : push F id x = x :=
  congrArg (fun (h : F.obj X ⟶ F.obj X) => h x) (F.map_id X)

theorem push_bijective (e : X ≃ Y) : Bijective (push F e) := by
  have l (x : F.obj X) : push F e.symm (push F e x) = x := by
    rw [push_push, show (⇑e.symm ∘ ⇑e) = id by funext a; exact e.symm_apply_apply a, push_id]
  have r (y : F.obj Y) : push F e (push F e.symm y) = y := by
    rw [push_push, show (⇑e ∘ ⇑e.symm) = id by funext a; exact e.apply_symm_apply a, push_id]
  exact ⟨fun _ _ h => (l _).symm.trans ((congrArg _ h).trans (l _)),fun y => ⟨_,r y⟩⟩

abbrev PB (f : X → S) (g : Y → S) := {p : X × Y // f p.1 = g p.2}
def left {f : X → S} {g : Y → S} (p : PB f g) : X := p.val.1
def right {f : X → S} {g : Y → S} (p : PB f g) : Y := p.val.2

def comparison (f : X → S) (g : Y → S) (h : F.obj (PB f g)) : PB (push F f) (push F g) :=
  ⟨(push F left h, push F right h),by
    change push F f (push F left h) = push F g (push F right h)
    rw [push_push,push_push]
    exact congrArg (fun k => push F k h) (funext fun p => p.property)⟩

def WeakPullbacks := ∀ {X Y S : Type u} (f : X → S) (g : Y → S), Surjective (comparison F f g)
def PreservesPullbacks := ∀ {X Y S : Type u} (f : X → S) (g : Y → S), Bijective (comparison F f g)

theorem map_injective (weak : WeakPullbacks F) (f : X → Y) (hf : Injective f) : Injective (push F f) := by
  intro x y h
  obtain ⟨t,ht⟩ := weak f f ⟨(x,y),h⟩
  have l := congrArg (fun p : PB (push F f) (push F f) => p.val.1) ht
  have r := congrArg (fun p : PB (push F f) (push F f) => p.val.2) ht
  have legs : (left (f:=f) (g:=f)) = right := funext fun p => hf p.property
  change push F left t = x at l
  change push F right t = y at r
  exact l.symm.trans ((congrArg (fun k => push F k t) legs).trans r)

abbrev terminal (X : Type u) : X → PUnit.{u+1} := fun _ => ⟨⟩

def pairChart (X Y : Type u) : (X × Y) ≃ PB (terminal X) (terminal Y) where
  toFun p := ⟨p,rfl⟩
  invFun p := p.val
  left_inv _ := rfl
  right_inv _ := rfl

def pairComparison (X Y : Type u) (t : F.obj (X × Y)) :=
  comparison F (terminal X) (terminal Y) (push F (pairChart X Y) t)

theorem pair_left (t : F.obj (X × Y)) : (pairComparison F X Y t).val.1 = push F Prod.fst t :=
  push_push F (pairChart X Y) left t

theorem pair_right (t : F.obj (X × Y)) : (pairComparison F X Y t).val.2 = push F Prod.snd t :=
  push_push F (pairChart X Y) right t

def PairBijective := ∀ X Y : Type u, Bijective (pairComparison F X Y)
def UniqueCouplings := ∀ (X Y : Type u) (p : F.obj X) (q : F.obj Y),
  push F (terminal X) p = push F (terminal Y) q →
    ∃! t : F.obj (X × Y), push F Prod.fst t = p ∧ push F Prod.snd t = q

theorem pair_iff_unique : PairBijective F ↔ UniqueCouplings F := by
  have spec {X Y : Type u} (t : F.obj (X × Y)) (w : PB (push F (terminal X)) (push F (terminal Y))) :
      pairComparison F X Y t = w ↔ push F Prod.fst t = w.val.1 ∧ push F Prod.snd t = w.val.2 := by
    rw [← pair_left, ← pair_right]
    exact ⟨fun e => ⟨congrArg (fun p => p.val.1) e,congrArg (fun p => p.val.2) e⟩,
      fun h => Subtype.ext (Prod.ext h.1 h.2)⟩
  constructor
  · intro h X Y p q hp
    let w : PB (push F (terminal X)) (push F (terminal Y)) := ⟨(p,q),hp⟩
    obtain ⟨t,ht⟩ := (h X Y).surjective w
    exact ⟨t,(spec t w).mp ht,fun s hs => (h X Y).injective (((spec s w).mpr hs).trans ht.symm)⟩
  · intro h X Y
    have one (w : PB (push F (terminal X)) (push F (terminal Y))) : ∃! t, pairComparison F X Y t = w := by
      obtain ⟨t,ht,un⟩ := h X Y w.val.1 w.val.2 w.property
      exact ⟨t,(spec _ _).mpr ht,fun s hs => un s ((spec _ _).mp hs)⟩
    exact ⟨fun x y e => (one _).unique e rfl, fun w => (one w).exists⟩

theorem preserves_of_pair (weak : WeakPullbacks F) (binary : PairBijective F) : PreservesPullbacks F := by
  intro X Y S f g
  refine ⟨?_,weak f g⟩
  intro x y eq
  apply map_injective F weak (Subtype.val : PB f g → X × Y) Subtype.val_injective
  apply (binary X Y).injective
  apply Subtype.ext
  apply Prod.ext
  · rw [pair_left,pair_left,push_push,push_push]
    exact congrArg (fun p => p.val.1) eq
  · rw [pair_right,pair_right,push_push,push_push]
    exact congrArg (fun p => p.val.2) eq

abbrev side₁ (p : X × Y × Z) := (p.1,p.2.2)
abbrev side₂ (p : X × Z × W) := (p.1,p.2.1)

def quadChart (X Y Z W : Type u) :
    (X × Y × Z × W) ≃ PB (side₁ (X:=X) (Y:=Y) (Z:=Z)) (side₂ (W:=W)) where
  toFun p := ⟨((p.1,p.2.1,p.2.2.1),(p.1,p.2.2.1,p.2.2.2)),rfl⟩
  invFun p := (p.val.1.1,p.val.1.2.1,p.val.1.2.2,p.val.2.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟨x,y,z⟩,x',z',w⟩,h⟩
    change (x,z) = (x',z') at h
    cases h
    rfl

def quadComparison (X Y Z W : Type u) (t : F.obj (X × Y × Z × W)) :=
  comparison F side₁ side₂ (push F (quadChart X Y Z W) t)

def QuadBijective := ∀ X Y Z W : Type u, Bijective (quadComparison F X Y Z W)

theorem quad_surjective (weak : WeakPullbacks F) (X Y Z W : Type u) : Surjective (quadComparison F X Y Z W) :=
  (weak side₁ side₂).comp (push_bijective F (quadChart X Y Z W)).surjective

theorem quad_of_preserves (h : PreservesPullbacks F) : QuadBijective F :=
  fun X Y Z W => (h side₁ side₂).comp (push_bijective F (quadChart X Y Z W))

theorem pair_of_quad (weak : WeakPullbacks F) (h : QuadBijective F) : PairBijective F := by
  intro Y W
  refine ⟨?_,(weak _ _).comp (push_bijective F (pairChart Y W)).surjective⟩
  intro t t' e
  let U := PUnit.{u+1}
  let pad : Y × W → U × Y × U × W := fun p => (⟨⟩,p.1,⟨⟩,p.2)
  have hinj : Injective pad := fun _ _ eq => congrArg (fun a => (a.2.1,a.2.2.2)) eq
  apply map_injective F weak pad hinj
  apply (h U Y U W).injective
  have hy : push F Prod.fst t = push F Prod.fst t' := by
    rw [← pair_left,← pair_left]; exact congrArg (fun p => p.val.1) e
  have hw : push F Prod.snd t = push F Prod.snd t' := by
    rw [← pair_right,← pair_right]; exact congrArg (fun p => p.val.2) e
  apply Subtype.ext
  apply Prod.ext
  · have hy' := congrArg (push F (fun y : Y => ((⟨⟩ : U),y,(⟨⟩ : U)))) hy
    simpa only [quadComparison,comparison,push_push,quadChart,pad,left,Function.comp_def,Equiv.coe_fn_mk] using hy'
  · have hw' := congrArg (push F (fun w : W => ((⟨⟩ : U),(⟨⟩ : U),w))) hw
    simpa only [quadComparison,comparison,push_push,quadChart,pad,right,Function.comp_def,Equiv.coe_fn_mk] using hw'

/-- For a weakly pullback-preserving Set functor, the two triangle marginals determine every quadrilateral exactly when the functor preserves all pullbacks. -/
theorem exact_uniqueness_boundary (weak : WeakPullbacks F) :
    (QuadBijective F ↔ PairBijective F) ∧ (PairBijective F ↔ UniqueCouplings F) ∧
    (UniqueCouplings F ↔ PreservesPullbacks F) :=
  ⟨⟨pair_of_quad F weak,fun p => quad_of_preserves F (preserves_of_pair F weak p)⟩,
    pair_iff_unique F,
    ⟨fun h => preserves_of_pair F weak ((pair_iff_unique F).mpr h),
      fun h => (pair_iff_unique F).mp (pair_of_quad F weak (quad_of_preserves F h))⟩⟩

end ContextualComposition.CouplingPullbacks
