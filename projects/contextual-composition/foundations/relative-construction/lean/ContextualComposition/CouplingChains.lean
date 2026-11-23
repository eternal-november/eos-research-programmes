module
public import ContextualComposition.AllCouplings

/-! Typed relational category laws, compatible state maps, and retained endpoint effects of finite chains. -/

@[expose] public section
namespace ContextualComposition.CouplingChains
open CategoryTheory CouplingPullbacks AllCouplings
set_option backward.isDefEq.respectTransparency false

universe u
variable (F : Type u ⥤ Type u) {P Q R S : Effect F}

def compose (a : Hom F P Q) (b : Hom F Q R) (e : Hom F P R) := Comp F a.val b.val e.val

theorem assoc (weak : WeakPullbacks F) (a : Hom F P Q) (b : Hom F Q R) (c : Hom F R S) (e : Hom F P S) :
    (∃ d : Hom F P R, compose F a b d ∧ compose F d c e) ↔
    ∃ d : Hom F Q S, compose F b c d ∧ compose F a d e := by
  constructor
  · rintro ⟨d,h,k⟩
    obtain ⟨s,hs,he⟩ := (associative F weak _ _ _ _).mp ⟨d.val,h,k⟩
    have m := endpoints F _ _ _ hs
    exact ⟨⟨s,m.1.trans b.property.1,m.2.trans c.property.2⟩,hs,he⟩
  · rintro ⟨d,h,k⟩
    obtain ⟨s,hs,he⟩ := (associative F weak _ _ _ _).mpr ⟨d.val,h,k⟩
    have m := endpoints F _ _ _ hs
    exact ⟨⟨s,m.1.trans a.property.1,m.2.trans b.property.2⟩,hs,he⟩

theorem left_unit (weak : WeakPullbacks F) (a e : Hom F P Q) : compose F (identity F P) a e ↔ a = e :=
  (left_identity F weak _ _ _ a.property.1).trans ⟨Subtype.ext,congrArg Subtype.val⟩

theorem right_unit (weak : WeakPullbacks F) (a e : Hom F P Q) : compose F a (identity F Q) e ↔ a = e :=
  (right_identity F weak _ _ _ a.property.2).trans ⟨Subtype.ext,congrArg Subtype.val⟩

structure StateMap (P Q : Effect F) where
  run : P.carrier → Q.carrier
  preserves : push F run P.law = Q.law

def change {P' Q' : Effect F} (p : StateMap F P P') (q : StateMap F Q Q') (a : Hom F P Q) : Hom F P' Q' :=
  ⟨push F (Prod.map p.run q.run) a.val,by
    constructor
    · rw [push_push]
      exact (push_push F Prod.fst p.run a.val).symm.trans ((congrArg (push F p.run) a.property.1).trans p.preserves)
    · rw [push_push]
      exact (push_push F Prod.snd q.run a.val).symm.trans ((congrArg (push F q.run) a.property.2).trans q.preserves)⟩

theorem change_identity {P' : Effect F} (p : StateMap F P P') :
    change F p p (identity F P) = identity F P' := by
  apply Subtype.ext
  change push F (Prod.map p.run p.run) (push F diag P.law) = push F diag P'.law
  rw [push_push,← p.preserves,push_push]; rfl

theorem change_lax {P' Q' R' : Effect F} (p : StateMap F P P') (q : StateMap F Q Q') (r : StateMap F R R')
    (a : Hom F P Q) (b : Hom F Q R) (e : Hom F P R) (h : compose F a b e) :
    compose F (change F p q a) (change F q r b) (change F p r e) := by
  obtain ⟨s,ha,hb,he⟩ := h
  let k := Prod.map p.run (Prod.map q.run r.run)
  refine ⟨push F k s,?_,?_,?_⟩
  · change push F xy (push F k s) = push F (Prod.map p.run q.run) a.val
    rw [← ha,push_push,push_push]; rfl
  · change push F yz (push F k s) = push F (Prod.map q.run r.run) b.val
    rw [← hb,push_push,push_push]; rfl
  · change push F xz (push F k s) = push F (Prod.map p.run r.run) e.val
    rw [← he,push_push,push_push]; rfl

structure StateIso (P Q : Effect F) where
  equiv : P.carrier ≃ Q.carrier
  preserves : push F equiv P.law = Q.law

def StateIso.forward (i : StateIso F P Q) : StateMap F P Q := ⟨i.equiv,i.preserves⟩

def StateIso.backward (i : StateIso F P Q) : StateMap F Q P where
  run := i.equiv.symm
  preserves := by
    rw [← i.preserves,push_push,show (⇑i.equiv.symm ∘ ⇑i.equiv) = id by funext x; simp,push_id]

theorem change_inverse {P' Q' : Effect F} (i : StateIso F P P') (j : StateIso F Q Q') (a : Hom F P Q) :
    change F (i.backward F) (j.backward F) (change F (i.forward F) (j.forward F) a) = a := by
  apply Subtype.ext
  change push F (Prod.map i.equiv.symm j.equiv.symm) (push F (Prod.map i.equiv j.equiv) a.val) = a.val
  rw [push_push,show (Prod.map (⇑i.equiv.symm) (⇑j.equiv.symm) ∘ Prod.map (⇑i.equiv) (⇑j.equiv)) = id by
    funext x; rcases x with ⟨x,y⟩; simp,push_id]

def StateIso.symm (i : StateIso F P Q) : StateIso F Q P :=
  ⟨i.equiv.symm,(i.backward F).preserves⟩

def changeEquiv {P' Q' : Effect F} (i : StateIso F P P') (j : StateIso F Q Q') :
    Hom F P Q ≃ Hom F P' Q' where
  toFun := change F (i.forward F) (j.forward F)
  invFun := change F (i.backward F) (j.backward F)
  left_inv := change_inverse F i j
  right_inv := change_inverse F (i.symm F) (j.symm F)

theorem change_iff {P' Q' R' : Effect F} (i : StateIso F P P') (j : StateIso F Q Q') (k : StateIso F R R')
    (a : Hom F P Q) (b : Hom F Q R) (e : Hom F P R) :
    compose F a b e ↔ compose F (change F (i.forward F) (j.forward F) a)
      (change F (j.forward F) (k.forward F) b) (change F (i.forward F) (k.forward F) e) := by
  refine ⟨change_lax F _ _ _ a b e,fun h => ?_⟩
  have hh := change_lax F (i.backward F) (j.backward F) (k.backward F) _ _ _ h
  simpa only [change_inverse] using hh

/-- A finite chain starts at a supplied effect; each extension prescribes a joint law on consecutive coordinates. -/
inductive Chain (F : Type u ⥤ Type u) (X : Type u) : Type u → Type (u+1) where
  | nil (p : F.obj X) : Chain F X X
  | snoc {Y Z} (s : Chain F X Y) (b : F.obj (Y × Z)) : Chain F X Z

variable {F} {X Y Z : Type u}

def Chain.Carrier : {Y : Type u} → Chain F X Y → Type u
  | _, .nil _ => X
  | _, .snoc (Z:=Z) p _ => p.Carrier × Z

def Chain.first : {Y : Type u} → (p : Chain F X Y) → p.Carrier → X
  | _, .nil _ => id
  | _, .snoc p _ => fun t => p.first t.1

def Chain.last : {Y : Type u} → (p : Chain F X Y) → p.Carrier → Y
  | _, .nil _ => id
  | _, .snoc _ _ => Prod.snd

def Chain.ends (p : Chain F X Y) (t : p.Carrier) := (p.first t,p.last t)

def Chain.Realizes : {Y : Type u} → (p : Chain F X Y) → F.obj p.Carrier → Prop
  | _, .nil law, t => t = law
  | _, .snoc p b, t => p.Realizes (push F Prod.fst t) ∧ push F (fun x => (p.last x.1,x.2)) t = b

def Chain.Possible : {Y : Type u} → (p : Chain F X Y) → F.obj (X × Y) → Prop
  | _, .nil law, e => e = push F diag law
  | _, .snoc p b, e => ∃ d, p.Possible d ∧ Comp F d b e

theorem Chain.possible_iff_joint (weak : WeakPullbacks F) (p : Chain F X Y) (e : F.obj (X × Y)) :
    p.Possible e ↔ ∃ t, p.Realizes t ∧ push F p.ends t = e := by
  induction p with
  | nil law =>
    exact ⟨fun h => ⟨law,rfl,h.symm⟩,fun ⟨_,rfl,h⟩ => h.symm⟩
  | @snoc Y Z p b ih =>
    let triple (t : p.Carrier × Z) := (p.first t.1,p.last t.1,t.2)
    constructor
    · rintro ⟨d,hd,s,hs,hb,he⟩
      obtain ⟨t,ht,hm⟩ := (ih d).mp hd
      obtain ⟨j,jt,js⟩ := glue F weak p.ends xy Prod.fst triple
        (fun w => (w.val.1,w.val.2.2.2)) rfl (by
          funext w
          exact Prod.ext (congrArg (fun k : X × Y => k.1) w.property)
            (Prod.ext (congrArg (fun k : X × Y => k.2) w.property) rfl))
        t s (hm.trans hs.symm)
      exact ⟨j,⟨jt.symm ▸ ht,(marginal F triple yz _ rfl js).trans hb⟩,(marginal F triple xz _ rfl js).trans he⟩
    · rintro ⟨t,⟨ht,hb⟩,he⟩
      refine ⟨push F p.ends (push F Prod.fst t),(ih _).mpr ⟨_,ht,rfl⟩,push F triple t,?_,?_,?_⟩
      · rw [push_push,push_push]; rfl
      · rw [push_push]; exact hb
      · rw [push_push]; exact he

end ContextualComposition.CouplingChains
