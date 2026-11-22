module

public import ContextualComposition.FubiniIso

@[expose] public section

/-! A global empty augmentation is incompatible with ambiguous arrows out
of zero in any coefficient setting with two natural tensor absorbers. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v
variable {C : Type u} {K : Coeff.{u,v} C} {T : Bi K} {Z U : C}
structure Absorbers (T : Bi K) (Z U : C) where
  left (a : C) : K.Hom (T.obj Z a) Z
  leftInv (a : C) : Inv (left a)
  leftNat {a b : C} (p : K.Hom a b) : K.seq (T.map (K.id Z) p) (left b) = left a
  right (a : C) : K.Hom (T.obj a Z) Z
  rightInv (a : C) : Inv (right a)
  rightNat {a b : C} (p : K.Hom a b) : K.seq (T.map p (K.id Z)) (right b) = right a
  unitor (a : C) : K.Hom (T.obj a U) a
  unitInv (a : C) : Inv (unitor a)
  unitNat {a b : C} (p : K.Hom a b) : K.seq (T.map p (K.id U)) (unitor b) = K.seq (unitor a) p
variable (E : Absorbers T Z U)
def fromZero (e : K.Hom Z U) (a : C) : K.Hom Z a :=
  K.seq (E.rightInv a).inv (K.seq (T.map (K.id a) e) (E.unitor a))
theorem Inv.cancelR {a b c : C} {f : K.Hom b c} (i : Inv f) {p q : K.Hom a b}
    (h : K.seq p f = K.seq q f) : p = q := by
  have hh := congrArg (fun g => K.seq g i.inv) h
  simpa only [K.assoc, i.hi, K.seq_id] using hh
theorem Inv.cancelL {a b c : C} {f : K.Hom a b} (i : Inv f) {p q : K.Hom b c}
    (h : K.seq f p = K.seq f q) : p = q := by
  have hh := congrArg (fun g => K.seq i.inv g) h
  simpa only [← K.assoc, i.ih, K.id_seq] using hh
include E in
theorem zero_unique (e : K.Hom Z U) {a : C} (p q : K.Hom Z a) : p = q := by
  have r : T.map p (K.id Z) = T.map q (K.id Z) :=
    (E.rightInv a).cancelR ((E.rightNat p).trans (E.rightNat q).symm)
  have interchange (f : K.Hom Z a) : K.seq (T.map (K.id Z) e) (T.map f (K.id U)) =
      K.seq (T.map f (K.id Z)) (T.map (K.id a) e) := by
    rw [← T.map_seq, ← T.map_seq, K.id_seq, K.seq_id, K.id_seq, K.seq_id]
  have h := (interchange p).trans ((congrArg (fun k => K.seq k (T.map (K.id a) e)) r).trans (interchange q).symm)
  have split : K.seq (E.leftInv Z).inv (T.map (K.id Z) e) = (E.leftInv U).inv := by
    apply (E.leftInv U).cancelR
    rw [K.assoc, E.leftNat, (E.leftInv Z).ih, (E.leftInv U).ih]
  have hh := congrArg (fun k => K.seq (E.leftInv Z).inv k) h
  simp only [← K.assoc, split] at hh
  have t := congrArg (fun k => K.seq (E.left U) k) hh
  simp only [← K.assoc, (E.leftInv U).hi, K.id_seq] at t
  apply (E.unitInv Z).cancelL
  rw [← E.unitNat, ← E.unitNat, t]
include E in
theorem global_empty_iff_initial : Nonempty (K.Hom Z U) ↔
    ∀ a, ∃ f : K.Hom Z a, ∀ g, g = f := by
  constructor
  · rintro ⟨e⟩ a
    exact ⟨fromZero E e a,fun g => zero_unique E e g _⟩
  · intro h
    exact ⟨(h U).choose⟩

def emptyFamily : Family C := ⟨0,Fin.elim0⟩
theorem empty_carrier_iff {S : Push K} {total : List C → C} (pin : FoldPinned S total) :
    Nonempty (Hom S (emptyFamily (C:=C)) (terminalShape U)) ↔ Nonempty (K.Hom (total []) U) := by
  constructor
  · rintro ⟨h⟩
    have e : S.obj h.addr (emptyFamily (C:=C)).val (0:Fin 1) = total [] :=
      empty_fibre S pin h.addr _ (0:Fin 1) (fun i => Fin.elim0 i)
    exact ⟨e ▸ h.cell (0:Fin 1)⟩
  · rintro ⟨e⟩
    let f : Fin 0 → Fin 1 := Fin.elim0
    refine ⟨⟨f,fun j => ?_⟩⟩
    have h := empty_fibre S pin f (emptyFamily (C:=C)).val j (fun i => Fin.elim0 i)
    exact h.symm ▸ e

/-- Only a structural isomorphism (not equality of objects) is needed to
test admissibility of the fixed empty carrier. -/
structure EmptyChart (S : Push K) (Z : C) where
  hom (f : Fin 0 → Fin 1) (i : Fin 1) : K.Hom (S.obj f (emptyFamily (C:=C)).val i) Z
  inverse (f i) : Inv (hom f i)
theorem empty_carrier_chart {S : Push K} (h : EmptyChart S Z) :
    Nonempty (Hom S (emptyFamily (C:=C)) (terminalShape U)) ↔ Nonempty (K.Hom Z U) := by
  constructor
  · rintro ⟨a⟩
    exact ⟨K.seq (h.inverse a.addr (0:Fin 1)).inv (a.cell (0:Fin 1))⟩
  · rintro ⟨e⟩
    exact ⟨⟨Fin.elim0, fun j => K.seq (h.hom Fin.elim0 j) e⟩⟩
include E in
theorem native_empty_dichotomy {S : Push K} (h : EmptyChart S Z) :
    Nonempty (Hom S (emptyFamily (C:=C)) (terminalShape U)) ↔
      ∀ a, ∃ f : K.Hom Z a, ∀ g, g = f :=
  (empty_carrier_chart h).trans (global_empty_iff_initial E)
end ContextualComposition.NativeFinitePush.DependentFibre
