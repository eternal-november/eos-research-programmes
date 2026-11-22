module
public import ContextualComposition.NativeAugCollapse

@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X : Type w} (A : X → C)
local notation "F" => taggedTail A

set_option backward.isDefEq.respectTransparency false in
theorem taggedTailMap_cast {xs ys : List X} (e : xs = ys) (z : C) :
    taggedTailMap A (castOrder e) z = eqToHom (congrArg (fun v => F v z) e) := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem taggedTailMap_prefix {xs ys : List X} (as : List X) (p : AddressOrder X xs ys) (z : C) :
    taggedTailMap A (AddressOrder.prepend as p) z =
      eqToHom (tailAppend A as xs z).symm ≫ tailMap (as.map A) (taggedTailMap A p z) ≫
        eqToHom (tailAppend A as ys z) := by
  induction as with
  | nil =>
    change taggedTailMap A p z = 𝟙 _ ≫ taggedTailMap A p z ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  | cons a as ih =>
    rw [tailAppend_cons_iso_inv, tailAppend_cons_iso]
    change A a ◁ taggedTailMap A (AddressOrder.prepend as p) z =
      (A a ◁ eqToHom (tailAppend A as xs z).symm) ≫
        (A a ◁ tailMap (as.map A) (taggedTailMap A p z)) ≫ A a ◁ eqToHom (tailAppend A as ys z)
    rw [ih, whiskerLeft_comp, whiskerLeft_comp]

set_option backward.isDefEq.respectTransparency false in
theorem taggedTailMap_suffix {xs ys : List X} (p : AddressOrder X xs ys) (as : List X) (z : C) :
    eqToHom (tailAppend A xs as z) ≫ taggedTailMap A (p.suffix as) z ≫
      eqToHom (tailAppend A ys as z).symm = taggedTailMap A p (F as z) := by
  induction p with
  | ident xs =>
    change eqToHom (tailAppend A xs as z) ≫ 𝟙 _ ≫ eqToHom (tailAppend A xs as z).symm = 𝟙 _
    rw [Category.id_comp, eqToHom_trans]
    rfl
  | swap a b ts =>
    rw [tailAppend_cons_iso, tailAppend_cons_iso, tailAppend_cons_iso_inv, tailAppend_cons_iso_inv]
    change (A a ◁ A b ◁ eqToHom (tailAppend A ts as z)) ≫
      crossHead (A a) (A b) (F (ts ++ as) z) ≫
        A b ◁ A a ◁ eqToHom (tailAppend A ts as z).symm =
          crossHead (A a) (A b) (F ts (F as z))
    rw [crossHead_nat, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, eqToHom_trans]
    have h : eqToHom ((tailAppend A ts as z).trans (tailAppend A ts as z).symm) =
        𝟙 (F ts (F as z)) := rfl
    rw [h, whiskerLeft_id, whiskerLeft_id, Category.id_comp]
  | keep a p ih =>
    rw [tailAppend_cons_iso, tailAppend_cons_iso_inv]
    change (A a ◁ eqToHom (tailAppend A _ as z)) ≫
      (A a ◁ taggedTailMap A (p.suffix as) z) ≫ A a ◁ eqToHom (tailAppend A _ as z).symm =
        A a ◁ taggedTailMap A p (F as z)
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, ih]
  | @seq x y t p q hp hq =>
    let s := eqToHom (tailAppend A y as z)
    let si := eqToHom (tailAppend A y as z).symm
    let r := taggedTailMap A (p.suffix as) z
    let k := taggedTailMap A (q.suffix as) z
    let d := eqToHom (tailAppend A x as z)
    let e := eqToHom (tailAppend A t as z).symm
    change d ≫ (r ≫ k) ≫ e = _
    have h : si ≫ s = 𝟙 _ := by unfold s si; rw [eqToHom_trans]; rfl
    have p' : d ≫ r ≫ si = _ := hp
    have q' : s ≫ k ≫ e = _ := hq
    change _ = taggedTailMap A p (F as z) ≫ taggedTailMap A q (F as z)
    rw [← p', ← q']
    simp only [Category.assoc, reassoc_of% h]


set_option backward.isDefEq.respectTransparency false in
theorem taggedTailMap_parallel {xs ys xs' ys' : List X}
    (r : AddressOrder X xs xs') (s : AddressOrder X ys ys') (z : C) :
    taggedTailMap A (r.parallel s) z =
      eqToHom (tailAppend A xs ys z).symm ≫ taggedTailMap A r (F ys z) ≫
        tailMap (xs'.map A) (taggedTailMap A s z) ≫ eqToHom (tailAppend A xs' ys' z) := by
  change taggedTailMap A (r.suffix ys) z ≫ taggedTailMap A (AddressOrder.prepend xs' s) z = _
  rw [taggedTailMap_prefix]
  have h := taggedTailMap_suffix A r ys z
  let l := eqToHom (tailAppend A xs ys z).symm
  let l' := eqToHom (tailAppend A xs ys z)
  have e : l ≫ l' = 𝟙 _ := by unfold l l'; rw [eqToHom_trans]; rfl
  rw [← h]
  simp only [Category.assoc]
  change _ = l ≫ l' ≫ _
  rw [reassoc_of% e]

variable {I : Type w}
def gridOrder {e f : GridExpr I} (p : GridCircuit I e f) : AddressOrder I e.leaves f.leaves :=
  match p with
  | .ident _ => .ident _
  | .seq p q => .seq (gridOrder p) (gridOrder q)
  | .bin p q => (gridOrder p).parallel (gridOrder q)
  | .dupZero => .ident []
  | .mergeZero => .ident []
  | .middle e f g h =>
      .seq (castOrder (List.append_assoc e.leaves f.leaves (g.leaves ++ h.leaves)))
        (.seq (AddressOrder.prepend e.leaves (taggedBlockSwap f.leaves g.leaves h.leaves))
          (castOrder (List.append_assoc e.leaves g.leaves (f.leaves ++ h.leaves)).symm))

omit [SymmetricCategory C] in
theorem tailMap_comp (xs : List C) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    tailMap xs (f ≫ g) = tailMap xs f ≫ tailMap xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x ◁ tailMap xs (f ≫ g) = (x ◁ tailMap xs f) ≫ x ◁ tailMap xs g
    rw [ih, whiskerLeft_comp]

variable (B : I → C)
omit [SymmetricCategory C] in
theorem alignFour_eqToHom (e f g h : GridExpr I) (z : C) :
    alignFour B e f g h z =
      eqToHom (show taggedTail B e.leaves (taggedTail B f.leaves
        (taggedTail B g.leaves (taggedTail B h.leaves z))) =
          taggedTail B (GridExpr.bin (GridExpr.bin e f) (GridExpr.bin g h)).leaves z from
        (congrArg (taggedTail B e.leaves) (tailTriple B f.leaves g.leaves h.leaves z)).trans
          ((tailAppend B e.leaves (f.leaves ++ (g.leaves ++ h.leaves)) z).trans
            (congrArg (fun a => taggedTail B a z)
              (List.append_assoc e.leaves f.leaves (g.leaves ++ h.leaves)).symm))) := by
  unfold alignFour
  rw [tailMap_eqToHom, tailMap_eqToHom, eqToHom_trans, eqToHom_trans]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- The independently computed grid-chart circuit and the flattened
native word circuit implement the same actual coefficient arrow. -/
theorem gridOrder_semantics {e f : GridExpr I} (p : GridCircuit I e f) (z : C) :
    taggedTailMap B (gridOrder p) z = flatCircuit B p z := by
  induction p generalizing z with
  | ident => rfl
  | dupZero => rfl
  | mergeZero => rfl
  | seq p q hp hq =>
    simp only [gridOrder, taggedTailMap, flatCircuit, hp, hq]
  | @bin e f g h p q hp hq =>
    simp only [gridOrder, taggedTailMap_parallel, flatCircuit]
    rw [hp, hq]
    rfl
  | middle e f g h =>
    let D := taggedTail B
    let U := f.leaves
    let V := g.leaves
    let W := h.leaves
    let P := e.leaves
    let s := eqToHom (tailTriple B U V W z)
    let t := eqToHom (tailTriple B V U W z)
    let si := eqToHom (tailTriple B U V W z).symm
    let ti := eqToHom (tailTriple B V U W z).symm
    let n := taggedTailMap B (taggedBlockSwap U V W) z
    let K := swapBlocks (U.map B) (V.map B) (D W z)
    have k : s ≫ n ≫ ti = K := taggedBlockSwap_correct B U V W z
    have a : si ≫ s = 𝟙 _ := by unfold si s; rw [eqToHom_trans]; rfl
    have b : ti ≫ t = 𝟙 _ := by unfold ti t; rw [eqToHom_trans]; rfl
    have H : n = si ≫ K ≫ t := by
      rw [← k]
      simp only [Category.assoc, reassoc_of% a]
      exact (Category.comp_id n).symm.trans (congrArg (fun m => n ≫ m) b).symm
    simp only [gridOrder, taggedTailMap, taggedTailMap_cast, flatCircuit, taggedTailMap_prefix]
    change eqToHom _ ≫ ((eqToHom _ ≫ tailMap (P.map B) n ≫ eqToHom _) ≫ eqToHom _) = _
    rw [H, tailMap_comp, tailMap_comp]
    unfold si t
    have ainv : inv (alignFour B e f g h z) = eqToHom (show
        D ((GridExpr.bin (.bin e f) (.bin g h)).leaves) z =
        D P (D U (D V (D W z))) from
      ((congrArg (D P) (tailTriple B U V W z)).trans
        ((tailAppend B P (U ++ (V ++ W)) z).trans
          (congrArg (fun a => D a z) (List.append_assoc P U (V ++ W)).symm))).symm) := by
      apply IsIso.inv_eq_of_hom_inv_id
      rw [alignFour_eqToHom, eqToHom_trans]
      rfl
    rw [tailMap_eqToHom, tailMap_eqToHom, ainv, alignFour_eqToHom B e g f h z]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
