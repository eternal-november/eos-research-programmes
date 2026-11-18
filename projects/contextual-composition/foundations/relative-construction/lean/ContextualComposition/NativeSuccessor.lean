module
public import ContextualComposition.TailPasting
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeSquares
open CategoryTheory Opposite
universe b w u v

/-- Equality of arrows along specified-by-existence object equalities; the transports
are equality transports, never arbitrary isomorphisms. -/
structure Aligned {C : Type*} [Category* C] {x y x' y' : C} (f : x ⟶ y) (g : x' ⟶ y') : Prop where
  src : x = x'
  dst : y = y'
  comm : f ≫ eqToHom dst = eqToHom src ≫ g

namespace Aligned
variable {C : Type*} [Category* C]
theorem refl {x y : C} (f : x ⟶ y) : Aligned f f := ⟨rfl,rfl,by simp⟩
theorem symm {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'} (h : Aligned f g) : Aligned g f := by
  obtain ⟨rfl,rfl,h⟩ := h
  simp at h; subst g; exact refl _
theorem trans {x y x' y' x'' y'' : C} {f : x ⟶ y} {g : x' ⟶ y'} {k : x'' ⟶ y''}
    (h : Aligned f g) (j : Aligned g k) : Aligned f k := by
  obtain ⟨rfl,rfl,h⟩ := h
  obtain ⟨rfl,rfl,j⟩ := j
  simp at h j; subst g; subst k; exact refl _
theorem comp {x y z x' y' z' : C} {f : x ⟶ y} {g : y ⟶ z} {f' : x' ⟶ y'} {g' : y' ⟶ z'}
    (h : Aligned f f') (j : Aligned g g') : Aligned (f ≫ g) (f' ≫ g') := by
  obtain ⟨rfl,rfl,h⟩ := h
  obtain ⟨_,rfl,j⟩ := j
  simp at h j; subst f'; subst g'; exact refl _
theorem map {D : Type*} [Category* D] (F : C ⥤ D) {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'}
    (h : Aligned f g) : Aligned (F.map f) (F.map g) := by
  obtain ⟨rfl,rfl,h⟩ := h; simp at h; subst g; exact refl _
theorem trailing {x y z : C} (f : x ⟶ y) (h : y = z) : Aligned (f ≫ eqToHom h) f := by
  subst z; simp; exact refl _
theorem eq {x y : C} {f g : x ⟶ y} (h : Aligned f g) : f = g := by simpa using h.comm
end Aligned

variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (Y : Bᵒᵖ ⥤ Cat.{v,u}) (S : P.Split)

private theorem payload_trailing {K : Type*} [Category* K] {e : K ⥤ B}
    {x y z : Total Y e} (f : x ⟶ y) (h : y = z) :
    Aligned (payloadMap (f ≫ eqToHom h)) (payloadMap f) := by
  subst z
  have aux (g : x ⟶ y) (h : g = f) : Aligned (payloadMap g) (payloadMap f) := by
    subst g; exact Aligned.refl (payloadMap f)
  exact aux _ (Category.comp_id f)

private theorem grade_trailing {K : Type*} [Category* K] {e : K ⥤ B}
    {x y z : Total Y e} (f : x ⟶ y) (h : y = z) :
    Aligned (gradeMap (f ≫ eqToHom h)) (gradeMap f) := by
  subst z; simp; exact Aligned.refl _

private theorem payload_eq {K : Type*} [Category* K] {e : K ⥤ B}
    {x y : Total Y e} {f g : x ⟶ y} (h : f = g) : Aligned (payloadMap f) (payloadMap g) := by
  subst g; exact Aligned.refl _

theorem map_next {A D : B} (a : A ⟶ D) {p : P.grades.obj (op A)} {q : P.grades.obj (op D)}
    (k : p ⟶ (P.grades.map a.op).toFunctor.obj q) {x y : Y.obj (op ((P.extend D).obj q))}
    (f : x ⟶ y) :
    Aligned ((Y.map ((P.extend A).map k).op).toFunctor.map
      ((Y.map ((P.lift a).app q).op).toFunctor.map f))
      ((Y.map (next a k).op).toFunctor.map f) := by
  unfold next
  rw [op_comp,Y.map_comp]
  exact Aligned.refl _

section Native
variable {A D E : B} {a : A ⟶ D} {b : D ⟶ E}
    {x : Total Y (P.extend A)} {y : Total Y (P.extend D)} {z : Total Y (P.extend E)}
    (f : x ⟶ (P.baseRestrict Y a).obj y) (g : y ⟶ (P.baseRestrict Y b).obj z)

set_option backward.isDefEq.respectTransparency false in
theorem native_tail_decomposition :
    Aligned (payloadMap (nativePaste (P.extensionPresheaf Y S) (a := a) (b := b)
      (x := x) (y := y) (z := z) f g))
      (payloadMap f ≫ (Y.map ((P.extend A).map (gradeMap f)).op).toFunctor.map
        ((Y.map ((P.lift a).app (grade _ _ y)).op).toFunctor.map (payloadMap g))) := by
  let g' := (P.baseRestrict Y a).map g
  apply (payload_eq Y (Category.assoc f g' _).symm).trans
  apply (payload_trailing Y (f ≫ g') _).trans
  rw [payload_comp]
  apply (Aligned.refl (payloadMap f)).comp
  apply (Aligned.trailing _ _).trans
  apply Aligned.map
  dsimp only [g',Endpoints.baseRestrict]
  rw [restrict_payload]
  exact Aligned.trailing _ _

set_option backward.isDefEq.respectTransparency false in
theorem native_head_decomposition :
    gradeMap (nativePaste (P.extensionPresheaf Y S) (a := a) (b := b)
      (x := x) (y := y) (z := z) f g) = headComp (P := P) (gradeMap f) (gradeMap g) := by
  apply Aligned.eq
  unfold nativePaste
  rw [← Category.assoc]
  apply (grade_trailing _ _ _).trans
  unfold headComp
  rw [← Category.assoc]
  exact (Aligned.trailing _ _).symm
end Native

private theorem total_ext {K : Type*} [Category* K] {e : K ⥤ B}
    {x y : Total Y e} {f g : x ⟶ y} (head : gradeMap f = gradeMap g)
    (tail : Aligned (payloadMap f) (payloadMap g)) : f = g := by
  apply (homEquiv x y).injective
  refine Sigma.ext head ?_
  obtain ⟨s,t,h⟩ := tail
  -- Both payloads start at the same object; head equality identifies their targets.
  have aux {k j : grade Y e x ⟶ grade Y e y}
      {m : payload Y e x ⟶ (Y.map (e.map k).op).toFunctor.obj (payload Y e y)}
      {l : payload Y e x ⟶ (Y.map (e.map j).op).toFunctor.obj (payload Y e y)}
      (hk : k = j) (hh : Aligned m l) : HEq m l := by
    subst j; exact heq_of_eq hh.eq
  exact aux head ⟨s,t,h⟩

set_option backward.isDefEq.respectTransparency false in
theorem square_comp_native : {n : Nat} → {A D E : B} → {a : A ⟶ D} → {b : D ⟶ E} →
    {t : Chain P n A} → {z : Chain P n D} → {w : Chain P n E} →
    {x : Y.obj (op (endpoint t))} → {y : Y.obj (op (endpoint z))} → {h : Y.obj (op (endpoint w))} →
    (f : DecoratedHom Y a t z x y) → (g : DecoratedHom Y b z w y h) →
    squareEquiv Y S (a ≫ b) t w x h (decoratedComp S Y f g) =
      nativePaste (Iterates.layer P S Y n) (a := a) (b := b)
        (x := realize Y S t x) (y := realize Y S z y) (z := realize Y S w h)
        (squareEquiv Y S a t z x y f) (squareEquiv Y S b z w y h g)
  | 0, _, _, _, _, _, .nil _, .nil _, .nil _, _, _, _, _, _ => rfl
  | n+1, A, D, E, a, b, .cons p t, .cons q z, .cons r w, x, y, h, f, g => by
    let F := Iterates.layer P S Y n
    let f' := squareEquiv Y S a (.cons p t) (.cons q z) x y f
    let g' := squareEquiv Y S b (.cons q z) (.cons r w) y h g
    let k := f.1.1
    let j := g.1.1
    let ft := squareEquiv Y S (next a k) t z x y (tailPart Y f)
    let gt := squareEquiv Y S (next b j) z w y h (tailPart Y g)
    apply total_ext F (e := P.extend A)
    · exact (native_head_decomposition F S (a := a) (b := b) (x := _) (y := _) (z := _) f' g').symm
    · apply Aligned.symm
      apply (native_tail_decomposition F S (a := a) (b := b) (x := _) (y := _) (z := _) f' g').trans
      rw [compared_paste_tail]
      apply Aligned.trans _ (Aligned.trailing _ _).symm
      rw [square_comp_native (tailPart Y f) (tailPart Y g)]
      unfold nativePaste
      rw [← Category.assoc]
      apply Aligned.trans _ (Aligned.trailing _ _).symm
      apply Aligned.comp
      · change Aligned (payloadMap (squareEquiv Y S a (.cons p t) (.cons q z) x y f)) ft
        rw [compared_tail]
        exact Aligned.trailing _ _
      · apply (map_next F a k (payloadMap g')).trans
        apply Aligned.map
        change Aligned (payloadMap (squareEquiv Y S b (.cons q z) (.cons r w) y h g)) gt
        rw [compared_tail]
        exact Aligned.trailing _ _
section Associativity
variable {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Cat.{v,u})
    {A D E H : C} {a : A ⟶ D} {b : D ⟶ E} {c : E ⟶ H}
    {x : F.obj (op A)} {y : F.obj (op D)} {z : F.obj (op E)} {w : F.obj (op H)}
    (f : x ⟶ (F.map a.op).toFunctor.obj y) (g : y ⟶ (F.map b.op).toFunctor.obj z)
    (h : z ⟶ (F.map c.op).toFunctor.obj w)
theorem native_reduced : Aligned (nativePaste F (a := a) (b := b) (x := x) (y := y) (z := z) f g)
    (f ≫ (F.map a.op).toFunctor.map g) := by
  unfold nativePaste; rw [← Category.assoc]; exact Aligned.trailing _ _

set_option backward.isDefEq.respectTransparency false in
theorem native_assoc : Aligned
    (nativePaste F (a := a ≫ b) (b := c) (x := x) (y := z) (z := w)
      (nativePaste F (a := a) (b := b) (x := x) (y := y) (z := z) f g) h)
    (nativePaste F (a := a) (b := b ≫ c) (x := x) (y := y) (z := w) f
      (nativePaste F (a := b) (b := c) (x := y) (y := z) (z := w) g h)) := by
  apply (native_reduced F _ _).trans
  apply Aligned.trans _ (native_reduced F _ _).symm
  have mapAssoc : Aligned ((F.map (a ≫ b).op).toFunctor.map h)
      ((F.map a.op).toFunctor.map ((F.map b.op).toFunctor.map h)) := by
    rw [op_comp,F.map_comp]; exact Aligned.refl _
  apply ((native_reduced F f g).comp mapAssoc).trans
  rw [Category.assoc]
  apply (Aligned.refl f).comp
  have hh := (native_reduced F g h).map (F.map a.op).toFunctor
  rw [Functor.map_comp] at hh
  exact hh.symm
end Associativity

set_option backward.isDefEq.respectTransparency false in
theorem decorated_assoc {n A D E H} {a : A ⟶ D} {b : D ⟶ E} {c : E ⟶ H}
    {t : Chain P n A} {z : Chain P n D} {w : Chain P n E} {l : Chain P n H}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    {h : Y.obj (op (endpoint w))} {j : Y.obj (op (endpoint l))}
    (f : DecoratedHom Y a t z x y) (g : DecoratedHom Y b z w y h) (k : DecoratedHom Y c w l h j) :
    rebaseDecorated Y (Category.assoc a b c) (decoratedComp S Y (decoratedComp S Y f g) k) =
      decoratedComp S Y f (decoratedComp S Y g k) := by
  apply (squareEquiv Y S _ _ _ _ _).injective
  rw [comparison_rebase]
  apply Aligned.eq
  apply (Aligned.trailing _ _).trans
  simp only [square_comp_native]
  apply native_assoc
end ContextualComposition.GrothendieckStep.TelescopeSquares
