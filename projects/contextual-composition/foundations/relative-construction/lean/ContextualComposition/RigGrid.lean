module

public import Mathlib.CategoryTheory.NatIso

@[expose] public section

/-!
# Finite distributor grids without additive coproducts

The two directions of expansion of a finite rectangle are compared using an
explicit row-to-column structural arrow. Only the binary middle-four and two
nullary diagrams are assumed at the two-variable interface. The inductive
proof does not use injections, initiality, or equality of additive endpoints.
-/

namespace ContextualComposition.RigGrid

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type u} [Category.{v} C]

/-- Data and morphism laws of a bifunctor, with both arguments explicit. -/
structure Binary where
  obj : C → C → C
  map : ∀ {a b c d : C}, (a ⟶ b) → (c ⟶ d) → (obj a c ⟶ obj b d)
  map_id (a c : C) : map (𝟙 a) (𝟙 c) = 𝟙 (obj a c)
  map_comp {a b c d e f : C} (p : a ⟶ b) (q : b ⟶ c) (r : d ⟶ e) (s : e ⟶ f) :
    map (p ≫ q) (r ≫ s) = map p r ≫ map q s

def Binary.mapIso (B : Binary (C := C)) {a b c d : C} (f : a ≅ b) (g : c ≅ d) :
    B.obj a c ≅ B.obj b d where
  hom := B.map f.hom g.hom
  inv := B.map f.inv g.inv
  hom_inv_id := by rw [← B.map_comp, f.hom_inv_id, g.hom_inv_id, B.map_id]
  inv_hom_id := by rw [← B.map_comp, f.inv_hom_id, g.inv_hom_id, B.map_id]

def Binary.left (B : Binary (C := C)) (a : C) : C ⥤ C where
  obj := B.obj a
  map f := B.map (𝟙 a) f
  map_id _ := B.map_id _ _
  map_comp f g := by simpa only [Category.id_comp] using B.map_comp (𝟙 a) (𝟙 a) f g

def Binary.right (B : Binary (C := C)) (a : C) : C ⥤ C where
  obj b := B.obj b a
  map f := B.map f (𝟙 a)
  map_id _ := B.map_id _ _
  map_comp f g := by simpa only [Category.id_comp] using B.map_comp f g (𝟙 a) (𝟙 a)

/-- The additive maps used by the right-fold presentation. In a symmetric
monoidal category `middle` swaps the addressed middle pair; `mergeZero`
is either unitor at the additive unit. No product laws occur in this interface. -/
structure Additive where
  sum : Binary (C := C)
  zero : C
  middle (a b c d : C) :
    sum.obj (sum.obj a b) (sum.obj c d) ≅ sum.obj (sum.obj a c) (sum.obj b d)
  middle_natural {a b c d a' b' c' d' : C}
      (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') (k : d ⟶ d') :
    sum.map (sum.map f g) (sum.map h k) ≫ (middle a' b' c' d').hom =
      (middle a b c d).hom ≫ sum.map (sum.map f h) (sum.map g k)
  mergeZero : sum.obj zero zero ≅ zero

def Additive.fold (S : Additive (C := C)) : List C → C
  | [] => S.zero
  | x :: xs => S.sum.obj x (S.fold xs)

/-- Binary and nullary forward splitting of an endofunctor. The finite
interchange lemma only needs these components, not a unital or associative
presentation of arbitrary additive partition maps. -/
structure Split (S : Additive (C := C)) (F : C ⥤ C) where
  bin (a b : C) : F.obj (S.sum.obj a b) ≅ S.sum.obj (F.obj a) (F.obj b)
  nil : F.obj S.zero ≅ S.zero

def Split.foldIso {S : Additive (C := C)} {F : C ⥤ C} (D : Split S F) :
    (xs : List C) → F.obj (S.fold xs) ≅ S.fold (xs.map F.obj)
  | [] => D.nil
  | x :: xs => D.bin x (S.fold xs) ≪≫ S.sum.mapIso (Iso.refl _) (D.foldIso xs)

/-- The pointwise additive sum retains the two actual component arrows. -/
def Additive.pointwise (S : Additive (C := C)) (F G : C ⥤ C) : C ⥤ C where
  obj a := S.sum.obj (F.obj a) (G.obj a)
  map f := S.sum.map (F.map f) (G.map f)
  map_id a := by rw [F.map_id, G.map_id, S.sum.map_id]
  map_comp f g := by rw [F.map_comp, G.map_comp, S.sum.map_comp]

def Split.pointwise {S : Additive (C := C)} {F G : C ⥤ C} (D : Split S F) (E : Split S G) :
    Split S (S.pointwise F G) where
  bin a b := S.sum.mapIso (D.bin a b) (E.bin a b) ≪≫
    S.middle (F.obj a) (F.obj b) (G.obj a) (G.obj b)
  nil := S.sum.mapIso D.nil E.nil ≪≫ S.mergeZero

def Additive.zeroFunctor (S : Additive (C := C)) : C ⥤ C where
  obj _ := S.zero
  map _ := 𝟙 S.zero
  map_id _ := rfl
  map_comp _ _ := by simp

def Additive.zeroSplit (S : Additive (C := C)) : Split S S.zeroFunctor where
  bin _ _ := S.mergeZero.symm
  nil := Iso.refl _

/-- A transformation respecting only the binary and nullary splitting
diagrams (the comparison orientation is the forward distributor). -/
structure PreservesSplit {S : Additive (C := C)} {F G : C ⥤ C}
    (D : Split S F) (E : Split S G) (t : F ⟶ G) : Prop where
  bin (a b : C) : t.app (S.sum.obj a b) ≫ (E.bin a b).hom =
    (D.bin a b).hom ≫ S.sum.map (t.app a) (t.app b)
  nil : t.app S.zero ≫ E.nil.hom = D.nil.hom

/-- Sum of a family of arrows along a given address list; unlike a function
on values it does not identify repeated occurrences. -/
def Additive.foldMap (S : Additive (C := C)) {A : Type*}
    {L R : A → C} (t : ∀ a : A, L a ⟶ R a) :
    (xs : List A) → S.fold (xs.map L) ⟶ S.fold (xs.map R)
  | [] => 𝟙 S.zero
  | x :: xs => S.sum.map (t x) (S.foldMap t xs)

theorem PreservesSplit.fold {S : Additive (C := C)} {F G : C ⥤ C}
    {D : Split S F} {E : Split S G} {t : F ⟶ G} (h : PreservesSplit D E t) (xs : List C) :
    t.app (S.fold xs) ≫ (E.foldIso xs).hom =
      (D.foldIso xs).hom ≫ S.foldMap t.app xs := by
  induction xs with
  | nil =>
    change t.app S.zero ≫ E.nil.hom = D.nil.hom ≫ 𝟙 S.zero
    rw [Category.comp_id, h.nil]
  | cons x xs ih =>
    simp only [Additive.fold, Split.foldIso, Iso.trans_hom, Binary.mapIso, Iso.refl_hom, Additive.foldMap]
    rw [← Category.assoc, h.bin, Category.assoc]
    simp only [Category.assoc, ← S.sum.map_comp, Category.id_comp, Category.comp_id, ih]

/-- One column-wise, occurrence-preserving merge of two rows. -/
def Additive.zipRows (S : Additive (C := C)) {A : Type*} (F G : A → C) :
    (ys : List A) → S.sum.obj (S.fold (ys.map F)) (S.fold (ys.map G)) ≅
      S.fold (ys.map (fun y => S.sum.obj (F y) (G y)))
  | [] => S.mergeZero
  | y :: ys => S.middle (F y) (S.fold (ys.map F)) (G y) (S.fold (ys.map G)) ≪≫
    S.sum.mapIso (Iso.refl _) (S.zipRows F G ys)

theorem Split.pointwise_fold_hom {S : Additive (C := C)} {F G : C ⥤ C}
    (D : Split S F) (E : Split S G) (ys : List C) :
    ((D.pointwise E).foldIso ys).hom =
      (S.sum.mapIso (D.foldIso ys) (E.foldIso ys)).hom ≫ (S.zipRows F.obj G.obj ys).hom := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [Split.foldIso, Additive.zipRows, Iso.trans_hom, Binary.mapIso, Iso.refl_hom]
    rw [ih]
    simp only [Split.pointwise, Additive.pointwise, Iso.trans_hom, Binary.mapIso, Category.assoc,
      S.sum.map_comp]
    have h := S.middle_natural (𝟙 (F.obj y)) (D.foldIso ys).hom
      (𝟙 (G.obj y)) (E.foldIso ys).hom
    rw [← Category.assoc (S.sum.map (S.sum.map (𝟙 (F.obj y)) (D.foldIso ys).hom)
      (S.sum.map (𝟙 (G.obj y)) (E.foldIso ys).hom)), h]
    simp only [Category.assoc, S.sum.map_id]
    rw [← S.sum.map_comp, Category.id_comp]

theorem Additive.foldMap_id (S : Additive (C := C)) {A : Type*} (F : A → C)
    (xs : List A) : S.foldMap (fun x => 𝟙 (F x)) xs = 𝟙 (S.fold (xs.map F)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldMap, ih, S.sum.map_id]
    rfl

theorem Additive.foldMap_comp (S : Additive (C := C)) {A : Type*}
    {F G H : A → C} (f : ∀ a, F a ⟶ G a) (g : ∀ a, G a ⟶ H a) (xs : List A) :
    S.foldMap (fun x => f x ≫ g x) xs = S.foldMap f xs ≫ S.foldMap g xs := by
  induction xs with
  | nil =>
    change 𝟙 S.zero = 𝟙 S.zero ≫ 𝟙 S.zero
    simp only [Category.id_comp]
  | cons x xs ih => simp only [foldMap, ih, S.sum.map_comp]

theorem Additive.zipRows_natural (S : Additive (C := C)) {A : Type*}
    {F F' G G' : A → C} (f : ∀ a, F a ⟶ F' a) (g : ∀ a, G a ⟶ G' a) (ys : List A) :
    S.sum.map (S.foldMap f ys) (S.foldMap g ys) ≫ (S.zipRows F' G' ys).hom =
      (S.zipRows F G ys).hom ≫ S.foldMap (fun y => S.sum.map (f y) (g y)) ys := by
  induction ys with
  | nil =>
    change S.sum.map (𝟙 S.zero) (𝟙 S.zero) ≫ S.mergeZero.hom =
      S.mergeZero.hom ≫ 𝟙 S.zero
    rw [S.sum.map_id, Category.id_comp, Category.comp_id]
  | cons y ys ih =>
    simp only [foldMap, zipRows, Iso.trans_hom, Binary.mapIso, Iso.refl_hom]
    rw [← Category.assoc, S.middle_natural]
    simp only [Category.assoc, ← S.sum.map_comp, Category.id_comp, Category.comp_id, ih]

/-- Input slice of rig coherence needed for rectangular expansion. The
finite conclusion is not a field. In an ordinary rig, `rightDist` is the
right distributor as a natural isomorphism in the remaining variable, and
its two diagrams are the binary middle-four and nullary distributor law.
The two diagrams of `absorbLeft` are the corresponding zero coherences. -/
structure GridData (S : Additive (C := C)) where
  mul : Binary (C := C)
  leftSplit (a : C) : Split S (mul.left a)
  rightDist (a b : C) : mul.left (S.sum.obj a b) ≅ S.pointwise (mul.left a) (mul.left b)
  absorbLeft : mul.left S.zero ≅ S.zeroFunctor
  rightDist_preserves (a b : C) :
    PreservesSplit (leftSplit _) ((leftSplit a).pointwise (leftSplit b)) (rightDist a b).hom
  absorbLeft_preserves : PreservesSplit (leftSplit _) S.zeroSplit absorbLeft.hom

variable {S : Additive (C := C)} (K : GridData S)

def GridData.rightSplit (c : C) : Split S (K.mul.right c) where
  bin a b := (K.rightDist a b).app c
  nil := K.absorbLeft.app c

def GridData.rowObj (xs ys : List C) : C :=
  S.fold (xs.map (fun x => S.fold (ys.map (K.mul.obj x))))

def GridData.colObj (xs ys : List C) : C :=
  S.fold (ys.map (fun y => S.fold (xs.map (fun x => K.mul.obj x y))))

/-- Right-first distribution; then each row is expanded by the left
distributor. Empty outer and inner lists use their respective absorbers. -/
def GridData.rowExpand : (xs ys : List C) →
    K.mul.obj (S.fold xs) (S.fold ys) ≅ K.rowObj xs ys
  | [], ys => K.absorbLeft.app (S.fold ys)
  | x :: xs, ys => (K.rightDist x (S.fold xs)).app (S.fold ys) ≪≫
      S.sum.mapIso ((K.leftSplit x).foldIso ys) (rowExpand xs ys)

/-- Structural transpose, built entirely in the additive operations.
Its recursive step keeps the head row's occurrence at the head of each
column and transposes the remaining rows. -/
def GridData.transpose : (xs ys : List C) → K.rowObj xs ys ≅ K.colObj xs ys
  | [], ys => S.zeroSplit.foldIso ys
  | x :: xs, ys =>
    S.sum.mapIso (Iso.refl _) (transpose xs ys) ≪≫ S.zipRows (K.mul.obj x)
      (fun y => S.fold (xs.map (fun a => K.mul.obj a y))) ys

/-- Left-first distribution; then each column is expanded by the right
distributor. This definition does not use `transpose`. -/
def GridData.colExpand (xs ys : List C) : K.mul.obj (S.fold xs) (S.fold ys) ⟶ K.colObj xs ys :=
  ((K.leftSplit (S.fold xs)).foldIso ys).hom ≫
    S.foldMap (fun y => ((K.rightSplit y).foldIso xs).hom) ys

theorem GridData.interchange (xs ys : List C) :
    (K.rowExpand xs ys).hom ≫ (K.transpose xs ys).hom = K.colExpand xs ys := by
  induction xs with
  | nil =>
    have h := K.absorbLeft_preserves.fold ys
    exact h
  | cons x xs ih =>
    simp only [GridData.rowExpand, GridData.transpose, Iso.trans_hom, Binary.mapIso,
      Iso.refl_hom, Category.assoc]
    rw [← Category.assoc (S.sum.map ((K.leftSplit x).foldIso ys).hom (K.rowExpand xs ys).hom),
      ← S.sum.map_comp]
    rw [ih]
    let F := K.mul.left x
    let G := K.mul.left (S.fold xs)
    let D : Split S F := K.leftSplit x
    let E : Split S G := K.leftSplit (S.fold xs)
    let H (y : C) := S.fold (xs.map (fun a => K.mul.obj a y))
    let k (y : C) : G.obj y ⟶ H y := ((K.rightSplit y).foldIso xs).hom
    let t := (K.rightDist x (S.fold xs)).hom
    change t.app (S.fold ys) ≫
      S.sum.map ((D.foldIso ys).hom ≫ 𝟙 _) ((E.foldIso ys).hom ≫ S.foldMap k ys) ≫
        (S.zipRows F.obj H ys).hom =
      ((K.leftSplit (S.sum.obj x (S.fold xs))).foldIso ys).hom ≫
        S.foldMap (fun y => t.app y ≫ S.sum.map (𝟙 (F.obj y)) (k y)) ys
    rw [Category.comp_id]
    have hzip := S.zipRows_natural (fun y => 𝟙 (F.obj y)) k ys
    rw [S.foldMap_id] at hzip
    have hfold := (K.rightDist_preserves x (S.fold xs)).fold ys
    change t.app (S.fold ys) ≫ ((D.pointwise E).foldIso ys).hom =
      ((K.leftSplit (S.sum.obj x (S.fold xs))).foldIso ys).hom ≫ S.foldMap t.app ys at hfold
    calc
      _ = t.app (S.fold ys) ≫
          (S.sum.map (D.foldIso ys).hom (E.foldIso ys).hom ≫ (S.zipRows F.obj G.obj ys).hom) ≫
          S.foldMap (fun y => S.sum.map (𝟙 (F.obj y)) (k y)) ys := by
        rw [← Category.comp_id (D.foldIso ys).hom, S.sum.map_comp]
        simp only [Category.assoc]
        rw [hzip]
        simp only [Category.comp_id]
      _ = (t.app (S.fold ys) ≫ ((D.pointwise E).foldIso ys).hom) ≫
          S.foldMap (fun y => S.sum.map (𝟙 (F.obj y)) (k y)) ys := by
        rw [Split.pointwise_fold_hom]
        simp only [Category.assoc, Binary.mapIso]
      _ = _ := by rw [hfold, Category.assoc, ← S.foldMap_comp]


/-- Pointwise arrows indexed by list positions. Separate occurrences with
equal endpoint objects may carry different arrows. The list constructor
retains those arrows, including in the repeated-object case. -/
inductive Arrows : List C → List C → Type (max u v)
  | nil : Arrows [] []
  | cons : (a ⟶ b) → Arrows as bs → Arrows (a :: as) (b :: bs)

def Arrows.fold {as bs : List C} (S : Additive (C := C)) :
    Arrows as bs → (S.fold as ⟶ S.fold bs)
  | .nil => 𝟙 S.zero
  | .cons f fs => S.sum.map f (fold S fs)

def Arrows.row (T : Binary (C := C)) {a b : C} (f : a ⟶ b) {as bs : List C} :
    Arrows as bs → Arrows (as.map (T.obj a)) (bs.map (T.obj b))
  | .nil => .nil
  | .cons g gs => .cons (T.map f g) (gs.row T f)

def Arrows.rows (S : Additive (C := C)) (T : Binary (C := C))
    {as bs xs ys : List C} (cols : Arrows xs ys) :
    Arrows as bs → Arrows (as.map (fun a => S.fold (xs.map (T.obj a))))
      (bs.map (fun b => S.fold (ys.map (T.obj b))))
  | .nil => .nil
  | .cons f fs => .cons ((cols.row T f).fold S) (rows S T cols fs)

/-- Binary and nullary hom-naturality laws needed for row-first distribution.
The hypotheses state exactly the two distributor naturality squares and the
right absorber square; the left absorber naturality is already bundled. -/
structure GridNatural : Prop where
  left {a b c a' b' c' : C} (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    K.mul.map f (S.sum.map g h) ≫ ((K.leftSplit a').bin b' c').hom =
      ((K.leftSplit a).bin b c).hom ≫ S.sum.map (K.mul.map f g) (K.mul.map f h)
  right {a b c a' b' c' : C} (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    K.mul.map (S.sum.map f g) h ≫ ((K.rightDist a' b').app c').hom =
      ((K.rightDist a b).app c).hom ≫ S.sum.map (K.mul.map f h) (K.mul.map g h)
  absorbRight {a b : C} (f : a ⟶ b) :
    K.mul.map f (𝟙 S.zero) ≫ (K.leftSplit b).nil.hom = (K.leftSplit a).nil.hom

theorem GridNatural.leftFold {K : GridData S} (H : GridNatural K) {a b : C} (f : a ⟶ b)
    {xs ys : List C} (gs : Arrows xs ys) :
    K.mul.map f (gs.fold S) ≫ ((K.leftSplit b).foldIso ys).hom =
      ((K.leftSplit a).foldIso xs).hom ≫ (gs.row K.mul f).fold S := by
  induction gs with
  | nil =>
    change K.mul.map f (𝟙 S.zero) ≫ (K.leftSplit b).nil.hom =
      (K.leftSplit a).nil.hom ≫ 𝟙 S.zero
    rw [Category.comp_id, H.absorbRight]
  | cons g gs ih =>
    simp only [Arrows.fold, Arrows.row, Split.foldIso, Iso.trans_hom, Binary.mapIso, Iso.refl_hom]
    rw [← Category.assoc, H.left]
    simp only [Category.assoc, ← S.sum.map_comp, Category.id_comp, Binary.left, Category.comp_id, ih]

/-- Naturality of the row normal form in all actual pointwise input arrows.
Aggregation arrows can be taken *as* the entries, with their aggregate
source objects; there is no splitting assumption on such arrows. -/
theorem GridNatural.rows {K : GridData S} (H : GridNatural K) {as bs xs ys : List C}
    (f : Arrows as bs) (g : Arrows xs ys) :
    K.mul.map (f.fold S) (g.fold S) ≫ (K.rowExpand bs ys).hom =
      (K.rowExpand as xs).hom ≫ (Arrows.rows S K.mul g f).fold S := by
  induction f with
  | nil =>
    have h := K.absorbLeft.hom.naturality (g.fold S)
    change K.mul.map (𝟙 S.zero) (g.fold S) ≫ (K.absorbLeft.hom.app (S.fold ys)) =
      K.absorbLeft.hom.app (S.fold xs) ≫ 𝟙 S.zero
    exact h
  | cons f fs ih =>
    simp only [Arrows.fold, Arrows.rows, GridData.rowExpand, Iso.trans_hom, Binary.mapIso]
    rw [← Category.assoc, H.right]
    simp only [Category.assoc, ← S.sum.map_comp, H.leftFold, ih]


/-- Transport an addressed list of arrows through a rule on input arrows.
The rule need not be a functor, as only the selected occurrence maps occur. -/
def Arrows.mapAlong {F G : C → C} (f : ∀ {a b}, (a ⟶ b) → (F a ⟶ G b))
    {xs ys : List C} : Arrows xs ys → Arrows (xs.map F) (ys.map G)
  | .nil => .nil
  | .cons g gs => .cons (f g) (mapAlong f gs)

theorem Additive.zipRows_naturalAlong (S : Additive (C := C)) {F F' G G' : C → C}
    (f : ∀ {a b}, (a ⟶ b) → (F a ⟶ F' b))
    (g : ∀ {a b}, (a ⟶ b) → (G a ⟶ G' b)) {xs ys : List C} (h : Arrows xs ys) :
    S.sum.map ((h.mapAlong f).fold S) ((h.mapAlong g).fold S) ≫ (S.zipRows F' G' ys).hom =
      (S.zipRows F G xs).hom ≫
        (h.mapAlong (fun k => S.sum.map (f k) (g k))).fold S := by
  induction h with
  | nil =>
    change S.sum.map (𝟙 S.zero) (𝟙 S.zero) ≫ S.mergeZero.hom =
      S.mergeZero.hom ≫ 𝟙 S.zero
    rw [S.sum.map_id, Category.id_comp, Category.comp_id]
  | cons h hs ih =>
    simp only [Arrows.mapAlong, Arrows.fold, zipRows, Iso.trans_hom, Binary.mapIso, Iso.refl_hom]
    rw [← Category.assoc, S.middle_natural]
    simp only [Category.assoc, ← S.sum.map_comp, Category.id_comp, Category.comp_id, ih]

theorem Additive.zeroSplit_fold_natural (S : Additive (C := C)) {xs ys : List C} (h : Arrows xs ys) :
    (S.zeroSplit.foldIso xs).hom ≫
      (h.mapAlong (F := fun _ => S.zero) (G := fun _ => S.zero) (fun _ => 𝟙 S.zero)).fold S =
      (S.zeroSplit.foldIso ys).hom := by
  induction h with
  | nil =>
    change 𝟙 S.zero ≫ 𝟙 S.zero = 𝟙 S.zero
    simp only [Category.id_comp]
  | cons h hs ih =>
    simp only [Additive.zeroSplit, Additive.zeroFunctor] at ih
    simp only [Split.foldIso, Additive.zeroSplit, Additive.zeroFunctor, Iso.trans_hom,
      Binary.mapIso, Iso.refl_hom, Arrows.mapAlong, Arrows.fold]
    simp only [Category.assoc, ← S.sum.map_comp, Category.id_comp, ih]

def Arrows.col (T : Binary (C := C)) {a b : C} (f : a ⟶ b) {as bs : List C}
    (g : Arrows as bs) : Arrows (as.map (fun x => T.obj x a)) (bs.map (fun x => T.obj x b)) :=
  g.mapAlong (fun h => T.map h f)

def Arrows.cols (S : Additive (C := C)) (T : Binary (C := C)) {as bs xs ys : List C}
    (f : Arrows as bs) (g : Arrows xs ys) :
    Arrows (xs.map (fun x => S.fold (as.map (fun a => T.obj a x))))
      (ys.map (fun y => S.fold (bs.map (fun b => T.obj b y)))) :=
  g.mapAlong (fun h => (f.col T h).fold S)

theorem Arrows.row_eq_mapAlong (T : Binary (C := C)) {a b : C} (f : a ⟶ b) {as bs : List C}
    (g : Arrows as bs) : g.row T f = g.mapAlong (fun h => T.map f h) := by
  induction g with
  | nil => rfl
  | cons d ds ih => simp only [row, mapAlong, ih]

theorem GridData.transpose_natural {as bs xs ys : List C} (f : Arrows as bs) (g : Arrows xs ys) :
    (Arrows.rows S K.mul g f).fold S ≫ (K.transpose bs ys).hom =
      (K.transpose as xs).hom ≫ (Arrows.cols S K.mul f g).fold S := by
  induction f with
  | nil =>
    change 𝟙 S.zero ≫ (S.zeroSplit.foldIso ys).hom = (S.zeroSplit.foldIso xs).hom ≫
      (g.mapAlong (F := fun _ => S.zero) (G := fun _ => S.zero) (fun _ => 𝟙 S.zero)).fold S
    rw [Category.id_comp, S.zeroSplit_fold_natural]
  | cons f fs ih =>
    simp only [Arrows.rows, Arrows.fold, GridData.transpose, Iso.trans_hom, Binary.mapIso,
      Iso.refl_hom, Category.assoc]
    rw [← Category.assoc, ← S.sum.map_comp, ih]
    rw [Category.comp_id, ← Category.id_comp ((g.row K.mul f).fold S), S.sum.map_comp]
    simp only [Category.assoc, Arrows.row_eq_mapAlong, Arrows.cols]
    rw [S.zipRows_naturalAlong]
    rfl

/-- Full arrow naturality of the left-first column normal form, proved via
the independently constructed transpose square. -/
theorem GridNatural.cols {K : GridData S} (H : GridNatural K) {as bs xs ys : List C}
    (f : Arrows as bs) (g : Arrows xs ys) :
    K.mul.map (f.fold S) (g.fold S) ≫ K.colExpand bs ys =
      K.colExpand as xs ≫ (Arrows.cols S K.mul f g).fold S := by
  rw [← K.interchange, ← K.interchange]
  rw [← Category.assoc, H.rows, Category.assoc, K.transpose_natural, Category.assoc]


/-- An actual right-parameter arrow induces a natural transformation
between the corresponding left-varying multiplication functors. -/
def Binary.moveRight (T : Binary (C := C)) {a b : C} (q : a ⟶ b) :
    T.right a ⟶ T.right b where
  app x := T.map (𝟙 x) q
  naturality {x y} f := by
    change T.map f (𝟙 a) ≫ T.map (𝟙 y) q = T.map (𝟙 x) q ≫ T.map f (𝟙 b)
    simp only [← T.map_comp, Category.id_comp, Category.comp_id]

theorem GridData.moveRight_preserves {b c : C} (q : b ⟶ c) :
    PreservesSplit (K.rightSplit b) (K.rightSplit c) (K.mul.moveRight q) where
  bin a d := (K.rightDist a d).hom.naturality q
  nil := by
    have h := K.absorbLeft.hom.naturality q
    change (K.mul.moveRight q).app S.zero ≫ (K.rightSplit c).nil.hom =
      (K.rightSplit b).nil.hom
    exact h.trans (Category.comp_id _)

theorem GridData.moveRight_fold {b c : C} (q : b ⟶ c) (xs : List C) :
    K.mul.map (𝟙 (S.fold xs)) q ≫ ((K.rightSplit c).foldIso xs).hom =
      ((K.rightSplit b).foldIso xs).hom ≫
        S.foldMap (fun x => K.mul.map (𝟙 x) q) xs :=
  (K.moveRight_preserves q).fold xs

/-- The local interchange underlying composition of dependent accumulation.
The same continuation arrow occurs at every address in the fibre, so it
can cross the merge using bifunctoriality and distributor naturality. The
aggregate is an arbitrary arrow from the whole fibre sum; it need not
factor over a single address or into a family of components. -/
theorem GridData.constantOnFibre {a b c : C} (xs : List C)
    (aggregate : S.fold xs ⟶ a) (q : b ⟶ c) :
    (((K.rightSplit b).foldIso xs).inv ≫ K.mul.map aggregate (𝟙 b)) ≫
        K.mul.map (𝟙 a) q =
      S.foldMap (fun x => K.mul.map (𝟙 x) q) xs ≫
        ((K.rightSplit c).foldIso xs).inv ≫ K.mul.map aggregate (𝟙 c) := by
  let l := (K.rightSplit b).foldIso xs
  let r := (K.rightSplit c).foldIso xs
  have n := K.moveRight_fold q xs
  change K.mul.map (𝟙 (S.fold xs)) q ≫ r.hom =
    l.hom ≫ S.foldMap (fun x => K.mul.map (𝟙 x) q) xs at n
  have n' := congrArg (fun f => l.inv ≫ f ≫ r.inv) n
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at n'
  change (l.inv ≫ K.mul.map aggregate (𝟙 b)) ≫ K.mul.map (𝟙 a) q =
    S.foldMap (fun x => K.mul.map (𝟙 x) q) xs ≫ r.inv ≫ K.mul.map aggregate (𝟙 c)
  simpa only [Category.assoc, ← K.mul.map_comp, Category.id_comp, Category.comp_id] using
    congrArg (fun f => f ≫ K.mul.map aggregate (𝟙 c)) n'

end ContextualComposition.RigGrid
