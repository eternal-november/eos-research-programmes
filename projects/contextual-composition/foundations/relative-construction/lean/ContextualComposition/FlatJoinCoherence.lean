module
public import ContextualComposition.ContextualRigAdapter
@[expose] public section

/-! The first additive chart diamond: a flat ordered sum can be split into
three blocks in either order with the actual additive associator. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
set_option backward.isDefEq.respectTransparency false
def tailFold (xs : List C) (z : C) : C :=
  match xs with
  | [] => z
  | a::xs => a ⊗ tailFold xs z
def splitTail (xs : List C) (z : C) : tailFold xs z ⟶ tailFold xs (𝟙_ C) ⊗ z :=
  match xs with
  | [] => (λ_ z).inv
  | a::xs => (a ◁ splitTail xs z) ≫ (α_ a (tailFold xs (𝟙_ C)) z).inv

theorem tail_append_obj (xs ys : List C) (z : C) :
    tailFold xs (tailFold ys z) = tailFold (xs ++ ys) z := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [tailFold, List.cons_append, ih]

def joinTail (xs ys : List C) (z : C) :
    tailFold xs (tailFold ys z) ⟶ (tailFold xs (𝟙_ C) ⊗ tailFold ys (𝟙_ C)) ⊗ z :=
  eqToHom (tail_append_obj xs ys z) ≫ splitTail (xs ++ ys) z ≫
    (eqToHom (tail_append_obj xs ys (𝟙_ C)).symm ▷ z) ≫
    (splitTail xs (tailFold ys (𝟙_ C)) ▷ z)

private theorem tail_append_eqToHom (a : C) (xs ys : List C) (z : C) :
    eqToHom (tail_append_obj (a::xs) ys z) = a ◁ eqToHom (tail_append_obj xs ys z) := by
  apply Eq.trans _ (whiskerLeft_eqToHom a (tail_append_obj xs ys z)).symm
  congr 1

theorem joinTail_assoc (xs ys : List C) (z : C) :
    joinTail xs ys z =
      splitTail xs (tailFold ys z) ≫
        tailFold xs (𝟙_ C) ◁ splitTail ys z ≫
        (α_ (tailFold xs (𝟙_ C)) (tailFold ys (𝟙_ C)) z).inv := by
  induction xs with
  | nil =>
    simp only [joinTail, splitTail, tailFold, List.nil_append, Category.id_comp, eqToHom_refl,
      id_whiskerRight]
    rw [← leftUnitor_inv_naturality_assoc]
    monoidal
  | cons a xs ih =>
    simp only [joinTail, tail_append_eqToHom, splitTail, tailFold, List.cons_append] at ih ⊢
    have he : eqToHom (tail_append_obj (a::xs) ys (𝟙_ C)).symm = a ◁ eqToHom (tail_append_obj xs ys (𝟙_ C)).symm := by
      rw [whiskerLeft_eqToHom]
    rw [he]
    calc
      _ = (a ◁ (eqToHom (tail_append_obj xs ys z) ≫ splitTail (xs ++ ys) z ≫
        eqToHom (tail_append_obj xs ys (𝟙_ C)).symm ▷ z ≫ splitTail xs (tailFold ys (𝟙_ C)) ▷ z)) ≫
        (α_ a (tailFold xs (𝟙_ C) ⊗ tailFold ys (𝟙_ C)) z).inv ≫
        (α_ a (tailFold xs (𝟙_ C)) (tailFold ys (𝟙_ C))).inv ▷ z := by monoidal
      _ = _ := by rw [ih]; monoidal

section Cross
variable [BraidedCategory C]
def crossHead (a b z : C) : a ⊗ (b ⊗ z) ⟶ b ⊗ (a ⊗ z) :=
  (α_ a b z).inv ≫ (β_ a b).hom ▷ z ≫ (α_ b a z).hom
theorem crossHead_nat (a b : C) {z z' : C} (f : z ⟶ z') :
    crossHead a b z ≫ b ◁ a ◁ f = (a ◁ b ◁ f) ≫ crossHead a b z' := by
  unfold crossHead
  simp only [Category.assoc]
  rw [← associator_naturality_right, ← whisker_exchange_assoc, ← associator_inv_naturality_right_assoc]
def extract (a : C) (xs : List C) (z : C) : tailFold xs (a ⊗ z) ⟶ a ⊗ tailFold xs z :=
  match xs with
  | [] => 𝟙 _
  | b::bs => (b ◁ extract a bs z) ≫ crossHead b a (tailFold bs z)
theorem extract_block (a : C) (xs : List C) (z : C) :
    extract a xs z ≫ a ◁ splitTail xs z =
      splitTail xs (a ⊗ z) ≫ crossHead (tailFold xs (𝟙_ C)) a z := by
  induction xs with
  | nil =>
    simp only [extract, splitTail, Category.id_comp, tailFold, crossHead, braiding_tensorUnit_left]
    monoidal
  | cons b bs ih =>
    simp only [extract, splitTail, tailFold, crossHead, Category.assoc]
    have aux := congrArg (fun h => b ◁ h) ih
    rw [braiding_tensor_left_hom]
    simp only [crossHead] at aux
    calc
      _ = (b ◁ (extract a bs z ≫ a ◁ splitTail bs z)) ≫
        crossHead b a (tailFold bs (𝟙_ C) ⊗ z) ≫
        a ◁ (α_ b (tailFold bs (𝟙_ C)) z).inv := by
          have move := crossHead_nat b a (splitTail bs z)
          unfold crossHead at move ⊢
          have pasted := congrArg (fun t => b ◁ extract a bs z ≫ t ≫ a ◁ (α_ b (tailFold bs (𝟙_ C)) z).inv) move
          simpa only [whiskerLeft_comp, Category.assoc] using pasted
      _ = _ := by rw [aux]; unfold crossHead; monoidal

def swapBlocks (xs ys : List C) (z : C) : tailFold xs (tailFold ys z) ⟶ tailFold ys (tailFold xs z) :=
  match ys with
  | [] => 𝟙 _
  | b::bs => extract b xs (tailFold bs z) ≫ b ◁ swapBlocks xs bs z
def separateBlocks (xs ys : List C) (z : C) :
    tailFold xs (tailFold ys z) ⟶ (tailFold xs (𝟙_ C) ⊗ tailFold ys (𝟙_ C)) ⊗ z :=
  splitTail xs (tailFold ys z) ≫ tailFold xs (𝟙_ C) ◁ splitTail ys z ≫
    (α_ (tailFold xs (𝟙_ C)) (tailFold ys (𝟙_ C)) z).inv
theorem swapBlocks_grouped (xs ys : List C) (z : C) :
    swapBlocks xs ys z ≫ separateBlocks ys xs z =
      separateBlocks xs ys z ≫ (β_ (tailFold xs (𝟙_ C)) (tailFold ys (𝟙_ C))).hom ▷ z := by
  induction ys with
  | nil =>
    simp only [swapBlocks, separateBlocks, splitTail, tailFold, Category.id_comp, braiding_tensorUnit_right]
    monoidal
  | cons y ys ih =>
    let A := tailFold xs (𝟙_ C)
    let B := tailFold ys (𝟙_ C)
    let F := tailFold ys z
    have exh := extract_block y xs F
    have wh := congrArg (fun f => y ◁ f) ih
    simp only [swapBlocks, separateBlocks, splitTail, tailFold, Category.assoc]
    rw [braiding_tensor_right_hom]
    calc
      _ = extract y xs F ≫ (y ◁ (swapBlocks xs ys z ≫ separateBlocks ys xs z)) ≫
          (α_ y (B ⊗ A) z).inv ≫ (α_ y B A).inv ▷ z := by dsimp [separateBlocks, A, B, F]; monoidal
      _ = _ := by
        rw [wh]
        simp only [separateBlocks, whiskerLeft_comp, Category.assoc]
        rw [← Category.assoc (extract y xs F), exh]
        simp only [Category.assoc]
        rw [← Category.assoc (crossHead A y F), crossHead_nat]
        unfold crossHead A B F
        monoidal
end Cross

def tailMap (xs : List C) {u v : C} (f : u ⟶ v) : tailFold xs u ⟶ tailFold xs v :=
  match xs with
  | [] => f
  | a::xs => a ◁ tailMap xs f
theorem splitTail_map (xs : List C) {u v : C} (f : u ⟶ v) :
    tailMap xs f ≫ splitTail xs v = splitTail xs u ≫ tailFold xs (𝟙_ C) ◁ f := by
  induction xs with
  | nil =>
    exact leftUnitor_inv_naturality f
  | cons x xs ih =>
    simp only [tailMap, splitTail, tailFold]
    calc
      _ = (x ◁ (tailMap xs f ≫ splitTail xs v)) ≫
        (α_ x (tailFold xs (𝟙_ C)) v).inv := by monoidal
      _ = _ := by rw [ih]; monoidal

section Four
variable [BraidedCategory C]
def fourGroup (as bs cs ds : List C) (z : C) :
    tailFold as (tailFold bs (tailFold cs (tailFold ds z))) ⟶
      ((tailFold as (𝟙_ C) ⊗ tailFold bs (𝟙_ C)) ⊗ (tailFold cs (𝟙_ C) ⊗ tailFold ds (𝟙_ C))) ⊗ z :=
  separateBlocks as bs (tailFold cs (tailFold ds z)) ≫
    (tailFold as (𝟙_ C) ⊗ tailFold bs (𝟙_ C)) ◁ separateBlocks cs ds z ≫
    (α_ (tailFold as (𝟙_ C) ⊗ tailFold bs (𝟙_ C)) (tailFold cs (𝟙_ C) ⊗ tailFold ds (𝟙_ C)) z).inv
def packFour (a b c d z : C) :
    a ⊗ ((b ⊗ c) ⊗ (d ⊗ z)) ⟶ ((a ⊗ b) ⊗ (c ⊗ d)) ⊗ z :=
  a ◁ (α_ b c (d ⊗ z)).hom ≫ (α_ a b (c ⊗ (d ⊗ z))).inv ≫
    (a ⊗ b) ◁ (α_ c d z).inv ≫ (α_ (a ⊗ b) (c ⊗ d) z).inv
omit [BraidedCategory C] in
theorem fourGroup_asMiddle (as bs cs ds : List C) (z : C) :
    fourGroup as bs cs ds z =
    splitTail as (tailFold bs (tailFold cs (tailFold ds z))) ≫
      tailFold as (𝟙_ C) ◁ separateBlocks bs cs (tailFold ds z) ≫
      tailFold as (𝟙_ C) ◁ (tailFold bs (𝟙_ C) ⊗ tailFold cs (𝟙_ C)) ◁ splitTail ds z ≫
      packFour (tailFold as (𝟙_ C)) (tailFold bs (𝟙_ C)) (tailFold cs (𝟙_ C)) (tailFold ds (𝟙_ C)) z := by
  unfold fourGroup separateBlocks packFour
  monoidal
theorem packFour_braid (a b c d z : C) :
    (a ◁ ((β_ b c).hom ▷ (d ⊗ z))) ≫ packFour a c b d z =
      packFour a b c d z ≫ tensorμ a b c d ▷ z := by
  unfold packFour tensorμ
  monoidal
/-- A literal exchange of the two middle flat lists, before the four
summands have been gathered. Compare with gathering first and applying
the actual additive middle-four on the four whole blocks. -/
theorem flat_middle (as bs cs ds : List C) (z : C) :
    tailMap as (swapBlocks bs cs (tailFold ds z)) ≫ fourGroup as cs bs ds z =
      fourGroup as bs cs ds z ≫
        tensorμ (tailFold as (𝟙_ C)) (tailFold bs (𝟙_ C)) (tailFold cs (𝟙_ C)) (tailFold ds (𝟙_ C)) ▷ z := by
  let A := tailFold as (𝟙_ C)
  let B := tailFold bs (𝟙_ C)
  let D := tailFold cs (𝟙_ C)
  let E := tailFold ds (𝟙_ C)
  let t := tailFold ds z
  rw [fourGroup_asMiddle, fourGroup_asMiddle]
  simp only [Category.assoc]
  rw [← Category.assoc (tailMap as _), splitTail_map, Category.assoc]
  rw [← Category.assoc (A ◁ swapBlocks bs cs t), ← whiskerLeft_comp, swapBlocks_grouped]
  simp only [whiskerLeft_comp, Category.assoc]
  have e := congrArg (fun f => A ◁ f) (whisker_exchange (β_ B D).hom (splitTail ds z)).symm
  simp only [whiskerLeft_comp] at e
  rw [← Category.assoc (A ◁ (β_ B D).hom ▷ t), e, Category.assoc]
  rw [packFour_braid]
end Four

section Expression
variable {I : Type u} (A : I → C)
abbrev word (e : GridExpr I) := e.leaves.map A
abbrev E (e : GridExpr I) := GridExpr.eval (S:=binary (Binary.ofMonoidal (C:=C))) (Z:=𝟙_ C) A e
theorem nestedFlat (e f : GridExpr I) (z : C) :
    tailFold (word A (GridExpr.bin e f)) z = tailFold (word A e) (tailFold (word A f) z) := by
  simp only [word, GridExpr.leaves, List.map_append, tail_append_obj]
def compressTree : (e : GridExpr I) → tailFold (word A e) (𝟙_ C) ⟶ E A e
  | .zero => 𝟙 _
  | .leaf i => (ρ_ (A i)).hom
  | .bin e f => eqToHom (nestedFlat A e f (𝟙_ C)) ≫
      splitTail (word A e) (tailFold (word A f) (𝟙_ C)) ≫
      (compressTree e ⊗ₘ compressTree f)
def withTail (e : GridExpr I) (z : C) : tailFold (word A e) z ⟶ E A e ⊗ z :=
  splitTail (word A e) z ≫ compressTree A e ▷ z
theorem withTail_zero (z : C) :
    withTail A GridExpr.zero z = (λ_ z).inv := by
  simp only [withTail, compressTree, id_whiskerRight, Category.comp_id]
  rfl
theorem withTail_bin (e f : GridExpr I) (z : C) :
    eqToHom (nestedFlat A e f z).symm ≫ withTail A (.bin e f) z =
      withTail A e (tailFold (word A f) z) ≫
        E A e ◁ withTail A f z ≫ (α_ (E A e) (E A f) z).inv := by
  let as := word A e
  let bs := word A f
  have square (cs : List C) (h : cs = as ++ bs)
      (p : tailFold cs z = tailFold as (tailFold bs z))
      (q : tailFold cs (𝟙_ C) = tailFold as (tailFold bs (𝟙_ C))) :
      eqToHom p.symm ≫ splitTail cs z ≫ eqToHom q ▷ z ≫
        splitTail as (tailFold bs (𝟙_ C)) ▷ z =
        separateBlocks as bs z := by
    subst cs
    have hp : p = (tail_append_obj as bs z).symm := Subsingleton.elim _ _
    have hq : q = (tail_append_obj as bs (𝟙_ C)).symm := Subsingleton.elim _ _
    rw [hp,hq]
    exact joinTail_assoc as bs z
  have reform := square (word A (.bin e f)) (List.map_append ..)
    (nestedFlat A e f z) (nestedFlat A e f (𝟙_ C))
  simp only [withTail, compressTree, Category.assoc, comp_whiskerRight]
  calc
    _ = separateBlocks as bs z ≫ (compressTree A e ⊗ₘ compressTree A f) ▷ z := by
      rw [← reform]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      unfold separateBlocks as bs
      rw [tensorHom_def]
      calc
        _ = splitTail (word A e) (tailFold (word A f) z) ≫
          tailFold (word A e) (𝟙_ C) ◁ splitTail (word A f) z ≫
          compressTree A e ▷ (tailFold (word A f) (𝟙_ C) ⊗ z) ≫
          E A e ◁ (compressTree A f ▷ z) ≫ (α_ (E A e) (E A f) z).inv := by monoidal
        _ = _ := by rw [whisker_exchange_assoc]; monoidal

theorem withTail_map (e : GridExpr I) {z z' : C} (p : z ⟶ z') :
    tailMap (word A e) p ≫ withTail A e z' =
      withTail A e z ≫ E A e ◁ p := by
  unfold withTail
  rw [← Category.assoc, splitTail_map, Category.assoc, whisker_exchange, Category.assoc]

section FourTrees
variable [BraidedCategory C]
def alignFour (e f g h : GridExpr I) (z : C) :
    tailFold (word A e) (tailFold (word A f) (tailFold (word A g) (tailFold (word A h) z))) ⟶
      tailFold (word A (.bin (.bin e f) (.bin g h))) z :=
  tailMap (word A e) (tailMap (word A f) (eqToHom (nestedFlat A g h z).symm)) ≫
      eqToHom (nestedFlat A e f (tailFold (word A (.bin g h)) z)).symm ≫
      eqToHom (nestedFlat A (.bin e f) (.bin g h) z).symm

omit [BraidedCategory C] in
theorem withTail_pair_factor (e f : GridExpr I) (z : C) :
    withTail A e (tailFold (word A f) z) ≫
      E A e ◁ withTail A f z ≫ (α_ (E A e) (E A f) z).inv =
    separateBlocks (word A e) (word A f) z ≫ (compressTree A e ⊗ₘ compressTree A f) ▷ z := by
  symm
  unfold separateBlocks withTail
  rw [tensorHom_def]
  calc
    _ = splitTail (word A e) (tailFold (word A f) z) ≫
      tailFold (word A e) (𝟙_ C) ◁ splitTail (word A f) z ≫
      compressTree A e ▷ (tailFold (word A f) (𝟙_ C) ⊗ z) ≫
      E A e ◁ (compressTree A f ▷ z) ≫ (α_ (E A e) (E A f) z).inv := by monoidal
    _ = _ := by rw [whisker_exchange_assoc]; monoidal

omit [BraidedCategory C] in
theorem withTail_four (e f g h : GridExpr I) (z : C) :
    alignFour A e f g h z ≫ withTail A (.bin (.bin e f) (.bin g h)) z =
      fourGroup (word A e) (word A f) (word A g) (word A h) z ≫
        ((compressTree A e ⊗ₘ compressTree A f) ⊗ₘ (compressTree A g ⊗ₘ compressTree A h)) ▷ z := by
  unfold alignFour
  simp only [Category.assoc]
  rw [withTail_bin]
  rw [← Category.assoc (eqToHom _), withTail_bin]
  simp only [Category.assoc]
  rw [← Category.assoc (tailMap _ _), withTail_map]
  simp only [Category.assoc]
  rw [← Category.assoc (E A e ◁ tailMap _ _), ← whiskerLeft_comp, withTail_map]
  let z' := tailFold (word A g) (tailFold (word A h) z)
  calc
    _ = withTail A e (tailFold (word A f) z') ≫
      E A e ◁ withTail A f z' ≫ (α_ (E A e) (E A f) z').inv ≫
      (E A e ⊗ E A f) ◁ (eqToHom (nestedFlat A g h z).symm ≫ withTail A (.bin g h) z) ≫
      (α_ (E A e ⊗ E A f) (E A g ⊗ E A h) z).inv := by
        dsimp [z']
        monoidal
    _ = _ := by
      rw [withTail_bin, withTail_pair_factor]
      have fact := withTail_pair_factor A e f z'
      rw [← Category.assoc (withTail A e _), ← Category.assoc (withTail A e _ ≫ _), Category.assoc (withTail A e _) (E A e ◁ withTail A f z'), fact]
      unfold fourGroup
      simp only [Category.assoc, whiskerLeft_comp]
      rw [← whisker_exchange_assoc (compressTree A e ⊗ₘ compressTree A f)]
      rw [tensorHom_def (compressTree A e ⊗ₘ compressTree A f) (compressTree A g ⊗ₘ compressTree A h)]
      monoidal

/-- A flat route computed by raw middle-block exchange, with the target
tree grouped by its own map. It does not obtain that chart by applying
the original tree-level braid. -/
theorem chart_middle_flat (e f g h : GridExpr I) (z : C) :
    tailMap (word A e) (swapBlocks (word A f) (word A g) (tailFold (word A h) z)) ≫
      alignFour A e g f h z ≫ withTail A (.bin (.bin e g) (.bin f h)) z =
    alignFour A e f g h z ≫ withTail A (.bin (.bin e f) (.bin g h)) z ≫
      tensorμ (E A e) (E A f) (E A g) (E A h) ▷ z := by
  rw [withTail_four, ← Category.assoc (alignFour A e f g h z), withTail_four]
  rw [← Category.assoc (tailMap _ _), flat_middle]
  simp only [Category.assoc]
  rw [← comp_whiskerRight, ← comp_whiskerRight]
  rw [tensorμ_natural]
end FourTrees
end Expression

section Circuit
variable [SymmetricCategory C] {I : Type u} (A : I → C)
omit [SymmetricCategory C] in
theorem tailMap_eqToHom (xs : List C) {a b : C} (e : a = b) :
    tailMap xs (eqToHom e) = eqToHom (congrArg (tailFold xs) e) := by
  subst b
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [tailMap, eqToHom_refl] at ih ⊢; rw [ih, whiskerLeft_id]; rfl
instance alignFour_isIso (e f g h : GridExpr I) (z : C) : IsIso (alignFour A e f g h z) := by
  unfold alignFour
  rw [tailMap_eqToHom, tailMap_eqToHom]
  infer_instance

noncomputable def flatCircuit {e f : GridExpr I} (p : GridCircuit I e f) (z : C) :
    tailFold (word A e) z ⟶ tailFold (word A f) z :=
  match p with
  | .ident _ => 𝟙 _
  | .seq p q => flatCircuit p z ≫ flatCircuit q z
  | .bin (a:=e) (b:=f) (c:=g) (d:=h) p q =>
    eqToHom (nestedFlat A e f z) ≫ flatCircuit p (tailFold (word A f) z) ≫
      tailMap (word A g) (flatCircuit q z) ≫ eqToHom (nestedFlat A g h z).symm
  | .dupZero => 𝟙 _
  | .mergeZero => 𝟙 _
  | .middle e f g h =>
    inv (alignFour A e f g h z) ≫
      tailMap (word A e) (swapBlocks (word A f) (word A g) (tailFold (word A h) z)) ≫
      alignFour A e g f h z

/-- The standard additive model uses the coherent braided middle-four
and its actual unitors. The flat circuit is computed independently from
the syntax by skipping syntactic zeros, concatenating contiguous lists,
and moving the central block by repeated adjacent crossings. -/
theorem flatCircuit_correct {e f : GridExpr I} (p : GridCircuit I e f) (z : C) :
    flatCircuit A p z ≫ withTail A f z =
      withTail A e z ≫ (GridCircuit.eval (symmetricCross (C:=C)) A p) ▷ z := by
  induction p generalizing z with
  | ident e =>
    simp only [flatCircuit, GridCircuit.eval, coeff, id_whiskerRight, Category.id_comp, Category.comp_id]
  | seq p q hp hq =>
    simp only [flatCircuit, GridCircuit.eval, coeff, comp_whiskerRight, Category.assoc]
    rw [hq, ← Category.assoc (flatCircuit _ _ _), hp]
    simp only [Category.assoc]
  | dupZero =>
    simp only [flatCircuit, Category.id_comp]
    change withTail A (.bin .zero .zero) z = withTail A .zero z ≫ (λ_ (𝟙_ C)).inv ▷ z
    have h := withTail_bin A .zero .zero z
    change 𝟙 z ≫ withTail A (.bin .zero .zero) z = _ at h
    rw [Category.id_comp, withTail_zero, withTail_zero] at h
    rw [h, withTail_zero]
    monoidal
  | mergeZero =>
    simp only [flatCircuit, Category.id_comp]
    change withTail A .zero z = withTail A (.bin .zero .zero) z ≫ (λ_ (𝟙_ C)).hom ▷ z
    have h := withTail_bin A .zero .zero z
    change 𝟙 z ≫ withTail A (.bin .zero .zero) z = _ at h
    rw [Category.id_comp, withTail_zero, withTail_zero] at h
    rw [h, withTail_zero]
    monoidal
  | middle e f g h =>
    simp only [flatCircuit, GridCircuit.eval, Additive.ofBraided, Category.assoc]
    rw [chart_middle_flat]
    simp only [← Category.assoc]
    rw [IsIso.inv_hom_id, Category.id_comp]
  | @bin e f g h p q ihp ihq =>
    simp only [flatCircuit, GridCircuit.eval, binary, Category.assoc]
    rw [withTail_bin]
    rw [← Category.assoc (tailMap _ _), withTail_map]
    simp only [Category.assoc]
    rw [← Category.assoc (flatCircuit A p _), ihp]
    simp only [Category.assoc]
    rw [← Category.assoc ((E A g) ◁ (flatCircuit A q z)), ← whiskerLeft_comp, ihq]
    simp only [whiskerLeft_comp, Category.assoc]
    let r := GridCircuit.eval (symmetricCross (C:=C)) A p
    let s := GridCircuit.eval (symmetricCross (C:=C)) A q
    change _ = withTail A (.bin e f) z ≫ (r ⊗ₘ s) ▷ z
    calc
      _ = eqToHom (nestedFlat A e f z) ≫
        (withTail A e (tailFold (word A f) z) ≫ E A e ◁ withTail A f z ≫
          (α_ (E A e) (E A f) z).inv) ≫ (r ⊗ₘ s) ▷ z := by
          rw [← whisker_exchange_assoc r (withTail A f z), tensorHom_def r s]
          monoidal
      _ = _ := by
        rw [← withTail_bin]
        simp

omit [SymmetricCategory C] in
theorem splitTail_unit (xs : List C) : splitTail xs (𝟙_ C) = (ρ_ (tailFold xs (𝟙_ C))).inv := by
  induction xs with
  | nil =>
    change (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv
    monoidal
  | cons x xs ih =>
    simp only [splitTail, ih, tailFold]
    monoidal
omit [SymmetricCategory C] in
theorem withTail_unit (e : GridExpr I) :
    withTail A e (𝟙_ C) = compressTree A e ≫ (ρ_ (E A e)).inv := by
  unfold withTail
  rw [splitTail_unit]
  monoidal

/-- General additive chart coherence for the raw order implemented by an
actual structural circuit. The two grouping maps are independently
computed from their own tree, with no assumption of circuit equality. -/
theorem independent_std_charts {e f : GridExpr I} (p : GridCircuit I e f) :
    flatCircuit A p (𝟙_ C) ≫ compressTree A f =
      compressTree A e ≫ GridCircuit.eval (symmetricCross (C:=C)) A p := by
  apply (cancel_mono (ρ_ (E A f)).inv).mp
  have h := flatCircuit_correct A p (𝟙_ C)
  rw [withTail_unit, withTail_unit] at h
  calc
    _ = flatCircuit A p (𝟙_ C) ≫ (compressTree A f ≫ (ρ_ (E A f)).inv) := Category.assoc ..
    _ = _ := by
      rw [h]
      monoidal
end Circuit

section Ragged
variable [SymmetricCategory C]
local notation "𝒮" => binary Binary.ofMonoidal
variable {T : Bi (coeff (C:=C))}
variable (R : Gather 𝒮 T (𝟙_ C)) (L : LeftGather 𝒮 T (𝟙_ C))
variable (F : Lin 𝒮 (𝟙_ C)) (h : AdditiveContextLaws F)
variable {X Y B : Type u} (V : X → C) (A : Y → B → C) (bs : Y → List B)
variable (xs : List X) (ys : List Y)
variable (D : GridBinary (symmetricCross (C:=C)) R L)
variable {q : C}
variable (β : T.obj (fold 𝒮 (𝟙_ C) V xs) (fold 𝒮 (𝟙_ C) (fun y => fold 𝒮 (𝟙_ C) (A y) (bs y)) ys) ⟶ q)

include h D in
/-- In a standard rig the column's grouping map is now independent
of the row's. The entry route from the raw flat word swaps the addressed
blocks before the column is grouped, rather than defining the column chart
by pasting the tree transpose onto the row chart. -/
theorem ragged_std_independent_flat :
    flatCircuit (fun i => F.obj (labels (T:=T) V A i)) (chartC bs xs ys) (𝟙_ C) ≫
      compressTree (fun i => F.obj (labels (T:=T) V A i)) (colTree bs xs ys) ≫
      GridExpr.gatherE F (labels (T:=T) V A) (colTree bs xs ys) ≫
      F.map (transportSource (eval_col_tree (S:=𝒮) (Z:=𝟙_ C) (T:=T) V A bs xs ys)
        (raggedColGather R L V xs ys bs A ≫ β)) =
    compressTree (fun i => F.obj (labels (T:=T) V A i)) (rowTree bs xs ys) ≫
      GridExpr.gatherE F (labels (T:=T) V A) (rowTree bs xs ys) ≫
      F.map (transportSource (eval_row_tree (S:=𝒮) (Z:=𝟙_ C) (T:=T) V A bs xs ys)
        (raggedRowGather R L V xs ys bs A ≫ β)) := by
  rw [← Category.assoc (flatCircuit _ _ _), independent_std_charts, Category.assoc]
  have step := actual_ragged_context (symmetricCross (C:=C)) F h.natural
    (actual_context_cross F h) R L V A bs xs ys D β
  exact congrArg (fun g => compressTree (fun i => F.obj (labels (T:=T) V A i)) (rowTree bs xs ys) ≫ g) step
end Ragged
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
