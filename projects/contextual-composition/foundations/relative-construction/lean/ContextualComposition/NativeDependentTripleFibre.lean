module
public import ContextualComposition.NativeDependentTripleInput
@[expose] public section

/-! A common final-fibre index for the two independently constructed
ternary native maps. Every target-bound cell retains its membership proofs. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {X Y W X' Y' W' : Type u} [DecidableEq X'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : X → List Y} {ws : X → Y → List W}
variable {xs' : List X'} {ys' : X' → List Y'} {ws' : X' → Y' → List W'}
variable {V : X → C} {B : X → Y → C} {D : X → Y → W → C}
variable {V' : X' → C} {B' : X' → Y' → C} {D' : X' → Y' → W' → C}
variable (F : OrderedDependentMap xs ys xs' ys' V B V' B')
variable (G : OrderedThirdMap F ws ws' D D')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
theorem taggedRaggedRows_childRead {X K : Type u} {Y Z : X → Type u}
    (A : K → C) (f : ∀ x, Z x → K) (read : ∀ x, Y x → Z x)
    (ls : ∀ x, List (Y x)) (ms : ∀ x, List (Z x))
    (h : ∀ x, (ls x).map (read x) = ms x) (xs : List X) :
    let F := fold 𝒮 Zₐ A
    let _cs := fun x => congrArg F ((congrArg (List.map (f x)) (h x).symm).trans List.map_map)
    let d := fun x => (congrArg (fold 𝒮 Zₐ (A ∘ f x)) (h x).symm).trans
      (std_fold_map (A ∘ f x) (read x) (ls x))
    let e := congrArg F (congrArg (fun z => xs.flatMap z)
      (funext fun x => (congrArg (List.map (f x)) (h x).symm).trans List.map_map))
    (rowsChart A (fun x => (ms x).map (f x)) xs ≫
      act 𝒮 Zₐ (fun x => eqToHom (std_fold_map A (f x) (ms x))) xs) ≫
      act 𝒮 Zₐ (fun x => eqToHom (d x)) xs =
      eqToHom e ≫ rowsChart A (fun x => (ls x).map (f x ∘ read x)) xs ≫
        act 𝒮 Zₐ (fun x => eqToHom (std_fold_map A (f x ∘ read x) (ls x))) xs := by
  intro F cs d e
  let s := fun x => eqToHom (std_fold_map A (f x) (ms x))
  let t := fun x => eqToHom (d x)
  let q := fun x => eqToHom (cs x)
  let u := fun x => eqToHom (std_fold_map A (f x ∘ read x) (ls x))
  have hh (x : X) : s x ≫ t x = q x ≫ u x := by
    unfold s t q u
    rw [eqToHom_trans, eqToHom_trans]
  have H : act 𝒮 Zₐ s xs ≫ act 𝒮 Zₐ t xs = act 𝒮 Zₐ q xs ≫ act 𝒮 Zₐ u xs :=
    (act_seq 𝒮 Zₐ s t xs).trans ((congrArg (fun f => act 𝒮 Zₐ f xs) (funext hh)).trans (act_seq 𝒮 Zₐ q u xs).symm)
  simp only [Category.assoc]
  rw [H]
  rw [reassoc_of% rowsChart_rows_congr A (fun x => (congrArg (List.map (f x)) (h x).symm).trans List.map_map) xs]

namespace OrderedThirdMap

abbrev TripleMid {a : X'} (x : F.Slice a) (b : Y') :=
  (G.tailInput F x.val x.property.1).Slice b

def tripleMidWord {a : X'} (x : F.Slice a) (b : Y') :
    List (G.TripleMid F x b) :=
  (G.tailInput F x.val x.property.1).slice b

def tripleMidRead {a : X'} {b : Y'} (x : F.Slice a) (y : G.TripleMid F x b) :
    (G.leftInput F R L).Slice (a,b) :=
  ⟨(x.val,y.val), (dependentWord_mem xs ys _).mpr ⟨x.property.1,y.property.1⟩,
    Prod.ext x.property.2 y.property.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem tripleMidRead_word (a : X') (b : Y') :
    (F.slice a).flatMap (fun x => (G.tripleMidWord F x b).map (G.tripleMidRead F R L x)) =
      (G.leftInput F R L).slice (a,b) := by
  let p := G.leftInput F R L
  let h := fun (x : F.Slice a) => (G.tripleMidWord F x b).map (G.tripleMidRead F R L x)
  apply (List.map_inj_right (f:=Subtype.val) (fun _ _ e => Subtype.ext e)).mp
  rw [sliceWord_map, List.map_flatMap]
  have e (x : F.Slice a) :
      (h x).map Subtype.val = (F.terms a b x).map (Prod.mk x.val) := by
    unfold h tripleMidWord
    rw [List.map_map]
    change (sliceWord (ys x.val) (F.child x.val) b).map (fun y => (x.val,y.val)) = _
    exact (List.map_map (l:=sliceWord (ys x.val) (F.child x.val) b)).symm.trans
      (congrArg (List.map (Prod.mk x.val)) (sliceWord_map (ys x.val) (F.child x.val) b))
  have k := origDepCarrier_fibre F (a,b)
  change parentFibreA _ p.parent (a,b) = _ at k
  rw [k]
  change (F.slice a).flatMap (fun y => (h y).map Subtype.val) =
    (parentFibreA xs F.parent a).flatMap (fun x => (childFibreA ys F.child b x).map (Prod.mk x))
  rw [show (fun x => (h x).map Subtype.val) = _ from funext e, ← sliceWord_map xs F.parent a,
    List.flatMap_map]
  rfl

theorem tripleMid_leaf_word (a : X') (b : Y') (d : W') (x : F.Slice a) (y : G.TripleMid F x b) :
    (G.leftInput F R L).terms (a,b) d (G.tripleMidRead F R L x y) =
      (G.tailInput F x.val x.property.1).terms b d y := rfl

theorem rightTerms_dependent (a : X') (b : Y') (d : W') (x : F.Slice a) :
    (G.rightInput F R L).terms a (b,d) x =
      dependentWord (F.terms a b x) (fun y => wordFibre (ws x.val y) (G.leaf x.val y) d) :=
  origDepCarrier_fibre (G.tailInput F x.val x.property.1) (b,d)

set_option backward.isDefEq.respectTransparency false in
theorem leftLeaf_matches_rightTail {a : X'} {b : Y'} (d : W') (x : F.Slice a)
    (y : G.TripleMid F x b) (h : d ∈ ws' a b) :
    let k := G.tailInput F x.val x.property.1
    let h' : d ∈ ws' (F.parent x.val) b := x.property.2.symm ▸ h
    HEq ((G.leftInput F R L).innerSliceCell (G.tripleMidRead F R L x y) d h)
      (k.innerSliceCell y d h') := by
  rcases x with ⟨x,hx,ex⟩
  change F.parent x = a at ex
  subst a
  rcases y with ⟨y,hy,ey⟩
  change F.child x y = b at ey
  subst b
  intro k h'
  let p := G.leftInput F R L
  let t := (x,y)
  let ht : t ∈ dependentWord xs ys := (dependentWord_mem xs ys t).mpr ⟨hx,hy⟩
  have l := p.innerSliceCell_eq_raw t ht d h
  have r := k.innerSliceCell_eq_raw y hy d h'
  change HEq (p.innerSliceCell (⟨t,ht,rfl⟩ : p.Slice (p.parent t)) d h)
    (k.innerSliceCell (⟨y,hy,rfl⟩ : k.Slice (k.parent y)) d h')
  rw [l,r]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem rightInnerSlice_heq {a : X'} (b : Y') (d : W') (x : F.Slice a)
    (hb : b ∈ ys' a) (hd : d ∈ ws' a b) :
    let k := G.tailInput F x.val x.property.1
    let m : (b,d) ∈ dependentWord (ys' (F.parent x.val)) (ws' (F.parent x.val)) :=
      x.property.2.symm ▸ (dependentWord_mem (ys' a) (ws' a) (b,d)).mpr ⟨hb,hd⟩
    HEq ((G.rightInput F R L).innerSliceCell x (b,d)
      ((dependentWord_mem (ys' a) (ws' a) (b,d)).mpr ⟨hb,hd⟩)) (origDependentCell k R L (b,d) m) := by
  rcases x with ⟨x,hx,ex⟩
  change F.parent x = a at ex
  subst a
  intro k m
  let p := G.rightInput F R L
  change HEq (p.innerSliceCell (⟨x,hx,rfl⟩ : p.Slice (p.parent x)) (b,d) m) _
  rw [p.innerSliceCell_eq_raw x hx (b,d) m]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem tailLocOuter_heq {a : X'} (b : Y') (x : F.Slice a) (hb : b ∈ ys' a) :
    let k := G.tailInput F x.val x.property.1
    let h : b ∈ ys' (F.parent x.val) := x.property.2.symm ▸ hb
    HEq (k.locOuter b h) (F.innerSliceCell x b hb) := by
  rcases x with ⟨x,hx,ex⟩
  change F.parent x = a at ex
  subst a
  intro k h
  have e := F.innerSliceCell_eq_raw x hx b hb
  change HEq (k.locOuter b h) (F.innerSliceCell (⟨x,hx,rfl⟩ : F.Slice (F.parent x)) b hb)
  rw [e]
  exact k.locOuter_heq_raw b h

section TailCells
variable {a : X'} (b : Y') (d : W') (x : F.Slice a)
variable (hb : b ∈ ys' a) (hd : d ∈ ws' a b)

def tripleMidBeta :
    fold 𝒮 Zₐ (fun y : G.TripleMid F x b => B x.val y.val) (G.tripleMidWord F x b) ⟶ B' a b :=
  let r := (std_fold_map (B x.val) Subtype.val (G.tripleMidWord F x b)).symm.trans
    (congrArg (fold 𝒮 Zₐ (B x.val)) (sliceWord_map (ys x.val) (F.child x.val) b))
  eqToHom r ≫ F.innerSliceCell x b hb

def tripleMidGamma (y : G.TripleMid F x b) :
    fold 𝒮 Zₐ (D x.val y.val) ((G.tailInput F x.val x.property.1).terms b d y) ⟶ D' a b d :=
  (G.leftInput F R L).innerSliceCell (G.tripleMidRead F R L x y) d hd

set_option backward.isDefEq.respectTransparency false in
theorem tripleMidBeta_tail :
    let p := G.tailInput F x.val x.property.1
    let h : b ∈ ys' (F.parent x.val) := x.property.2.symm ▸ hb
    HEq (G.tripleMidBeta F b x hb) (p.locOuter b h) :=
  (hom_source_pin_heq _ _).trans (G.tailLocOuter_heq F b x hb).symm

set_option backward.isDefEq.respectTransparency false in
theorem tripleMidGamma_tail (y : G.TripleMid F x b) :
    let p := G.tailInput F x.val x.property.1
    let h : d ∈ ws' (F.parent x.val) b := x.property.2.symm ▸ hd
    HEq (G.tripleMidGamma F R L b d x hd y) (p.innerSliceCell y d h) :=
  G.leftLeaf_matches_rightTail F R L d x y hd

def tripleTailRawCell :
    fold 𝒮 Zₐ (dependentLabels (T:=T)
      (fun y : G.TripleMid F x b => B x.val y.val) (fun y z => D x.val y.val z))
      (dependentWord (G.tripleMidWord F x b) ((G.tailInput F x.val x.property.1).terms b d)) ⟶
    T.obj (B' a b) (D' a b d) :=
  let p := G.tailInput F x.val x.property.1
  let ys := G.tripleMidWord F x b
  let ws := p.terms b d
  let V := fun y : G.TripleMid F x b => B x.val y.val
  let D := fun (y : G.TripleMid F x b) z => D x.val y.val z
  taggedRaggedRows (dependentLabels (T:=T) V D) Prod.mk ws ys ≫
    act 𝒮 Zₐ (fun y => (Lin.left L (V y)).collect (D y) (ws y) ≫
      T.map (𝟙 (V y)) (G.tripleMidGamma F R L b d x hd y)) ys ≫
    DependentFibre.gather R V (D' a b d) ys ≫ T.map (G.tripleMidBeta F b x hb) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
theorem rightInnerSlice_raw_heq :
    HEq ((G.rightInput F R L).innerSliceCell x (b,d)
      ((dependentWord_mem (ys' a) (ws' a) (b,d)).mpr ⟨hb,hd⟩))
      (G.tripleTailRawCell F R L b d x hb hd) := by
  refine (G.rightInnerSlice_heq F R L b d x hb hd).trans ?_
  rcases x with ⟨x,hx,ex⟩
  change F.parent x = a at ex
  subst a
  let P := G.tailInput F x hx
  let xx : F.Slice (F.parent x) := ⟨x,hx,rfl⟩
  let h' := (dependentWord_mem (ys' (F.parent x)) (ws' (F.parent x)) (b,d)).mpr ⟨hb,hd⟩
  let E := dependentLabels (T:=T) (B x) (D x)
  let s := P.slice b
  let U := P.terms b d
  let f := fun (y : P.Slice b) (z : W) => (y.val,z)
  let g := fun p : P.Slice b × W => (p.1.val,p.2)
  let V := fun y : P.Slice b => B x y.val
  let D₀ := fun y : P.Slice b => D x y.val
  have e₀ : (dependentWord s U).map g = s.flatMap (fun y => (U y).map (f y)) := by
    unfold dependentWord
    simp only [List.map_flatMap, List.map_map]
    rfl
  have e₁ : fold 𝒮 Zₐ E (s.flatMap (fun y => (U y).map (f y))) =
      fold 𝒮 Zₐ (E ∘ g) (dependentWord s U) :=
    (congrArg (fold 𝒮 Zₐ E) e₀.symm).trans (std_fold_map E g (dependentWord s U))
  have ht : HEq (taggedRaggedRows E f U s) (taggedRaggedRows (E ∘ g) Prod.mk U s) :=
    (taggedRaggedRows_tag_heq E g Prod.mk U s).symm
  let q := fun y => (Lin.left L (V y)).collect (D₀ y) (U y) ≫ T.map (𝟙 (V y))
    (G.tripleMidGamma F R L b d xx hd y)
  have aa (y : P.Slice b) : P.innerSliceCell y d hd = G.tripleMidGamma F R L b d xx hd y :=
    eq_of_heq (G.tripleMidGamma_tail F R L b d xx hd y).symm
  have bb : P.locOuter b hb = G.tripleMidBeta F b xx hb :=
    eq_of_heq (G.tripleMidBeta_tail F b xx hb).symm
  have h₀ := origDependentCell_flatRows P R L (b,d) h'
  change HEq (origDependentCell P R L (b,d) h') (G.tripleTailRawCell F R L b d xx hb hd)
  rw [h₀]
  apply HEq.trans (hom_source_pin_heq _ _)
  have k : (fun y : P.Slice b => attachedSliceChildCell P L y d hd) = q := by
    funext y
    unfold q attachedSliceChildCell
    rw [aa y]
    rfl
  change HEq (taggedRaggedRows E f U s ≫ act 𝒮 Zₐ (fun y => attachedSliceChildCell P L y d hd) s ≫
      DependentFibre.gather R V (D' (F.parent x) b d) s ≫ T.map (P.locOuter b hb) (𝟙 _)) _
  rw [k, bb]
  apply structural_seq_heq (K:=coeff (C:=C)) e₁
    (rfl : fold 𝒮 Zₐ (fun y : P.Slice b => fold 𝒮 Zₐ (E ∘ f y) (U y)) s = _)
    (rfl : T.obj (B' (F.parent x) b) (D' (F.parent x) b d) = _) ht
  rfl

theorem rightInnerSlice_raw_word :
    let P := G.tailInput F x.val x.property.1
    let f := fun t : P.Slice b × W => (t.1.val,t.2)
    (dependentWord (G.tripleMidWord F x b) (P.terms b d)).map f =
      (G.rightInput F R L).terms a (b,d) x :=
  dependentSlice_word_raw (G.tailInput F x.val x.property.1) (b,d)

set_option backward.isDefEq.respectTransparency false in
theorem rightAttachedChild_raw_heq :
    let P := G.tailInput F x.val x.property.1
    let V := F.parentVal a x
    let A := dependentLabels (T:=T) (fun y : P.Slice b => B x.val y.val)
      (fun y z => D x.val y.val z)
    let w := dependentWord (G.tripleMidWord F x b) (P.terms b d)
    HEq
      (attachedSliceChildCell (G.rightInput F R L) L x (b,d)
        ((dependentWord_mem (ys' a) (ws' a) (b,d)).mpr ⟨hb,hd⟩))
      ((Lin.left L V).collect A w ≫ T.map (𝟙 V) (G.tripleTailRawCell F R L b d x hb hd)) := by
  intro P V A w
  let f := fun t : P.Slice b × W => (t.1.val,t.2)
  let B := dependentLabels (T:=T) (B x.val) (D x.val)
  let w' := (G.rightInput F R L).terms a (b,d) x
  let e : w.map f = w' := G.rightInnerSlice_raw_word F R L b d x
  let e₁ : fold 𝒮 Zₐ B w' = fold 𝒮 Zₐ A w :=
    (congrArg (fold 𝒮 Zₐ B) e.symm).trans (std_fold_map B f w)
  let e₀ : fold 𝒮 Zₐ (T.obj V ∘ B) w' = fold 𝒮 Zₐ (T.obj V ∘ A) w :=
    (congrArg (fold 𝒮 Zₐ (T.obj V ∘ B)) e.symm).trans (std_fold_map (T.obj V ∘ B) f w)
  let e₂ : T.obj V (fold 𝒮 Zₐ B w') = T.obj V (fold 𝒮 Zₐ A w) := congrArg (T.obj V) e₁
  let h : (b,d) ∈ dependentWord (ys' a) (ws' a) := (dependentWord_mem _ _ _).mpr ⟨hb,hd⟩
  have k {l : List (Y × W)} (e : l = w') :
      HEq ((Lin.left L V).collect B w') ((Lin.left L V).collect B l) := by subst l; rfl
  have h₀ := (k e).trans (linCollect_map_heq (Lin.left L V) B f w).symm
  have h₁ := G.rightInnerSlice_raw_heq F R L b d x hb hd
  exact structural_seq_heq (K:=coeff (C:=C)) e₀ e₂ (rfl : T.obj V (T.obj (B' a b) (D' a b d)) = _) h₀
    (biMap_heq (T:=T) (rfl : V = V) rfl e₁ rfl (show HEq (𝟙 V) (𝟙 V) from HEq.rfl) h₁)

end TailCells

section RightFinal
variable (a : X') (b : Y') (d : W')
variable (ha : a ∈ xs') (hb : b ∈ ys' a) (hd : d ∈ ws' a b)

def rightFinalRows (x : F.Slice a) : List (G.TripleMid F x b × W) :=
  dependentWord (G.tripleMidWord F x b) ((G.tailInput F x.val x.property.1).terms b d)

def rightFinalTag (x : F.Slice a) (v : G.TripleMid F x b × W) : X × Y × W :=
  (x.val,v.1.val,v.2)

def rightFinalWords (x : F.Slice a) : List (X × Y × W) :=
  (G.rightFinalRows F a b d x).map (G.rightFinalTag F a b x)

set_option backward.isDefEq.respectTransparency false in
theorem rightFinalWords_read (x : F.Slice a) :
    G.rightFinalWords F a b d x =
      ((G.rightInput F R L).terms a (b,d) x).map (Prod.mk x.val) := by
  unfold rightFinalWords
  let f := fun t : G.TripleMid F x b × W => (t.1.val,t.2)
  have z := G.rightInnerSlice_raw_word F R L b d x
  change (G.rightFinalRows F a b d x).map f = _ at z
  change (G.rightFinalRows F a b d x).map (Prod.mk x.val ∘ f) = _
  rw [← List.map_map, z]

def rightFinalAttach (x : F.Slice a) :
    fold 𝒮 Zₐ (assocRightLabels T V B D ∘ G.rightFinalTag F a b x)
      (G.rightFinalRows F a b d x) ⟶ T.obj (F.parentVal a x) (T.obj (B' a b) (D' a b d)) :=
  let V := F.parentVal a x
  let A := dependentLabels (T:=T) (fun y : G.TripleMid F x b => B x.val y.val) (fun y z => D x.val y.val z)
  (Lin.left L V).collect A (G.rightFinalRows F a b d x) ≫
    T.map (𝟙 V) (G.tripleTailRawCell F R L b d x hb hd)

def rightFinalSchedule :
    fold 𝒮 Zₐ (assocRightLabels T V B D) ((F.slice a).flatMap (G.rightFinalWords F a b d)) ⟶
      T.obj (V' a) (T.obj (B' a b) (D' a b d)) :=
  let s := F.slice a
  let A := assocRightLabels T V B D
  let r := G.rightFinalWords F a b d
  let c := fun x => eqToHom (std_fold_map A (G.rightFinalTag F a b x) (G.rightFinalRows F a b d x))
  rowsChart A r s ≫ act 𝒮 Zₐ (fun x => c x ≫ G.rightFinalAttach F R L a b d hb hd x) s ≫
    DependentFibre.gather R (F.parentVal a) (T.obj (B' a b) (D' a b d)) s ≫
    T.map (F.locOuter a ha) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
theorem rightFinalSchedule_heq :
    HEq (origDependentCell (G.rightInput F R L) R L (a,(b,d))
      ((dependentWord_mem _ _ _).mpr ⟨ha,(dependentWord_mem _ _ _).mpr ⟨hb,hd⟩⟩))
      (G.rightFinalSchedule F R L a b d ha hb hd) := by
  let s := F.slice a
  let P := G.rightInput F R L
  let D := assocRightLabels T V B D
  let M := P.terms a (b,d)
  let f := fun (x : F.Slice a) (y : Y × W) => (x.val,y)
  let w := G.rightFinalRows F a b d
  let read := fun (x : F.Slice a) (y : G.TripleMid F x b × W) => (y.1.val,y.2)
  let r := G.rightFinalWords F a b d
  let t := fun x => G.rightFinalTag F a b x
  let hw (x : F.Slice a) : (w x).map (read x) = M x := G.rightInnerSlice_raw_word F R L b d x
  let h := (dependentWord_mem (ys' a) (ws' a) (b,d)).mpr ⟨hb,hd⟩
  let p := fun x => attachedSliceChildCell P L x (b,d) h
  let q := G.rightFinalAttach F R L a b d hb hd
  let p' := fun x => std_fold_map D (f x) (M x)
  let q' := fun x => std_fold_map D (t x) (w x)
  let e := fun x => (congrArg (fold 𝒮 Zₐ (D ∘ f x)) (hw x).symm).trans
    (std_fold_map (D ∘ f x) (read x) (w x))
  have hh (x : F.Slice a) : p x = eqToHom (e x) ≫ q x := by
    have z := heq_paste (e x) (rfl : _ = _) (G.rightAttachedChild_raw_heq F R L b d x hb hd)
    rw [eqToHom_refl, Category.comp_id] at z
    exact z
  have k := origDependentCell_flatRows P R L (a,(b,d))
      ((dependentWord_mem _ _ _).mpr ⟨ha,h⟩)
  rw [k]
  apply HEq.trans (hom_source_pin_heq _ _)
  let c := (congrArg (fold 𝒮 Zₐ D) (congrArg (fun m => s.flatMap m)
    (funext fun x => (G.rightFinalWords_read F R L a b d x).symm)))
  apply HEq.trans _ (hom_source_pin_heq c _)
  apply heq_of_eq
  have zz := taggedRaggedRows_childRead D f read w M hw s
  dsimp only at zz
  have rr : act 𝒮 Zₐ p s = act 𝒮 Zₐ (fun x => eqToHom (e x)) s ≫ act 𝒮 Zₐ q s :=
    (congrArg (fun f => act 𝒮 Zₐ f s) (funext hh)).trans
      (act_seq 𝒮 Zₐ (fun x => eqToHom (e x)) q s).symm
  let z := DependentFibre.gather R (F.parentVal a) (T.obj (B' a b) (D' a b d)) s ≫
    T.map (F.locOuter a ha) (𝟙 (T.obj (B' a b) (D' a b d)))
  change (rowsChart D (fun x => (M x).map (f x)) s ≫ act 𝒮 Zₐ (fun x => eqToHom (p' x)) s) ≫
      act 𝒮 Zₐ p s ≫ z = eqToHom c ≫ rowsChart D r s ≫
    act 𝒮 Zₐ (fun x => eqToHom (q' x) ≫ q x) s ≫ z
  rw [rr]
  simp only [Category.assoc] at zz ⊢
  have zz' : rowsChart D (fun x => (M x).map (f x)) s ≫
      act 𝒮 Zₐ (fun x => eqToHom (p' x)) s ≫ act 𝒮 Zₐ (fun x => eqToHom (e x)) s =
      eqToHom c ≫ rowsChart D r s ≫ act 𝒮 Zₐ (fun x => eqToHom (q' x)) s := zz
  rw [reassoc_of% zz']
  rw [reassoc_of% (act_seq 𝒮 Zₐ (fun x => eqToHom (q' x)) q s)]

set_option backward.isDefEq.respectTransparency false in
theorem rightFinalWords_fibre :
    (F.slice a).flatMap (G.rightFinalWords F a b d) =
      wordFibre (dependentWord xs (fun x => dependentWord (ys x) (ws x)))
        (origDepCarrier (G.rightInput F R L)) (a,(b,d)) := by
  let p := G.rightInput F R L
  have k := dependentSlice_word_raw p (a,(b,d))
  unfold dependentWord at k
  rw [List.map_flatMap] at k
  simp only [List.map_map] at k
  change (F.slice a).flatMap (fun x => ((G.rightInput F R L).terms a (b,d) x).map (Prod.mk x.val)) = _ at k
  exact (congrArg (fun f => (F.slice a).flatMap f) (funext (G.rightFinalWords_read F R L a b d))).trans k

end RightFinal

section LeftParent
variable (a : X') (b : Y') (ha : a ∈ xs') (hb : b ∈ ys' a)

def leftMiddleTag (x : F.Slice a) (y : G.TripleMid F x b) : X × Y := (x.val,y.val)

def leftMiddleWords (x : F.Slice a) : List (X × Y) :=
  (G.tripleMidWord F x b).map (G.leftMiddleTag F a b x)

def leftMiddleRaw (x : F.Slice a) :
    fold 𝒮 Zₐ (dependentLabels (T:=T) V B ∘ G.leftMiddleTag F a b x)
      (G.tripleMidWord F x b) ⟶ T.obj (F.parentVal a x) (B' a b) :=
  (Lin.left L (F.parentVal a x)).collect (fun y : G.TripleMid F x b => B x.val y.val)
    (G.tripleMidWord F x b) ≫ T.map (𝟙 (F.parentVal a x)) (G.tripleMidBeta F b x hb)

def leftFinalOuterRaw :
    fold 𝒮 Zₐ (dependentLabels (T:=T) V B) ((F.slice a).flatMap (G.leftMiddleWords F a b)) ⟶
      T.obj (V' a) (B' a b) :=
  let s := F.slice a
  let E := dependentLabels (T:=T) V B
  let f := fun x => eqToHom (std_fold_map E (G.leftMiddleTag F a b x) (G.tripleMidWord F x b))
  rowsChart E (G.leftMiddleWords F a b) s ≫
    act 𝒮 Zₐ (fun x => f x ≫ G.leftMiddleRaw F L a b hb x) s ≫
    DependentFibre.gather R (F.parentVal a) (B' a b) s ≫ T.map (F.locOuter a ha) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
theorem leftFinalOuterRaw_heq :
    HEq (origDependentCell F R L (a,b) ((dependentWord_mem _ _ _).mpr ⟨ha,hb⟩))
      (G.leftFinalOuterRaw F R L a b ha hb) := by
  let s := F.slice a
  let D := dependentLabels (T:=T) V B
  let M := F.terms a b
  let f := fun (x : F.Slice a) (y : Y) => (x.val,y)
  let w := fun x : F.Slice a => G.tripleMidWord F x b
  let read := fun (x : F.Slice a) (y : G.TripleMid F x b) => y.val
  let r := G.leftMiddleWords F a b
  let t := G.leftMiddleTag F a b
  let h' (x : F.Slice a) : (w x).map (read x) = M x := sliceWord_map (ys x.val) (F.child x.val) b
  let p := fun x => attachedSliceChildCell F L x b hb
  let q := G.leftMiddleRaw F L a b hb
  let p' := fun x => std_fold_map D (f x) (M x)
  let q' := fun x => std_fold_map D (t x) (w x)
  let e := fun x => (congrArg (fold 𝒮 Zₐ (D ∘ f x)) (h' x).symm).trans
    (std_fold_map (D ∘ f x) (read x) (w x))
  have hh (x : F.Slice a) : p x = eqToHom (e x) ≫ q x := by
    let H := F.parentVal a x
    let J := B x.val
    let d := (std_fold_map J (read x) (w x)).symm.trans (congrArg (fold 𝒮 Zₐ J) (h' x))
    let k := F.innerSliceCell x b hb
    have n₀ : HEq ((Lin.left L H).collect J (M x)) ((Lin.left L H).collect (J ∘ read x) (w x)) := by
      have z {l : List Y} (h : l = M x) :
          HEq ((Lin.left L H).collect J (M x)) ((Lin.left L H).collect J l) := by subst l; rfl
      exact (z (h' x)).trans (linCollect_map_heq (Lin.left L H) J (read x) (w x)).symm
    have n₁ : HEq k (G.tripleMidBeta F b x hb) := (hom_source_pin_heq d k).symm
    have o : HEq (p x) (q x) :=
      structural_seq_heq (K:=coeff (C:=C)) (e x) (congrArg (T.obj H) d.symm)
        (rfl : T.obj H (B' a b) = _) n₀
        (biMap_heq (T:=T) (rfl : H = H) rfl d.symm rfl (show HEq (𝟙 H) (𝟙 H) from HEq.rfl) n₁)
    have m := heq_paste (e x) (rfl : _ = _) o
    rw [eqToHom_refl, Category.comp_id] at m
    exact m
  have k := origDependentCell_flatRows F R L (a,b) ((dependentWord_mem _ _ _).mpr ⟨ha,hb⟩)
  rw [k]
  apply HEq.trans (hom_source_pin_heq _ _)
  let c := congrArg (fold 𝒮 Zₐ D) (congrArg (fun m => s.flatMap m)
    (funext fun x => (congrArg (List.map (f x)) (h' x).symm).trans List.map_map))
  apply HEq.trans _ (hom_source_pin_heq c _)
  apply heq_of_eq
  have zz := taggedRaggedRows_childRead D f read w M h' s
  dsimp only at zz
  have rr : act 𝒮 Zₐ p s = act 𝒮 Zₐ (fun x => eqToHom (e x)) s ≫ act 𝒮 Zₐ q s :=
    (congrArg (fun f => act 𝒮 Zₐ f s) (funext hh)).trans
      (act_seq 𝒮 Zₐ (fun x => eqToHom (e x)) q s).symm
  let z := DependentFibre.gather R (F.parentVal a) (B' a b) s ≫ T.map (F.locOuter a ha) (𝟙 (B' a b))
  change (rowsChart D (fun x => (M x).map (f x)) s ≫ act 𝒮 Zₐ (fun x => eqToHom (p' x)) s) ≫
      act 𝒮 Zₐ p s ≫ z = eqToHom c ≫ rowsChart D r s ≫
    act 𝒮 Zₐ (fun x => eqToHom (q' x) ≫ q x) s ≫ z
  rw [rr]
  simp only [Category.assoc] at zz ⊢
  have zz' : rowsChart D (fun x => (M x).map (f x)) s ≫
      act 𝒮 Zₐ (fun x => eqToHom (p' x)) s ≫ act 𝒮 Zₐ (fun x => eqToHom (e x)) s =
      eqToHom c ≫ rowsChart D r s ≫ act 𝒮 Zₐ (fun x => eqToHom (q' x)) s := zz
  rw [reassoc_of% zz']
  rw [reassoc_of% (act_seq 𝒮 Zₐ (fun x => eqToHom (q' x)) q s)]

def leftMiddleSlice (x : F.Slice a) : List ((G.leftInput F R L).Slice (a,b)) :=
  (G.tripleMidWord F x b).map (G.tripleMidRead F R L x)

theorem leftMiddleSlice_val (x : F.Slice a) :
    (G.leftMiddleSlice F R L a b x).map Subtype.val = G.leftMiddleWords F a b x := by
  unfold leftMiddleSlice leftMiddleWords
  rw [List.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem leftFinalOuter_index :
    let P := G.leftInput F R L
    let s := F.slice a
    let K := P.parentVal (a,b)
    let rows := G.leftMiddleSlice F R L a b
    let r := fun x => eqToHom (std_fold_map K (G.tripleMidRead F R L x) (G.tripleMidWord F x b))
    let chart := (G.tripleMidRead_word F R L a b).symm
    P.locOuter (a,b) ((dependentWord_mem _ _ _).mpr ⟨ha,hb⟩) =
      eqToHom (congrArg (fold 𝒮 Zₐ K) chart) ≫ rowsChart K rows s ≫
        act 𝒮 Zₐ (fun x => r x ≫ G.leftMiddleRaw F L a b hb x) s ≫
        DependentFibre.gather R (F.parentVal a) (B' a b) s ≫ T.map (F.locOuter a ha) (𝟙 _) := by
  intro P s K rows r chart
  let E := dependentLabels (T:=T) V B
  let h := (dependentWord_mem xs' ys' (a,b)).mpr ⟨ha,hb⟩
  let v : P.Slice (a,b) → X × Y := Subtype.val
  let rx := G.leftMiddleWords F a b
  let a₀ := fun x => eqToHom (std_fold_map E (G.leftMiddleTag F a b x) (G.tripleMidWord F x b))
  let a₁ := fun x => eqToHom ((congrArg (fold 𝒮 Zₐ E) (G.leftMiddleSlice_val F R L a b x).symm).trans
      (std_fold_map E v (rows x)))
  let a₂ := G.leftMiddleRaw F L a b hb
  let a₃ : fold 𝒮 Zₐ K (P.slice (a,b)) = fold 𝒮 Zₐ E (s.flatMap rx) :=
    ((std_fold_map E v (P.slice (a,b))).symm.trans
      (congrArg (fold 𝒮 Zₐ E) (congrArg (List.map v) chart))).trans
        ((congrArg (fold 𝒮 Zₐ E) List.map_flatMap).trans
          (congrArg (fold 𝒮 Zₐ E) (congrArg (fun r => s.flatMap r)
            (funext fun x => G.leftMiddleSlice_val F R L a b x))))
  have h₀ : P.locOuter (a,b) h = eqToHom a₃ ≫ G.leftFinalOuterRaw F R L a b ha hb := by
    have k : HEq (P.locOuter (a,b) h) (G.leftFinalOuterRaw F R L a b ha hb) :=
      (P.locOuter_heq_raw _ _).trans (G.leftFinalOuterRaw_heq F R L a b ha hb)
    have e := heq_paste a₃ (rfl : _ = _) k
    rw [eqToHom_refl, Category.comp_id] at e
    exact e
  have hh (x : F.Slice a) : a₁ x ≫ r x = a₀ x := by
    unfold a₁ r a₀
    rw [eqToHom_trans]
  have hh' : act 𝒮 Zₐ a₁ s ≫ act 𝒮 Zₐ r s = act 𝒮 Zₐ a₀ s :=
    (act_seq 𝒮 Zₐ a₁ r s).trans (congrArg (fun f => act 𝒮 Zₐ f s) (funext hh))
  let e₀ := rows_relabel_obj E v rows s
  let c := (congrArg (fold 𝒮 Zₐ E) (congrArg (fun r => s.flatMap r)
      (funext fun x => G.leftMiddleSlice_val F R L a b x)))
  let ee := c.symm.trans e₀
  have rr : rowsChart E rx s ≫ act 𝒮 Zₐ a₁ s = eqToHom ee ≫ rowsChart K rows s := by
    let hh := fun x => G.leftMiddleSlice_val F R L a b x
    let z := rowsChart_rows_congr E hh s
    let v' := fun x => eqToHom (congrArg (fold 𝒮 Zₐ E) (hh x))
    let w' := fun x => eqToHom (std_fold_map E v (rows x))
    have a (x : F.Slice a) : v' x ≫ a₁ x = w' x := by
      unfold v' a₁ w'
      rw [eqToHom_trans]
    have b : act 𝒮 Zₐ v' s ≫ act 𝒮 Zₐ a₁ s = act 𝒮 Zₐ w' s :=
      (act_seq 𝒮 Zₐ v' a₁ s).trans (congrArg (fun f => act 𝒮 Zₐ f s) (funext a))
    have k := rowsChart_relabel_input E v rows s
    change rowsChart E (fun x => (rows x).map v) s ≫ act 𝒮 Zₐ w' s =
      eqToHom e₀ ≫ rowsChart K rows s at k
    rw [← b, reassoc_of% z] at k
    have q := congrArg (fun f => eqToHom c.symm ≫ f) k
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at q
    exact q
  rw [h₀]
  change eqToHom a₃ ≫ (rowsChart E rx s ≫ act 𝒮 Zₐ (fun x => a₀ x ≫ a₂ x) s ≫
    DependentFibre.gather R (F.parentVal a) (B' a b) s ≫ T.map (F.locOuter a ha) (𝟙 _)) =
      eqToHom _ ≫ rowsChart K rows s ≫ act 𝒮 Zₐ (fun x => r x ≫ a₂ x) s ≫ _
  have h' : act 𝒮 Zₐ (fun x => a₀ x ≫ a₂ x) s =
      act 𝒮 Zₐ a₁ s ≫ act 𝒮 Zₐ (fun x => r x ≫ a₂ x) s := by
    calc
      _ = act 𝒮 Zₐ a₀ s ≫ act 𝒮 Zₐ a₂ s := (act_seq 𝒮 Zₐ a₀ a₂ s).symm
      _ = (act 𝒮 Zₐ a₁ s ≫ act 𝒮 Zₐ r s) ≫ act 𝒮 Zₐ a₂ s :=
        congrArg (fun q => q ≫ act 𝒮 Zₐ a₂ s) hh'.symm
      _ = _ := (Category.assoc _ _ _).trans (congrArg (fun q => act 𝒮 Zₐ a₁ s ≫ q) (act_seq 𝒮 Zₐ r a₂ s))
  rw [h']
  simp only [Category.assoc]
  rw [reassoc_of% rr, eqToHom_trans_assoc]

end LeftParent

section LeftFinal
variable (a : X') (b : Y') (d : W')
variable (ha : a ∈ xs') (hb : b ∈ ys' a) (hd : d ∈ ws' a b)

def leftFinalTag (x : F.Slice a) (v : G.TripleMid F x b × W) : (X × Y) × W :=
  ((x.val,v.1.val),v.2)

def leftFinalWords (x : F.Slice a) : List ((X × Y) × W) :=
  (G.rightFinalRows F a b d x).map (G.leftFinalTag F a b x)

theorem leftFinalWords_matches (x : F.Slice a) :
    (G.leftFinalWords F a b d x).map tripleRetag = G.rightFinalWords F a b d x := by
  unfold leftFinalWords rightFinalWords
  rw [List.map_map]
  rfl

def leftFinalLeafAttach (x : F.Slice a) (y : G.TripleMid F x b) :
    fold 𝒮 Zₐ (fun z => assocLeftLabels T V B D (G.leftFinalTag F a b x (y,z)))
      ((G.tailInput F x.val x.property.1).terms b d y) ⟶
      T.obj (T.obj (V x.val) (B x.val y.val)) (D' a b d) :=
  let C₀ := T.obj (V x.val) (B x.val y.val)
  (Lin.left L C₀).collect (D x.val y.val) ((G.tailInput F x.val x.property.1).terms b d y) ≫
    T.map (𝟙 C₀) (G.tripleMidGamma F R L b d x hd y)

def leftFinalAttach (x : F.Slice a) :
    fold 𝒮 Zₐ (assocLeftLabels T V B D ∘ G.leftFinalTag F a b x)
      (G.rightFinalRows F a b d x) ⟶ T.obj (T.obj (F.parentVal a x) (B' a b)) (D' a b d) :=
  let A := assocLeftLabels T V B D ∘ G.leftFinalTag F a b x
  let ys := G.tripleMidWord F x b
  let ws := (G.tailInput F x.val x.property.1).terms b d
  let B₀ := fun y : G.TripleMid F x b => T.obj (V x.val) (B x.val y.val)
  let d₀ := D' a b d
  taggedRaggedRows A Prod.mk ws ys ≫ act 𝒮 Zₐ (G.leftFinalLeafAttach F R L a b d hd x) ys ≫
    DependentFibre.gather R B₀ d₀ ys ≫ T.map (G.leftMiddleRaw F L a b hb x) (𝟙 d₀)

def leftFinalSchedule :
    fold 𝒮 Zₐ (assocLeftLabels T V B D) ((F.slice a).flatMap (G.leftFinalWords F a b d)) ⟶
      T.obj (T.obj (V' a) (B' a b)) (D' a b d) :=
  let s := F.slice a
  let A := assocLeftLabels T V B D
  let r := G.leftFinalWords F a b d
  let c := fun x => eqToHom (std_fold_map A (G.leftFinalTag F a b x) (G.rightFinalRows F a b d x))
  let V₀ := F.parentVal a
  let d₀ := D' a b d
  rowsChart A r s ≫ act 𝒮 Zₐ (fun x => c x ≫ G.leftFinalAttach F R L a b d hb hd x) s ≫
    DependentFibre.gather R (fun x => T.obj (V₀ x) (B' a b)) d₀ s ≫
    T.map (DependentFibre.gather R V₀ (B' a b) s ≫ T.map (F.locOuter a ha) (𝟙 (B' a b))) (𝟙 d₀)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
theorem leftFinalGather_stage
    (NR : GatherOuterNat R)
    [(rightFactor (T:=T) (D' a b d)).LaxBraided] (hr : SameRightGather R (D' a b d)) :
    let P := G.leftInput F R L
    let s := F.slice a
    let z := P.slice (a,b)
    let K := P.parentVal (a,b)
    let rows := G.leftMiddleSlice F R L a b
    let r := fun x => eqToHom (std_fold_map K (G.tripleMidRead F R L x) (G.tripleMidWord F x b))
    let d₀ := D' a b d
    let H := fun x => T.obj (F.parentVal a x) (B' a b)
    let m := DependentFibre.gather R (F.parentVal a) (B' a b) s ≫ T.map (F.locOuter a ha) (𝟙 (B' a b))
    let e := congrArg (fold 𝒮 Zₐ (fun x => T.obj (K x) d₀)) (G.tripleMidRead_word F R L a b).symm
    let c := fun x => DependentFibre.gather R K d₀ (rows x) ≫
      T.map (r x ≫ G.leftMiddleRaw F L a b hb x) (𝟙 d₀)
    DependentFibre.gather R K d₀ z ≫
        T.map (P.locOuter (a,b) ((dependentWord_mem _ _ _).mpr ⟨ha,hb⟩)) (𝟙 d₀) =
      eqToHom e ≫ rowsChart (fun x => T.obj (K x) d₀) rows s ≫
        act 𝒮 Zₐ c s ≫ DependentFibre.gather R H d₀ s ≫ T.map m (𝟙 d₀) := by
  intro P s z K rows r d₀ H m e c
  let Q := rightFactor (T:=T) d₀
  let d := (G.tripleMidRead_word F R L a b).symm
  let KK := fun x => T.obj (K x) d₀
  let p := fun x => r x ≫ G.leftMiddleRaw F L a b hb x
  let G₀ := Lin.right R d₀
  let L₀ := fun x => fold 𝒮 Zₐ K (rows x)
  have q {l₁ l₂ : List (P.Slice (a,b))} (h : l₁ = l₂) :
      DependentFibre.gather R K d₀ l₁ ≫ Q.map (eqToHom (congrArg (fold 𝒮 Zₐ K) h)) =
        eqToHom (congrArg (fold 𝒮 Zₐ KK) h) ≫ DependentFibre.gather R K d₀ l₂ := by
    cases h
    let f : fold 𝒮 Zₐ KK l₁ ⟶ T.obj (fold 𝒮 Zₐ K l₁) d₀ := DependentFibre.gather R K d₀ l₁
    change f ≫ Q.map (eqToHom (rfl : fold 𝒮 Zₐ K l₁ = _)) =
      eqToHom (rfl : fold 𝒮 Zₐ KK l₁ = _) ≫ f
    simp only [eqToHom_refl, Q.map_id, Category.id_comp]
    exact Category.comp_id f
  have g : DependentFibre.gather R K d₀ (s.flatMap rows) ≫ Q.map (rowsChart K rows s) =
      rowsChart KK rows s ≫ act 𝒮 Zₐ (fun x => DependentFibre.gather R K d₀ (rows x)) s ≫
        DependentFibre.gather R L₀ d₀ s :=
    (right_gather_rows R d₀ hr K rows s).symm
  have h : DependentFibre.gather R L₀ d₀ s ≫ Q.map (act 𝒮 Zₐ p s) =
      act 𝒮 Zₐ (fun x => Q.map (p x)) s ≫ DependentFibre.gather R H d₀ s := by
    have z := Lin.collect_nat G₀ (rightNatural R NR d₀) p s
    simp only [G₀, linRight_collect_gather] at z
    exact z.symm
  have hh : act 𝒮 Zₐ (fun x => DependentFibre.gather R K d₀ (rows x)) s ≫
      act 𝒮 Zₐ (fun x => Q.map (p x)) s = act 𝒮 Zₐ c s :=
    act_seq 𝒮 Zₐ (fun x => DependentFibre.gather R K d₀ (rows x)) (fun x => Q.map (p x)) s
  rw [leftFinalOuter_index (F:=F) (G:=G) R L a b ha hb]
  change DependentFibre.gather R K d₀ z ≫
      Q.map (eqToHom (congrArg (fold 𝒮 Zₐ K) d) ≫ rowsChart K rows s ≫ act 𝒮 Zₐ p s ≫ m) =
    eqToHom e ≫ rowsChart KK rows s ≫ act 𝒮 Zₐ c s ≫ DependentFibre.gather R H d₀ s ≫ Q.map m
  simp only [Q.map_comp]
  rw [reassoc_of% q d]
  change eqToHom e ≫ DependentFibre.gather R K d₀ (s.flatMap rows) ≫ Q.map (rowsChart K rows s) ≫
    Q.map (act 𝒮 Zₐ p s) ≫ Q.map m = _
  rw [reassoc_of% g, reassoc_of% h, reassoc_of% hh]

def leftBaseLeafWords (t : (G.leftInput F R L).Slice (a,b)) : List ((X × Y) × W) :=
  ((G.leftInput F R L).terms (a,b) d t).map (Prod.mk t.val)

theorem leftFinalWords_group (x : F.Slice a) :
    (G.leftMiddleSlice F R L a b x).flatMap (G.leftBaseLeafWords F R L a b d) =
      G.leftFinalWords F a b d x := by
  unfold leftMiddleSlice leftFinalWords rightFinalRows leftBaseLeafWords dependentWord
  let P := G.leftInput F R L
  let r : G.TripleMid F x b → P.Slice (a,b) := G.tripleMidRead F R L x
  let G₀ := fun z : P.Slice (a,b) => ((P.terms (a,b) d z).map (Prod.mk z.val))
  let s := G.tripleMidWord F x b
  let u := fun y => (((G.tailInput F x.val x.property.1).terms b d y).map (Prod.mk y))
  change (s.map r).flatMap G₀ = (s.flatMap u).map (G.leftFinalTag F a b x)
  rw [List.flatMap_map r G₀ s, List.map_flatMap]
  apply congrArg (fun f => s.flatMap f)
  funext y
  rw [List.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem leftFinalBranch_cell (x : F.Slice a) :
    let P := G.leftInput F R L
    let A := assocLeftLabels T V B D
    let K := P.parentVal (a,b)
    let rows := G.leftMiddleSlice F R L a b x
    let f := fun (y : P.Slice (a,b)) (z : W) => (y.val,z)
    let t := P.terms (a,b) d
    let d₀ := D' a b d
    let pin := std_fold_map K (G.tripleMidRead F R L x) (G.tripleMidWord F x b)
    let e := congrArg (fold 𝒮 Zₐ A) (G.leftFinalWords_group F R L a b d x)
    let j := std_fold_map A (G.leftFinalTag F a b x) (G.rightFinalRows F a b d x)
    taggedRaggedRows A f t rows ≫ act 𝒮 Zₐ (fun y => attachedSliceChildCell P L y d hd) rows ≫
      DependentFibre.gather R K d₀ rows ≫ T.map (eqToHom pin ≫ G.leftMiddleRaw F L a b hb x) (𝟙 d₀) =
      eqToHom e ≫ eqToHom j ≫ G.leftFinalAttach F R L a b d hb hd x := by
  intro P A K rows f t d₀ pin e j
  let H := rightFactor (T:=T) d₀
  let r : G.TripleMid F x b → P.Slice (a,b) := G.tripleMidRead F R L x
  let s := G.tripleMidWord F x b
  let u := G.rightFinalRows F a b d x
  let B := fun y => T.obj (K y) d₀
  let p := fun y : P.Slice (a,b) => attachedSliceChildCell P L y d hd
  let q := G.leftFinalLeafAttach F R L a b d hd x
  let src := std_fold_map B r s
  let C₀ := fun (y : G.TripleMid F x b) (z : W) => ((y,z) : G.TripleMid F x b × W)
  let D₀ := (A ∘ G.leftFinalTag F a b x)
  let C₁ := G.leftFinalTag F a b x
  let G₀ := DependentFibre.gather R (K ∘ r) d₀ s
  let V₀ := G.leftMiddleRaw F L a b hb x
  let W₀ := (G.tailInput F x.val x.property.1).terms b d
  have h₀ : DependentFibre.gather R K d₀ rows ≫ H.map (eqToHom pin) = eqToHom src ≫ G₀ :=
    heq_paste src (congrArg (T.obj · d₀) pin) ((rightGather_map_heq R K rfl r s).symm) |>
      fun p => by
        have ee {a b : C} (p : a = b) : H.map (eqToHom p) = eqToHom (congrArg (T.obj · d₀) p) := by
          subst b
          simp only [eqToHom_refl, H.map_id]
          rfl
        rw [ee]
        exact p
  have hp (y : G.TripleMid F x b) : p (r y) = q y := rfl
  have h₁ := taggedRaggedRows_read_parents A B f t r s p
  dsimp only at h₁
  let z₀ := congrArg (fold 𝒮 Zₐ A) (List.flatMap_map r (G.leftBaseLeafWords F R L a b d) s)
  have h₁' : taggedRaggedRows A f t rows ≫ act 𝒮 Zₐ p rows ≫ eqToHom src =
      eqToHom z₀ ≫ taggedRaggedRows A (f ∘ r) W₀ s ≫ act 𝒮 Zₐ q s := by
    have E := (funext hp)
    rw [← E]
    exact h₁
  let v : (s.flatMap (fun y => (W₀ y).map (f (r y)))) = (u.map C₁) := by
    unfold u rightFinalRows dependentWord
    rw [List.map_flatMap]
    apply congrArg (fun f => s.flatMap f)
    funext y
    rw [List.map_map]
    rfl
  have h₂ : taggedRaggedRows A (f ∘ r) W₀ s = eqToHom ((congrArg (fold 𝒮 Zₐ A) v).trans j) ≫
        taggedRaggedRows D₀ C₀ W₀ s := by
    have z := heq_paste ((congrArg (fold 𝒮 Zₐ A) v).trans j) (rfl : _ = _)
      (taggedRaggedRows_tag_heq A C₁ C₀ W₀ s).symm
    rw [eqToHom_refl, Category.comp_id] at z
    exact z
  change taggedRaggedRows A f t rows ≫ act 𝒮 Zₐ p rows ≫
      DependentFibre.gather R K d₀ rows ≫ H.map (eqToHom pin ≫ V₀) =
    eqToHom e ≫ eqToHom j ≫ G.leftFinalAttach F R L a b d hb hd x
  rw [H.map_comp, reassoc_of% h₀, reassoc_of% h₁', h₂]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2600000 in
theorem leftFinalSchedule_heq (NR : GatherOuterNat R)
    [(rightFactor (T:=T) (D' a b d)).LaxBraided] (hr : SameRightGather R (D' a b d)) :
    HEq (origDependentCell (G.leftInput F R L) R L ((a,b),d)
      ((dependentWord_mem _ _ _).mpr ⟨(dependentWord_mem _ _ _).mpr ⟨ha,hb⟩,hd⟩))
      (G.leftFinalSchedule F R L a b d ha hb hd) := by
  let P := G.leftInput F R L
  let A := assocLeftLabels T V B D
  let s := F.slice a
  let z := P.slice (a,b)
  let K := P.parentVal (a,b)
  let D := D' a b d
  let B := fun x => T.obj (K x) D
  let rows := G.leftMiddleSlice F R L a b
  let zs := s.flatMap rows
  let f := fun (y : P.Slice (a,b)) (w : W) => (y.val,w)
  let t := P.terms (a,b) d
  let M := G.leftBaseLeafWords F R L a b d
  let M' := G.leftFinalWords F a b d
  let v := fun x => std_fold_map K (G.tripleMidRead F R L (b:=b) x) (G.tripleMidWord F x b)
  let c := fun x => DependentFibre.gather R K D (rows x) ≫
    T.map (eqToHom (v x) ≫ G.leftMiddleRaw F L a b hb x) (𝟙 D)
  let p := fun y : P.Slice (a,b) => attachedSliceChildCell P L y d hd
  let gam := fun x => taggedRaggedRows A f t (rows x) ≫ act 𝒮 Zₐ p (rows x)
  let j := fun x => std_fold_map A (G.leftFinalTag F a b x) (G.rightFinalRows F a b d x)
  let al := fun x => congrArg (fold 𝒮 Zₐ A) (G.leftFinalWords_group F R L a b d x)
  let q := G.leftFinalAttach F R L a b d hb hd
  let F₀ := fun x => T.obj (F.parentVal a x) (B' a b)
  let R₀ := DependentFibre.gather R F₀ D s ≫ T.map
    (DependentFibre.gather R (F.parentVal a) (B' a b) s ≫ T.map (F.locOuter a ha) (𝟙 (B' a b))) (𝟙 D)
  let e := (G.tripleMidRead_word F R L a b).symm
  let fa := congrArg (fold 𝒮 Zₐ A) (congrArg (List.flatMap M) e)
  let fb := congrArg (fold 𝒮 Zₐ A) (List.flatMap_assoc (l:=s) (f:=rows) (g:=M))
  let fc := congrArg (fold 𝒮 Zₐ A) (congrArg (fun r => s.flatMap r)
    (funext fun x => G.leftFinalWords_group F R L a b d x))
  have m : taggedRaggedRows A f t z ≫ act 𝒮 Zₐ p z ≫ eqToHom (congrArg (fold 𝒮 Zₐ B) e) =
      eqToHom fa ≫ taggedRaggedRows A f t zs ≫ act 𝒮 Zₐ p zs := by
    have h {z zs : List (P.Slice (a,b))} (e : z = zs) :
        taggedRaggedRows A f t z ≫ act 𝒮 Zₐ p z ≫ eqToHom (congrArg (fold 𝒮 Zₐ B) e) =
        eqToHom (congrArg (fold 𝒮 Zₐ A) (congrArg (List.flatMap M) e)) ≫
          taggedRaggedRows A f t zs ≫ act 𝒮 Zₐ p zs := by
      cases e
      let g : fold 𝒮 Zₐ (fun y => fold 𝒮 Zₐ (A ∘ f y) (t y)) z ⟶ fold 𝒮 Zₐ B z := act 𝒮 Zₐ p z
      change taggedRaggedRows A f t z ≫ g ≫ 𝟙 _ = 𝟙 _ ≫ taggedRaggedRows A f t z ≫ g
      rw [Category.id_comp, Category.comp_id g]
    exact h e
  have m' : taggedRaggedRows A f t zs ≫ act 𝒮 Zₐ p zs ≫ rowsChart B rows s =
      eqToHom fb ≫ rowsChart A (fun x => (rows x).flatMap M) s ≫ act 𝒮 Zₐ gam s :=
    taggedRaggedRows_parent_groups A B f t s rows p
  have h (x : F.Slice a) : gam x ≫ c x = eqToHom (al x) ≫ eqToHom (j x) ≫ q x :=
    (Category.assoc _ _ _).trans (G.leftFinalBranch_cell F R L a b d hb hd x)
  have hh : act 𝒮 Zₐ gam s ≫ act 𝒮 Zₐ c s =
      act 𝒮 Zₐ (fun x => eqToHom (al x)) s ≫ act 𝒮 Zₐ (fun x => eqToHom (j x) ≫ q x) s :=
    (act_seq 𝒮 Zₐ gam c s).trans ((congrArg (fun f => act 𝒮 Zₐ f s) (funext h)).trans
      (act_seq 𝒮 Zₐ (fun x => eqToHom (al x)) (fun x => eqToHom (j x) ≫ q x) s).symm)
  have h' : rowsChart A (fun x => (rows x).flatMap M) s ≫ act 𝒮 Zₐ (fun x => eqToHom (al x)) s =
      eqToHom fc ≫ rowsChart A M' s := rowsChart_rows_congr A (G.leftFinalWords_group F R L a b d) s
  have o := origDependentCell_flatRows P R L ((a,b),d)
    ((dependentWord_mem _ _ _).mpr ⟨(dependentWord_mem _ _ _).mpr ⟨ha,hb⟩,hd⟩)
  rw [o]
  apply HEq.trans (hom_source_pin_heq _ _)
  apply HEq.trans _ (hom_source_pin_heq ((fa.trans fb).trans fc) _)
  apply heq_of_eq
  have g := leftFinalGather_stage (F:=F) (G:=G) R L a b d ha hb NR hr
  change DependentFibre.gather R K D z ≫ T.map (P.locOuter (a,b) _) (𝟙 D) =
      eqToHom (congrArg (fold 𝒮 Zₐ B) e) ≫ rowsChart B rows s ≫ act 𝒮 Zₐ c s ≫ R₀ at g
  change taggedRaggedRows A f t z ≫ act 𝒮 Zₐ p z ≫
      DependentFibre.gather R K D z ≫ T.map (P.locOuter (a,b) _) (𝟙 D) =
    eqToHom ((fa.trans fb).trans fc) ≫ rowsChart A M' s ≫
      act 𝒮 Zₐ (fun x => eqToHom (j x) ≫ q x) s ≫ R₀
  rw [g, reassoc_of% m, reassoc_of% m', reassoc_of% hh, reassoc_of% h']
  simp only [eqToHom_trans_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2600000 in
theorem finalSchedules_square (P : TensorPrimitive T)
    (NR : GatherOuterNat R) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L) :
    let A := assocLeftLabels T V B D
    let A' := A ∘ (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
    let r := (F.slice a).flatMap (G.rightFinalWords F a b d)
    let φ := fun z : X × Y × W => P.assoc (V z.1) (B z.1 z.2.1) (D z.1 z.2.1 z.2.2)
    HEq
      (G.leftFinalSchedule F R L a b d ha hb hd ≫ P.assoc (V' a) (B' a b) (D' a b d))
      (act 𝒮 Zₐ (V:=A') φ r ≫ G.rightFinalSchedule F R L a b d ha hb hd) := by
  intro A A' r φ
  let A₁ := assocRightLabels T V B D
  let s := F.slice a
  let V := F.parentVal a
  let b' := B' a b
  let d' := D' a b d
  let k := fun x => P.assoc (V x) b' d'
  let r₀ := G.rightFinalWords F a b d
  let l₀ := G.leftFinalWords F a b d
  let w := G.rightFinalRows F a b d
  let f := G.leftFinalTag F a b
  let h := G.rightFinalTag F a b
  let g := (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
  have e (x : F.Slice a) : (r₀ x).map g = l₀ x := by
    unfold r₀ l₀ rightFinalWords leftFinalWords
    rw [List.map_map]
    rfl
  let c := fun x => ((congrArg (fold 𝒮 Zₐ A) (e x).symm).trans (std_fold_map A g (r₀ x)))
  let z := ((congrArg (fold 𝒮 Zₐ A) (congrArg (fun r => s.flatMap r) (funext e).symm)).trans
    (rows_relabel_obj A g r₀ s))
  have p₀ : rowsChart A l₀ s ≫ act 𝒮 Zₐ (fun x => eqToHom (c x)) s =
      eqToHom z ≫ rowsChart A' r₀ s := by
    have t := rowsChart_relabel_input A g r₀ s
    let u := fun x => eqToHom (congrArg (fold 𝒮 Zₐ A) (e x))
    let v := fun x => eqToHom (std_fold_map A g (r₀ x))
    let b := congrArg (fold 𝒮 Zₐ A) (congrArg (fun r => s.flatMap r) (funext e))
    have hh := rowsChart_rows_congr A e s
    have i (x : F.Slice a) : u x ≫ eqToHom (c x) = v x := by
      unfold u c v
      rw [eqToHom_trans]
    have i' : act 𝒮 Zₐ u s ≫ act 𝒮 Zₐ (fun x => eqToHom (c x)) s = act 𝒮 Zₐ v s :=
      (act_seq 𝒮 Zₐ u (fun x => eqToHom (c x)) s).trans (congrArg (fun f => act 𝒮 Zₐ f s) (funext i))
    let t' := congrArg (fun y => eqToHom b.symm ≫ y) t
    rw [← i', reassoc_of% hh] at t'
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at t'
    exact t'
  let lf := fun x => eqToHom (std_fold_map A (f x) (w x))
  let rf := fun x => eqToHom (std_fold_map A₁ (h x) (w x))
  let qL := G.leftFinalAttach F R L a b d hb hd
  let qR := G.rightFinalAttach F R L a b d hb hd
  let p := fun x => act 𝒮 Zₐ φ (r₀ x)
  have w₀ (x : F.Slice a) : qL x ≫ k x =
      act 𝒮 Zₐ (fun y => φ (h x y)) (w x) ≫ qR x := by
    let z := dependentAssoc_middle_whole R L P NR NL Q (V x) b' d'
      (fun y : G.TripleMid F x b => B x.val y.val)
      (fun y w => D x.val y.val w)
      (G.tripleMidWord F x b) ((G.tailInput F x.val x.property.1).terms b d)
      (G.tripleMidBeta F b x hb) (G.tripleMidGamma F R L b d x hd) (hl (V x))
    change _ ≫ k x = _
    unfold qL
    unfold leftFinalAttach
    simp only [Category.assoc]
    exact z
  have w₁ (x : F.Slice a) : (lf x ≫ qL x) ≫ k x = eqToHom (c x) ≫ p x ≫ (rf x ≫ qR x) := by
    have ee : lf x = eqToHom (c x) ≫ eqToHom (std_fold_map A' (h x) (w x)) := by
      unfold lf
      rw [eqToHom_trans]
    have hh := std_act_map A' (h x) φ (w x)
    change eqToHom (std_fold_map A' (h x) (w x)) ≫ act 𝒮 Zₐ (fun y => φ (h x y)) (w x) = p x ≫ rf x at hh
    rw [ee]
    simp only [Category.assoc]
    rw [w₀, reassoc_of% hh]
  have w₂ : act 𝒮 Zₐ (fun x => lf x ≫ qL x) s ≫ act 𝒮 Zₐ k s =
      act 𝒮 Zₐ (fun x => eqToHom (c x)) s ≫ act 𝒮 Zₐ p s ≫ act 𝒮 Zₐ (fun x => rf x ≫ qR x) s :=
    (act_seq 𝒮 Zₐ (fun x => lf x ≫ qL x) k s).trans
      ((congrArg (fun f => act 𝒮 Zₐ f s) (funext w₁)).trans
        ((act_seq 𝒮 Zₐ (fun x => eqToHom (c x)) (fun x => p x ≫ (rf x ≫ qR x)) s).symm.trans
          (congrArg (fun g => act 𝒮 Zₐ (fun x => eqToHom (c x)) s ≫ g)
            (act_seq 𝒮 Zₐ p (fun x => rf x ≫ qR x) s).symm)))
  have ha' := dependentAssoc_parent_cell R L P NR Q (V' a) b' d' V s (F.locOuter a ha)
  have hh' : act 𝒮 Zₐ φ r ≫ rowsChart A₁ r₀ s =
      rowsChart A' r₀ s ≫ act 𝒮 Zₐ p s := rowsChart_natural r₀ φ s
  apply heq_of_paste z (rfl : T.obj (V' a) (T.obj b' d') = _)
  rw [eqToHom_refl, Category.comp_id]
  unfold leftFinalSchedule rightFinalSchedule
  simp only [Category.assoc]
  rw [ha', reassoc_of% w₂, reassoc_of% p₀, reassoc_of% hh']

set_option backward.isDefEq.respectTransparency false in
theorem leftFinalWords_fibre :
    (F.slice a).flatMap (G.leftFinalWords F a b d) =
      wordFibre (dependentWord (dependentWord xs ys) (fun p => ws p.1 p.2))
        (origDepCarrier (G.leftInput F R L)) ((a,b),d) := by
  let p := G.leftInput F R L
  let M := G.leftBaseLeafWords F R L a b d
  let rows := G.leftMiddleSlice F R L a b
  let s := F.slice a
  have k := dependentSlice_word_raw p ((a,b),d)
  unfold dependentWord at k
  rw [List.map_flatMap] at k
  simp only [List.map_map] at k
  change (p.slice (a,b)).flatMap M = _ at k
  exact (((List.flatMap_assoc (l:=s) (f:=rows) (g:=M)).trans
    (congrArg (fun f => s.flatMap f) (funext (G.leftFinalWords_group F R L a b d)))).symm.trans
      (congrArg (List.flatMap M) (G.tripleMidRead_word F R L a b))).trans k

end LeftFinal

end OrderedThirdMap
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
