module
public import ContextualComposition.NativeIndependentAssociator
@[expose] public section

/-! The original independent native map in caller-selected raw word
coordinates, without unfolding an opaque whole source cell into any
component maps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable {X Y X' Y' : Type u} [DecidableEq X'] [DecidableEq Y']
variable {xs : List X} {ys : List Y} {xs' : List X'} {ys' : List Y'}
variable (f : X → X') (g : Y → Y')
variable (A : X → C) (B : Y → C) (A' : X' → C) (B' : Y' → C)
variable (p : ∀ x ∈ xs', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C)
  A (wordFibre xs f x) ⟶ A' x)
variable (q : ∀ y ∈ ys', fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C)
  B (wordFibre ys g y) ⟶ B' y)
variable (hf : ∀ a ∈ xs, f a ∈ xs') (hg : ∀ a ∈ ys, g a ∈ ys')
variable (hx' : xs'.Nodup) (hy' : ys'.Nodup)

include hf hg in
omit [DecidableEq X'] [DecidableEq Y'] in
theorem wordProduct_support :
    ∀ t ∈ xs.product ys, Prod.map f g t ∈ xs'.product ys' := by
  intro t ht
  have e := (dependentWord_mem xs (fun _ => ys) t).mp ht
  exact (dependentWord_mem xs' (fun _ => ys') _).mpr ⟨hf _ e.1,hg _ e.2⟩

def wordProductCell (t : X' × Y') (ht : t ∈ xs'.product ys') :
    fold 𝒮 Zₐ (crossLabel T A B) (wordFibre (xs.product ys) (Prod.map f g) t) ⟶ crossLabel T A' B' t :=
  let a := wordFibre xs f t.1
  let b := wordFibre ys g t.2
  let H := (dependentWord_mem xs' (fun _ => ys') t).mp ht
  eqToHom (congrArg (fold 𝒮 Zₐ (crossLabel T A B)) (product_word_fibre xs ys f g t)) ≫
    rectWordChart (crossLabel T A B) a b ≫ independentCell R L A B a b (p _ H.1) (q _ H.2)

noncomputable def wordProductMap :
    Hom ℙ (wordFamily (crossLabel T A B) (xs.product ys)) (wordFamily (crossLabel T A' B') (xs'.product ys')) :=
  wordNativeMap (Prod.map f g) (wordProduct_support f g hf hg) (nodup_product_word hx' hy')
    (crossLabel T A B) (crossLabel T A' B')
    (fun j => wordProductCell R L f g A B A' B' p q (xs'.product ys')[j] (List.getElem_mem _))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2100000 in
theorem wordProductMap_original_heq :
    HEq (independentNativeWordMap T
      (wordNativeMap f hf hx' A A' (fun j => p xs'[j] (List.getElem_mem _)))
      (wordNativeMap g hg hy' B B' (fun j => q ys'[j] (List.getElem_mem _))) R L)
      (wordProductMap R L f g A B A' B' p q hf hg hx' hy') := by
  let e := wordNativeMap f hf hx' A A' (fun j => p xs'[j] (List.getElem_mem _))
  let d := wordNativeMap g hg hy' B B' (fun j => q ys'[j] (List.getElem_mem _))
  let V := wordFamily A xs
  let W := wordFamily B ys
  let V' := wordFamily A' xs'
  let W' := wordFamily B' ys'
  let w := independentWord V W
  let v := independentWord V' W'
  let a := xs.product ys
  let b := xs'.product ys'
  let u := readPair xs ys
  let t := readPair xs' ys'
  let F := Prod.map e.addr d.addr
  let G := Prod.map f g
  let k := fun j : Fin v.length => independentWordCell T e d R L v[j]
  let z := fun j : Fin b.length => wordProductCell R L f g A B A' B' p q b[j] (List.getElem_mem _)
  have hu : w.map u = a := readPair_word xs ys
  have ht : v.map t = b := readPair_word xs' ys'
  have hc (i : Fin V.n × Fin W.n) : t (F i) = G (u i) :=
    congrArg₂ Prod.mk (wordCarrier_get f hf hx' i.1) (wordCarrier_get g hg hy' i.2)
  unfold wordProductMap independentNativeWordMap
  change HEq (wordNativeMap F (independent_word_support e d) (independentWord_nodup V' W')
    (crossLabel T A B ∘ u) (crossLabel T A' B' ∘ t) k)
    (wordNativeMap G (wordProduct_support f g hf hg) (nodup_product_word hx' hy')
      (crossLabel T A B) (crossLabel T A' B') z)
  apply readWordNativeMap_heq _ _ u t F G (independent_word_support e d) _ _ _ hu ht (fun i _ => hc i)
  intro j
  let i := v[j]
  let x := xs'[i.1]
  let y := ys'[i.2]
  let h : (x,y) ∈ b := (dependentWord_mem xs' (fun _ => ys') _).mpr ⟨List.getElem_mem _,List.getElem_mem _⟩
  let j' := Fin.cast ((List.length_map t).symm.trans (congrArg List.length ht)) j
  have e₀ := wordCarrier_fibre f hf hx' i.1
  have d₀ := wordCarrier_fibre g hg hy' i.2
  have e₁ : HEq (e.cell i.1) (p x (List.getElem_mem _)) := hom_source_pin_heq _ _
  have d₁ : HEq (d.cell i.2) (q y (List.getElem_mem _)) := hom_source_pin_heq _ _
  have H := rectangleCell_map_heq' R L A B (fun (j : Fin xs.length) => xs[j]) (fun (j : Fin ys.length) => ys[j])
    (fibreList e.addr i.1) (fibreList d.addr i.2) e₀ d₀ e₁ d₁
  have k₀ : HEq (k j) (wordProductCell R L f g A B A' B' p q (x,y) h) :=
    (hom_source_pin_heq _ _).trans (H.trans (hom_source_pin_heq _ _).symm)
  have hread : (x,y) = b[j'] := retag_word_get t v ht j
  have he {i i' : X' × Y'} (h : i = i') (hs : i ∈ b) (hs' : i' ∈ b) :
      HEq (wordProductCell R L f g A B A' B' p q i hs) (wordProductCell R L f g A B A' B' p q i' hs') := by
    subst i'
    rfl
  exact k₀.trans (he hread h (List.getElem_mem _))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
