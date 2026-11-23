module
public import ContextualComposition.NativeFubiniTreeWhisker
@[expose] public section

/-! The actual separate tree operation also has a direct ordered
word presentation in its nested raw addresses. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)

namespace DependentFubiniTree

def word : (a : DependentFubiniTree I) → List a.Address
  | .unit => [PUnit.unit]
  | .leaf A => dependentWord A.xs A.us
  | .fork a b => (word a).product (word b)

theorem word_nodup : (a : DependentFubiniTree I) → a.word.Nodup
  | .unit => (by decide : ([PUnit.unit] : List PUnit.{u+1}).Nodup)
  | .leaf A => dependentWord_nodup A.xs_unique A.us_unique
  | .fork a b => nodup_product_word (word_nodup a) (word_nodup b)

def wordCell : (a : DependentFubiniTree I) → (fold 𝒮 Zₐ (separateCoeff (T:=T) a) a.word ⟶ I)
  | .unit => (ρ_ I).hom
  | .leaf A => OrderedDependentAugData.accCell R L J A
  | .fork a b => rectangularWordAugCell R L (J.ρ I)
    (separateCoeff (T:=T) a) (separateCoeff (T:=T) b) a.word b.word (wordCell a) (wordCell b)

set_option backward.isDefEq.respectTransparency false in
theorem separate_word_eq : (a : DependentFubiniTree I) →
    a.separate R L J = wordAug (separateCoeff (T:=T) a) a.word (a.wordCell R L J)
  | .unit => unit_wordAug
  | .leaf _ => rfl
  | .fork a b =>
    (congrArg₂ (independentAug R L (J.ρ I)) (separate_word_eq a) (separate_word_eq b)).trans
      (independentAug_ordered_eq R L (J.ρ I)
          (separateCoeff (T:=T) a) (separateCoeff (T:=T) b) a.word b.word (a.wordCell R L J) (b.wordCell R L J))

set_option backward.isDefEq.respectTransparency false in
theorem separateFrame_word :
    (a : DependentFubiniTree I) → (i : Fin (a.separate R L J).base.n) →
    (a.separateTagFrame R L J).read i = a.word[Fin.cast (congrArg (fun A : Aug ℙ I => A.base.n)
      (a.separate_word_eq R L J)) i]
  | .unit, _ => @Subsingleton.elim PUnit.{u+1} inferInstance _ _
  | .leaf _, _ => rfl
  | .fork a b, i =>
    frame_tensor_read_cast (a.separateTagFrame R L J) (b.separateTagFrame R L J)
      (congrArg Aug.base (a.separate_word_eq R L J)) (congrArg Aug.base (b.separate_word_eq R L J))
      (separateFrame_word a) (separateFrame_word b) i

end DependentFubiniTree

section Read
variable {X Y : Type u} {A : X → C} {B : Y → C} {xs : List X} {ys : List Y}
variable (f : X ≃ Y) (e : xs.map f = ys) (φ : ∀ x, A x ≅ B (f x))
variable (a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (b : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)

set_option backward.isDefEq.respectTransparency false in
def WordAugReadComparison.ofOrderPreserving
    (h : act 𝒮 Zₐ (fun x => (φ x).hom) xs ≫
      eqToHom ((std_fold_map B f xs).symm.trans (congrArg (fold 𝒮 Zₐ B) e)) ≫ b = a) :
    WordAugReadComparison A B xs ys a b := by
  let p := (std_fold_map B f xs).symm.trans (congrArg (fold 𝒮 Zₐ B) e)
  let q := eqToHom p ≫ b
  let t := AddressOrder.ident xs
  have h' : AddressOrder.mapSum additiveStructure A t ≫ act 𝒮 Zₐ (fun x => (φ x).hom) xs ≫ q = a := by
    change 𝟙 _ ≫ (act 𝒮 Zₐ (fun x => (φ x).hom) xs ≫ q) = a
    rw [Category.id_comp]
    exact h
  exact WordAugReadComparison.ofScalarOrder f id xs ys xs xs (List.map_id xs) e φ a b a q
    HEq.rfl (hom_source_pin_heq p b).symm t h'

end Read
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
