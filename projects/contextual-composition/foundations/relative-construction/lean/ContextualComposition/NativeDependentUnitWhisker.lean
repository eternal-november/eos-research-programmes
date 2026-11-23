module
public import ContextualComposition.NativeDependentLeftUnit
@[expose] public section

/-! The unit arrows may be whiskered through a surrounding dependent
accumulation, using exact raw unit-erasure and the original cells. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem wordAug_cell_heq {X : Type w} {Y : Type z} {I : C}
    {A : X → C} {B : Y → C} {xs : List X} {ys : List Y}
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (h : wordAug A xs a = wordAug B ys b) : HEq a b := by
  rw [wordAug_total, wordAug_total] at h
  let c := wordTotalPin A xs
  let d := wordTotalPin B ys
  have aux {F G : Family C} (p : totalFold F ⟶ I) (q : totalFold G ⟶ I)
      (h : totalAug F p = totalAug G q) : HEq p q := by
    have e : F = G := congrArg Aug.base h
    subst G
    have h' : HEq (totalAug F p).ε (totalAug F q).ε := by
      have eqAug (A B : Aug ℙ I) (e : A = B) : HEq A.ε B.ε := by subst B; rfl
      exact eqAug _ _ h
    let pp (j : Fin 1) := eqToHom (congrArg (fold 𝒮 Zₐ F.val) (fibreList_terminal F.n j)) ≫ p
    let qq (j : Fin 1) := eqToHom (congrArg (fold 𝒮 Zₐ F.val) (fibreList_terminal F.n j)) ≫ q
    have H : (Hom.mk (terminalCarrier F.n) pp : Hom ℙ F (terminalShape I)) =
        Hom.mk (terminalCarrier F.n) qq := eq_of_heq h'
    have k := congrFun (eq_of_heq (Hom.mk.inj H).2) (0 : Fin 1)
    let e₀ := congrArg (fold 𝒮 Zₐ F.val) (fibreList_terminal F.n (0 : Fin 1))
    change eqToHom e₀ ≫ p = eqToHom e₀ ≫ q at k
    exact heq_of_eq ((cancel_epi (eqToHom e₀)).mp k)
  have h₀ := aux (eqToHom c ≫ a) (eqToHom d ≫ b) h
  exact (hom_source_pin_heq c a).symm.trans (h₀.trans (hom_source_pin_heq d b))

set_option backward.isDefEq.respectTransparency false in
theorem wordAug_act_preserves_pullback {X : Type w} {Y : Type z} {I : C}
    {A B : Y → C} (g : X → Y) (xs : List X) (ys : List Y) (h : xs.map g = ys)
    (p : ∀ y, A y ⟶ B y) (a : fold 𝒮 Zₐ (A ∘ g) xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (ha : wordAug (A ∘ g) xs a = wordAug A ys (act 𝒮 Zₐ p ys ≫ b)) :
    let e := (std_fold_map B g xs).symm.trans (congrArg (fold 𝒮 Zₐ B) h)
    act 𝒮 Zₐ (fun x => p (g x)) xs ≫ eqToHom e ≫ b = a := by
  intro e
  exact wordAct_preservation_read g xs ys h p (wordAug_cell_heq _ _ ha)
    (hom_source_pin_heq e b) rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
