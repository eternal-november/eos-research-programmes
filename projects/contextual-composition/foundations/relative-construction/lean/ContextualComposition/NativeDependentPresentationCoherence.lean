module
public import ContextualComposition.NativeDependentPresentation
@[expose] public section

/-! Coherence of successive additive-presentation changes at fixed raw
dependent addresses. Inverse charts are actual circuit inverses. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem orderSumIso_seq {W : Type u} (A : W → C) {xs ys zs : List W}
    (e : AddressOrder W xs ys) (f : AddressOrder W ys zs) :
    orderSumIso A (.seq e f) = (orderSumIso A e) ≪≫ (orderSumIso A f) := by
  apply Iso.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem orderSumIso_ident {W : Type u} (A : W → C) (xs : List W) :
    orderSumIso A (.ident xs) = Iso.refl _ := by
  apply Iso.ext
  rfl

variable {I : C}

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentAugData.reorder_seq (D : OrderedDependentAugData I)
    {ys zs : List D.X} {vs ws : D.X → List D.U}
    (e : AddressOrder D.X D.xs ys) (d : ∀ x, AddressOrder D.U (D.us x) (vs x))
    (f : AddressOrder D.X ys zs) (g : ∀ x, AddressOrder D.U (vs x) (ws x)) :
    (D.reorder e d).reorder f g = D.reorder (.seq e f) (fun x => .seq (d x) (g x)) := by
  have h : ∀ {W : Type u} (A : W → C) {xs ys zs : List W}
      (e : AddressOrder W xs ys) (f : AddressOrder W ys zs) (a : fold 𝒮 Zₐ A xs ⟶ I),
      (orderSumIso A f).inv ≫ (orderSumIso A e).inv ≫ a = (orderSumIso A (.seq e f)).inv ≫ a := by
    intros
    rw [orderSumIso_seq]
    exact (Category.assoc _ _ _).symm
  cases D
  simp only [OrderedDependentAugData.reorder]
  congr 1
  · exact h _ e f _
  · funext x
    exact h _ (d x) (g x) _

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentAugData.reorder_ident (D : OrderedDependentAugData I) :
    D.reorder (.ident _) (fun _ => .ident _) = D := by
  cases D
  simp [OrderedDependentAugData.reorder, orderSumIso_ident]

set_option backward.isDefEq.respectTransparency false in
theorem wordReorderIso_comp {W : Type u} (A : W → C) {xs ys zs : List W}
    (e : AddressOrder W xs ys) (f : AddressOrder W ys zs) (g : AddressOrder W xs zs) (hx : xs.Nodup) :
    (wordReorderIso A e hx).hom.comp (wordReorderIso A f (e.perm.nodup hx)).hom =
      (wordReorderIso A g hx).hom := by
  let hy := e.perm.nodup hx
  let hz := g.perm.nodup hx
  let p := wordReindex_trace A A e hx hy (fun w => Iso.refl (A w))
  let q := wordReindex_trace A A f hy hz (fun w => Iso.refl (A w))
  let r := wordReindex_trace A A g hx hz (fun w => Iso.refl (A w))
  exact RawSingletonTrace.eq (p.comp q) r (fun _ => Category.id_comp _)

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentAugData.accumulatedReorderIso_comp (D : OrderedDependentAugData I)
    {ys zs : List D.X} {vs ws : D.X → List D.U}
    (e : AddressOrder D.X D.xs ys) (d : ∀ x, AddressOrder D.U (D.us x) (vs x))
    (f : AddressOrder D.X ys zs) (g : ∀ x, AddressOrder D.U (vs x) (ws x)) :
    HEq ((D.accumulatedReorderIso e d R L hl hr J N NL).hom.comp
      ((D.reorder e d).accumulatedReorderIso f g R L hl hr J N NL).hom)
      (D.accumulatedReorderIso (.seq e f) (fun x => .seq (d x) (g x)) R L hl hr J N NL).hom := by
  apply augmentHom_heq_native_of_eq _ _ rfl (congrArg (OrderedDependentAugData.accumulate R L J)
    (D.reorder_seq e d f g))
  exact heq_of_eq (wordReorderIso_comp (dependentLabels (T:=T) D.V D.A)
    (dependentOrder e d) (dependentOrder f g) (dependentOrder (.seq e f) (fun x => .seq (d x) (g x)))
    (dependentWord_nodup D.xs_unique D.us_unique))

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentAugData.accumulatedReorderIso_ident (D : OrderedDependentAugData I) :
    HEq (D.accumulatedReorderIso (.ident _) (fun _ => .ident _) R L hl hr J N NL).hom
      (AugHom.ident (D.accumulate R L J)) := by
  apply augmentHom_heq_native_of_eq _ _ rfl (congrArg (OrderedDependentAugData.accumulate R L J)
    D.reorder_ident)
  let A := dependentLabels (T:=T) D.V D.A
  let o := dependentOrder (.ident D.xs) (fun x => .ident (D.us x))
  let n := dependentWord_nodup D.xs_unique D.us_unique
  exact heq_of_eq (RawSingletonTrace.eq (wordReindex_trace A A o n n (fun z => Iso.refl (A z)))
    (RawSingletonTrace.ident (rawWordFrame A _ n)) (fun _ => rfl))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
