module
public import ContextualComposition.NativeFubiniJointRegroup
public import ContextualComposition.NativeIndependentAssocNaturality
@[expose] public section

/-! An address and coefficient trace of the actual independent associator,
through the independently constructed native product presentations. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {T : Bi (coeff (C:=C))}

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem frame_tensor_read_cast {X Y : Type u} {A B : Family C}
    {V : X → C} {W : Y → C} {xs : List X} {ys : List Y}
    (F : RawSingletonFrame X A) (G : RawSingletonFrame Y B)
    (e : A = wordFamily V xs) (d : B = wordFamily W ys)
    (ef : ∀ j, F.read j = xs[Fin.cast (congrArg Family.n e) j])
    (df : ∀ j, G.read j = ys[Fin.cast (congrArg Family.n d) j])
    (i : Fin (independentFamily T A B).n) :
    let h := (congrArg₂ (independentFamily T) e d).trans (independentFamily_word (T:=T) V W xs ys)
    (F.tensor T G).read i = (xs.product ys)[Fin.cast (congrArg Family.n h) i] := by
  subst A; subst B
  intro h
  let u := readPair xs ys
  let a := independentWord (wordFamily V xs) (wordFamily W ys)
  let t := a[i]
  have k := rawWordFrame_read_cast (crossLabel T V W) u a (xs.product ys) (readPair_word xs ys) i
  change (F.read t.1,G.read t.2) = _
  rw [ef, df]
  exact k

variable {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (P : TensorPrimitive T)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))
variable {X Y W : Type u} (A : X → C) (B : Y → C) (D : W → C)
variable (xs : List X) (ys : List Y) (ws : List W)
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (q : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)
variable (r : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D ws ⟶ I)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3300000 in
theorem independentAssocIso_trace (hx : xs.Nodup) (hy : ys.Nodup) (hw : ws.Nodup) :
    let F := (((rawWordFrame A xs hx).tensor T (rawWordFrame B ys hy)).tensor T (rawWordFrame D ws hw)).relabel
      (tripleRetag (X:=X) (Y:=Y) (W:=W)) tripleRetag.injective (assocLeftLabels T A (fun _ => B) (fun _ _ => D) ∘ tripleRetag.symm) (fun _ => rfl)
    let G := (rawWordFrame A xs hx).tensor T ((rawWordFrame B ys hy).tensor T (rawWordFrame D ws hw))
    RawSingletonTrace F G (fun z => P.assoc (A z.1) (B z.2.1) (D z.2.2))
      (independentAssocIso R L J P NR NL Q U A B D xs ys ws p q r hl hr ι
        (nodup_product_word hx (nodup_product_word hy hw))).hom.native := by
  intro F G
  let M := assocLeftLabels T A (fun _ => B) (fun _ _ => D)
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let H := M ∘ g.symm
  let K := crossLabel T A (crossLabel T B D)
  let u := (xs.product ys).product ws
  let w := xs.product (ys.product ws)
  let hn := nodup_product_word hx (nodup_product_word hy hw)
  let Fx := rawWordFrame A xs hx
  let Fy := rawWordFrame B ys hy
  let Fw := rawWordFrame D ws hw
  let F₀ := (Fx.tensor T Fy).tensor T Fw
  let exy := independentFamily_word (T:=T) A B xs ys
  let eyw := independentFamily_word (T:=T) B D ys ws
  let el := (congrArg₂ (independentFamily T) exy
    (rfl : wordFamily D ws = wordFamily D ws)).trans (independentFamily_word (T:=T) (crossLabel T A B) D (xs.product ys) ws)
  let er := (congrArg₂ (independentFamily T)
    (rfl : wordFamily A xs = wordFamily A xs) eyw).trans (independentFamily_word (T:=T) A (crossLabel T B D) xs (ys.product ws))
  let re := tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)
  let e := wordFamily_read_eq H g u w re
  let v := independentAssocIso R L J P NR NL Q U A B D xs ys ws p q r hl hr ι hn
  let α (z : X × Y × W) : H z ⟶ K z := P.assoc (A z.1) (B z.2.1) (D z.2.2)
  have h := independentAssocIso_pointwise_heq R L J P NR NL Q U A B D xs ys ws p q r hl hr ι hn
  have elread (i : Fin _ ) : F₀.read i = u[Fin.cast (congrArg Family.n el) i] :=
    frame_tensor_read_cast (Fx.tensor T Fy) Fw exy rfl
      (fun j => frame_tensor_read_cast Fx Fy rfl rfl (fun _ => rfl) (fun _ => rfl) j)
      (fun _ => rfl) i
  have hF (i : Fin _) : F.read i = w[Fin.cast (congrArg Family.n (el.trans e)) i] := by
    change g (F₀.read i) = _
    rw [elread]
    exact rawWordFrame_read_cast H g u w re (Fin.cast (congrArg Family.n el) i)
  have hG (i : Fin _) : G.read i = w[Fin.cast (congrArg Family.n er) i] :=
    frame_tensor_read_cast Fx (Fy.tensor T Fw) rfl eyw (fun _ => rfl)
      (fun j => frame_tensor_read_cast Fy Fw rfl rfl (fun _ => rfl) (fun _ => rfl) j) i
  exact (wordPointwise_trace w hn α).retarget (el.trans e).symm er.symm h.symm
    (rawFrame_read_reverse F (rawWordFrame H w hn) (el.trans e) hF)
    (rawFrame_read_reverse G (rawWordFrame K w hn) er hG) (fun _ => HEq.rfl)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
