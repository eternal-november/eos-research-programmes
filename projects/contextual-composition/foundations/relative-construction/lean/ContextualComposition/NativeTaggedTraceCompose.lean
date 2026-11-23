module
public import ContextualComposition.NativeFubiniTreeTagValues
@[expose] public section

/-! Composition and inversion of exact native singleton traces across
different raw address alphabets. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w x y z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem RawSingletonTrace.inverse {Ω : Type w} {I : C} {A B : Aug ℙ I}
    {F : RawSingletonFrame Ω A.base} {G : RawSingletonFrame Ω B.base}
    (φ : ∀ x, F.label x ≅ G.label x) (e : NativeAugmentedIso A B)
    (t : RawSingletonTrace F G (fun x => (φ x).hom) e.hom.native) :
    RawSingletonTrace G F (fun x => (φ x).inv) e.inv.native := by
  obtain ⟨r,p,h,hr,hp⟩ := t
  let c (i : Fin A.base.n) : B.base.val (r i) ⟶ A.base.val i :=
    eqToHom ((G.at_read (r i)).trans (congrArg G.label (hr i))) ≫ (φ (F.read i)).inv ≫ eqToHom (F.at_read i).symm
  let f := nativeSingletonMap r.symm c
  have hf : RawSingletonTrace G F (fun x => (φ x).inv) f := by
    refine ⟨r.symm, c, rfl, RawSingletonTrace.symm_read r hr, ?_⟩
    intro i
    unfold c
    exact (hom_source_pin_heq _ _).trans (hom_target_pin_heq _ _)
  have hp₀ : RawSingletonTrace F G (fun x => (φ x).hom) e.hom.native := ⟨r,p,h,hr,hp⟩
  have hg : e.hom.native.comp f = Hom.ident A.base :=
    (hp₀.comp hf).eq (RawSingletonTrace.ident F)
      (fun i => (φ (F.read i)).hom_inv_id)
  have k := congrArg AugHom.native e.inv_hom
  change e.inv.native.comp e.hom.native = Hom.ident B.base at k
  have hh : f = e.inv.native := by
    calc
      f = (Hom.ident B.base).comp f := (Hom.ident_comp _).symm
      _ = e.inv.native.comp (e.hom.native.comp f) := by rw [← Hom.comp_assoc, k]
      _ = e.inv.native := by rw [hg, Hom.comp_ident]
  exact hh ▸ hf

variable {Ω : Type w} {Θ : Type x} {Ξ : Type y}
variable {A B D : Family C}

/-- A trace records the actual singleton aggregation, the raw address
equivalence, and the actual coefficient isomorphism. -/
def NativeAddressTrace (F : RawSingletonFrame Ω A) (G : RawSingletonFrame Θ B)
    (e : Ω ≃ Θ) (p : ∀ x, F.label x ≅ G.label (e x)) (f : Hom ℙ A B) : Prop :=
  RawSingletonTrace F
    (G.relabel e.symm e.symm.injective (G.label ∘ e) (fun x => congrArg G.label (e.apply_symm_apply x).symm))
    (fun x => (p x).hom) f

set_option backward.isDefEq.respectTransparency false in
theorem NativeAddressTrace.ident (F : RawSingletonFrame Ω A) :
    NativeAddressTrace F F (Equiv.refl Ω) (fun x => Iso.refl (F.label x)) (Hom.ident A) :=
  (RawSingletonTrace.ident F).changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)

set_option backward.isDefEq.respectTransparency false in
theorem NativeAddressTrace.comp
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Θ B} {H : RawSingletonFrame Ξ D}
    {e : Ω ≃ Θ} {d : Θ ≃ Ξ}
    {p : ∀ x, F.label x ≅ G.label (e x)} {q : ∀ x, G.label x ≅ H.label (d x)}
    {f : Hom ℙ A B} {g : Hom ℙ B D}
    (hf : NativeAddressTrace F G e p f) (hg : NativeAddressTrace G H d q g) :
    NativeAddressTrace F H (e.trans d) (fun x => (p x).trans (q (e x))) (f.comp g) := by
  let H₀ := H.relabel d.symm d.symm.injective (H.label ∘ d) (fun x => congrArg H.label (d.apply_symm_apply x).symm)
  let G₀ := G.relabel e.symm e.symm.injective (G.label ∘ e) (fun x => congrArg G.label (e.apply_symm_apply x).symm)
  have ht : RawSingletonTrace G H₀ (fun x => (q x).hom) g := hg
  have hu : RawSingletonTrace F G₀ (fun x => (p x).hom) f := hf
  have hg₀ := ht.relabel
    e.symm e.symm.injective (G.label ∘ e) (H.label ∘ d ∘ e)
    (fun x => congrArg G.label (e.apply_symm_apply x).symm)
    (fun x => congrArg (H.label ∘ d) (e.apply_symm_apply x).symm)
    (fun x => (q (e x)).hom) (fun x => by
      have h : e (e.symm x) = x := e.apply_symm_apply x
      change HEq (q x).hom (q (e (e.symm x))).hom
      rw [h])
  exact (hu.comp hg₀).changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)

set_option backward.isDefEq.respectTransparency false in
theorem NativeAddressTrace.reverse {I : C} {A B : Aug ℙ I}
    {F : RawSingletonFrame Ω A.base} {G : RawSingletonFrame Θ B.base}
    {e : Ω ≃ Θ} {p : ∀ x, F.label x ≅ G.label (e x)}
    (η : NativeAugmentedIso A B) (h : NativeAddressTrace F G e p η.hom.native) :
    NativeAddressTrace G F e.symm
      (fun y => eqToIso (congrArg G.label (e.apply_symm_apply y).symm) ≪≫ (p (e.symm y)).symm)
      η.inv.native := by
  let G₀ := G.relabel e.symm e.symm.injective (G.label ∘ e)
    (fun x => congrArg G.label (e.apply_symm_apply x).symm)
  let q := fun y => eqToIso (congrArg G.label (e.apply_symm_apply y).symm) ≪≫ (p (e.symm y)).symm
  have ht : RawSingletonTrace F G₀ (fun x => (p x).hom) η.hom.native := h
  have h₀ : RawSingletonTrace G₀ F (fun x => (p x).inv) η.inv.native :=
    RawSingletonTrace.inverse (F:=F) (G:=G₀) p η ht
  have h₁ := h₀.relabel e e.injective G.label (F.label ∘ e.symm)
    (fun _ => rfl) (fun x => congrArg F.label (e.symm_apply_apply x).symm)
    (fun y => (q y).hom) (fun x => by
      unfold q
      have e₀ := e.symm_apply_apply x
      have H : HEq (p x).inv (p (e.symm (e x))).inv := by rw [e₀]
      exact H.trans (hom_source_pin_heq (congrArg G.label (e.apply_symm_apply (e x)).symm) ((p (e.symm (e x))).inv)).symm)
  exact h₁.changeFrame (fun x => e.apply_symm_apply (G.read x)) (fun _ => rfl) (fun _ => HEq.rfl)

set_option backward.isDefEq.respectTransparency false in
def biTensorIso {T : Bi (coeff (C:=C))} {a b c d : C} (p : a ≅ b) (q : c ≅ d) :
    T.obj a c ≅ T.obj b d where
  hom := T.map p.hom q.hom
  inv := T.map p.inv q.inv
  hom_inv_id := by
    change (coeff (C:=C)).seq _ _ = (coeff (C:=C)).id _
    rw [← T.map_seq]
    exact (congrArg₂ T.map p.hom_inv_id q.hom_inv_id).trans (T.map_id _ _)
  inv_hom_id := by
    change (coeff (C:=C)).seq _ _ = (coeff (C:=C)).id _
    rw [← T.map_seq]
    exact (congrArg₂ T.map p.inv_hom_id q.inv_hom_id).trans (T.map_id _ _)

set_option backward.isDefEq.respectTransparency false in
theorem NativeAddressTrace.tensor {Λ : Type z} {A₀ B₀ : Family C} {T : Bi (coeff (C:=C))}
    (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
    (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Θ B}
    {H : RawSingletonFrame Ξ A₀} {K : RawSingletonFrame Λ B₀}
    {e : Ω ≃ Θ} {d : Ξ ≃ Λ}
    {p : ∀ x, F.label x ≅ G.label (e x)} {q : ∀ x, H.label x ≅ K.label (d x)}
    {f : Hom ℙ A B} {g : Hom ℙ A₀ B₀}
    (hf : NativeAddressTrace F G e p f) (hg : NativeAddressTrace H K d q g) :
    NativeAddressTrace (F.tensor T H) (G.tensor T K) (e.prodCongr d)
      (fun x => biTensorIso (T:=T) (p x.1) (q x.2))
      (independentNativeWordMap T f g R L) :=
  (RawSingletonTrace.tensor R L hl hr hf hg).changeFrame
    (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)

set_option backward.isDefEq.respectTransparency false in
theorem NativeAddressTrace.eq
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Θ B}
    {e : Ω ≃ Θ} {p q : ∀ x, F.label x ≅ G.label (e x)} {f g : Hom ℙ A B}
    (hf : NativeAddressTrace F G e p f) (hg : NativeAddressTrace F G e q g)
    (h : ∀ x, (p x).hom = (q x).hom) : f = g :=
  RawSingletonTrace.eq hf hg (fun j => h (e.symm (G.read j)))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
