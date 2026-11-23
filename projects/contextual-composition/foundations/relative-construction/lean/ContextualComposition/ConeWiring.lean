module

public import ContextualComposition.CouplingChains
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! Explicit cone operations, substitution, symmetric actions, and their product representability boundary. Native supplied effects form the example category. -/

@[expose] public section

namespace ContextualComposition.ConeWiring

open CategoryTheory CategoryTheory.Limits CouplingPullbacks AllCouplings CouplingChains
universe u v w
variable {C : Type u} [Category.{v} C] {I : Type*} {J : I → Type*}

abbrev Wiring (Q : C) (P : I → C) := ∀ i, Q ⟶ P i

def unary (Q : C) : Wiring Q (fun _ : Unit => Q) := fun _ => 𝟙 Q
def nullary (Q : C) : Wiring Q (fun i : Empty => i.elim) := fun i => i.elim

def subst {P : I → C} {Q : C} {R : ∀ i, J i → C} (a : Wiring Q P) (b : ∀ i, Wiring (P i) (R i)) :
    Wiring Q (fun k : Σ i, J i => R k.1 k.2) := fun k => a k.1 ≫ b k.1 k.2

theorem unit_outer {Q : C} {P : I → C} (a : Wiring Q P) (i : I) :
    subst (unary Q) (fun _ => a) ⟨(),i⟩ = a i := Category.id_comp _

theorem unit_inner {Q : C} {P : I → C} (a : Wiring Q P) (i : I) :
    subst a (fun k => unary (P k)) ⟨i,()⟩ = a i := Category.comp_id _

theorem substitute_assoc {K : ∀ i, J i → Type*} {Q : C} {P : I → C} {R : ∀ i, J i → C}
    {S : ∀ i j, K i j → C} (a : Wiring Q P) (b : ∀ i, Wiring (P i) (R i))
    (c : ∀ i j, Wiring (R i j) (S i j)) (i j k) :
    subst (subst a b) (fun ij => c ij.1 ij.2) ⟨⟨i,j⟩,k⟩ =
    subst a (fun i => subst (b i) (c i)) ⟨i,⟨j,k⟩⟩ := Category.assoc _ _ _

def permute {Q : C} {P : I → C} {I' : Type*} (e : I' ≃ I) (a : Wiring Q P) :
    Wiring Q (P ∘ e) := fun j => a (e j)

theorem permute_comp {Q : C} {P : I → C} {I' I'' : Type*} (e : I' ≃ I) (d : I'' ≃ I') (a : Wiring Q P) :
    permute d (permute e a) = permute (d.trans e) a := rfl

theorem permute_subst {Q : C} {P : I → C} {R : ∀ i, J i → C} {I' : Type*} {J' : I' → Type*}
    (e : I' ≃ I) (d : ∀ i, J' i ≃ J (e i)) (a : Wiring Q P) (b : ∀ i, Wiring (P i) (R i))
    (i : I') (j : J' i) :
    subst (permute e a) (fun i => permute (d i) (b (e i))) ⟨i,j⟩ =
    subst a b ⟨e i,d i j⟩ := rfl

variable {D : Type*} [Category* D] (G : C ⥤ D)

def transport {Q : C} {P : I → C} (a : Wiring Q P) : Wiring (G.obj Q) (G.obj ∘ P) :=
  fun i => G.map (a i)

theorem transport_subst {Q : C} {P : I → C} {R : ∀ i, J i → C} (a : Wiring Q P) (b : ∀ i, Wiring (P i) (R i)) (k) :
    transport G (subst a b) k = subst (transport G a) (fun i => transport G (b i)) k := G.map_comp _ _

theorem transport_unit (Q : C) : transport G (unary Q) () = unary (G.obj Q) () := G.map_id _

theorem transport_permute {Q : C} {P : I → C} {I' : Type*} (e : I' ≃ I) (a : Wiring Q P) :
    transport G (permute e a) = permute e (transport G a) := rfl

/-- Representability in the opposite unary category is natural in the candidate joint source. -/
structure Represents (R : C) (P : I → C) where
  equivalence : ∀ Q : C, (Q ⟶ R) ≃ Wiring Q P
  natural : ∀ {Q Q'} (h : Q' ⟶ Q) (f : Q ⟶ R) i, equivalence Q' (h ≫ f) i = h ≫ equivalence Q f i

def Represents.fan {R : C} {P : I → C} (d : Represents R P) : Fan P := Fan.mk R (d.equivalence R (𝟙 R))

def Represents.isLimit {R : C} {P : I → C} (d : Represents R P) : IsLimit d.fan := by
  have fac {Q : C} (f : Q ⟶ R) (i : I) : f ≫ d.fan.proj i = d.equivalence Q f i := by
    simpa [fan] using (d.natural f (𝟙 R) i).symm
  refine Fan.IsLimit.mk d.fan (fun s => (d.equivalence s.pt).symm s.proj) ?_ ?_
  · intro s i
    exact (fac _ i).trans (congrFun ((d.equivalence s.pt).apply_symm_apply s.proj) i)
  · intro s f eq
    apply (d.equivalence s.pt).injective
    funext i
    exact ((fac f i).symm.trans (eq i)).trans (congrFun ((d.equivalence s.pt).apply_symm_apply s.proj).symm i)

def ofProduct {P : I → C} (s : Fan P) (h : IsLimit s) : Represents s.pt P where
  equivalence Q := {
    toFun := fun f i => f ≫ s.proj i
    invFun := fun p => h.lift (Fan.mk Q p)
    left_inv f := h.uniq (Fan.mk Q (fun i => f ≫ s.proj i)) f (fun _ => rfl) |>.symm
    right_inv p := funext fun i => h.fac (Fan.mk Q p) ⟨i⟩ }
  natural _ _ _ := Category.assoc _ _ _

theorem representable_iff_product (P : I → C) :
    (∃ R : C, Nonempty (Represents R P)) ↔ HasProduct P := by
  constructor
  · rintro ⟨_,⟨r⟩⟩; exact ⟨⟨r.fan,r.isLimit⟩⟩
  · intro h
    let := h
    exact ⟨_,⟨ofProduct _ (limit.isLimit (Discrete.functor P))⟩⟩

section Effects

variable (F : Type u ⥤ Type u)

instance : Category (Effect F) where
  Hom P Q := StateMap F P Q
  id P := ⟨id,push_id F P.law⟩
  comp f g := ⟨g.run ∘ f.run, (push_push F _ _ _).symm.trans ((congrArg (push F g.run) f.preserves).trans g.preserves)⟩

abbrev Context (A : Type u) := A → Effect F

/-- The pointwise category of effect-preserving maps between raw context fibres. -/
instance (A : Type u) : Category (Context F A) where
  Hom P Q := ∀ a, P a ⟶ Q a
  id _ _ := 𝟙 _
  comp f g a := f a ≫ g a

def reindex {A B : Type u} (s : A → B) : Context F B ⥤ Context F A where
  obj P := P ∘ s
  map f a := f (s a)

theorem reindex_comp {A B D : Type u} (s : A → B) (t : B → D) :
    reindex F t ⋙ reindex F s = reindex F (t ∘ s) := rfl

theorem reindex_id (A : Type u) : reindex F (id : A → A) = 𝟭 _ := rfl

end Effects
end ContextualComposition.ConeWiring
