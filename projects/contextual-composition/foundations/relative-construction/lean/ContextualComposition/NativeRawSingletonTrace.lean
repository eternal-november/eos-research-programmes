module
public import ContextualComposition.NativeIndependentAssociator
@[expose] public section

/-! Structural native comparisons can change the enumeration of raw
occurrences. Compare composites through the actual singleton fibres,
not by assuming that the carrier functor is faithful. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)

structure RawSingletonFrame (Ω : Type w) (A : Family C) where
  read : Fin A.n → Ω
  label : Ω → C
  at_read : ∀ i, A.val i = label (read i)
  injective : Function.Injective read

def RawSingletonTrace {Ω : Type w} {A B : Family C}
    (F : RawSingletonFrame Ω A) (G : RawSingletonFrame Ω B)
    (p : ∀ x, F.label x ⟶ G.label x) (f : Hom ℙ A B) : Prop :=
  ∃ (e : Fin A.n ≃ Fin B.n) (c : ∀ j, A.val (e.symm j) ⟶ B.val j),
    f = nativeSingletonMap e c ∧ (∀ i, G.read (e i) = F.read i) ∧
      (∀ j, HEq (c j) (p (G.read j)))

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem RawSingletonTrace.symm_read {Ω : Type w} {A B : Family C}
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Ω B}
    (e : Fin A.n ≃ Fin B.n) (h : ∀ i, G.read (e i) = F.read i) (j : Fin B.n) :
    F.read (e.symm j) = G.read j := by
  simpa only [Equiv.apply_symm_apply] using (h (e.symm j)).symm

set_option backward.isDefEq.respectTransparency false in
theorem RawSingletonTrace.comp {Ω : Type w} {A B D : Family C}
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Ω B} {H : RawSingletonFrame Ω D}
    {p : ∀ x, F.label x ⟶ G.label x} {q : ∀ x, G.label x ⟶ H.label x}
    {f : Hom ℙ A B} {g : Hom ℙ B D}
    (hf : RawSingletonTrace F G p f) (hg : RawSingletonTrace G H q g) :
    RawSingletonTrace F H (fun x => p x ≫ q x) (f.comp g) := by
  obtain ⟨e,a,rfl,he,ha⟩ := hf
  obtain ⟨d,b,rfl,hd,hb⟩ := hg
  refine ⟨e.trans d, fun j => a (d.symm j) ≫ b j, nativeSingletonMap_comp e d a b, ?_, ?_⟩
  · exact fun i => (hd (e i)).trans (he i)
  · intro j
    have h₀ := RawSingletonTrace.symm_read d hd j
    have h₁ := RawSingletonTrace.symm_read e he (d.symm j)
    have s := (F.at_read (e.symm (d.symm j))).trans (congrArg F.label (h₁.trans h₀))
    have t := (G.at_read (d.symm j)).trans (congrArg G.label h₀)
    have u := H.at_read j
    have h (x y : Ω) (e : x = y) : HEq (p x) (p y) := by subst y; rfl
    exact structural_seq_heq (K:=coeff (C:=C)) s t u
      ((ha (d.symm j)).trans (h _ _ h₀)) (hb j)

theorem RawSingletonTrace.eq {Ω : Type w} {A B : Family C}
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Ω B}
    {p q : ∀ x, F.label x ⟶ G.label x} {f g : Hom ℙ A B}
    (hf : RawSingletonTrace F G p f) (hg : RawSingletonTrace F G q g)
    (h : ∀ j, p (G.read j) = q (G.read j)) : f = g := by
  obtain ⟨e,a,rfl,he,ha⟩ := hf
  obtain ⟨d,b,rfl,hd,hb⟩ := hg
  apply nativeSingletonMap_congr
  · intro i
    exact G.injective ((he i).trans (hd i).symm)
  · intro j
    exact (ha j).trans ((heq_of_eq (h j)).trans (hb j).symm)

def rawWordFrame {Ω : Type u} (A : Ω → C) (xs : List Ω) (hn : xs.Nodup) :
    RawSingletonFrame Ω (wordFamily A xs) where
  read j := xs[j]
  label := A
  at_read _ := rfl
  injective := by
    intro i j h
    exact Fin.ext (hn.getElem_inj.mp h)

set_option backward.isDefEq.respectTransparency false in
theorem wordReindex_trace {Ω : Type u} (A B : Ω → C) {xs ys : List Ω}
    (p : AddressOrder Ω xs ys) (hx : xs.Nodup) (hy : ys.Nodup) (φ : ∀ x, A x ≅ B x) :
    RawSingletonTrace (rawWordFrame A xs hx) (rawWordFrame B ys hy) (fun x => (φ x).hom)
      (nativeReindex (wordEquiv p.perm hx) (wordComparisonCells A B p hx φ)) := by
  let e := wordEquiv p.perm hx
  refine ⟨e, fun j => (wordComparisonCells A B p hx φ j).hom, rfl, ?_, ?_⟩
  · intro i
    exact wordEquiv_get p.perm hx i
  · intro j
    change HEq
      (eqToHom (congrArg A (wordEquiv_get_symm p.perm hx j)) ≫ (φ ys[j]).hom)
      ((φ ys[j]).hom)
    exact hom_source_pin_heq _ _


local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
theorem wordAugIso_trace {Ω : Type u} {I : C} (A B : Ω → C) {xs ys : List Ω}
    (p : AddressOrder Ω xs ys) (hx : xs.Nodup) (hy : ys.Nodup) (φ : ∀ x, A x ≅ B x)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (hp : AddressOrder.mapSum additiveStructure A p ≫ act 𝒮 Zₐ (fun x => (φ x).hom) ys ≫ b = a) :
    RawSingletonTrace (rawWordFrame A xs hx) (rawWordFrame B ys hy) (fun x => (φ x).hom)
      (wordAugIso A B p hx φ a b hp).hom.native :=
  wordReindex_trace A B p hx hy φ

def RawSingletonFrame.relabel {Ω : Type w} {Ω' : Type*} {A : Family C}
    (F : RawSingletonFrame Ω A) (f : Ω → Ω') (h : Function.Injective f)
    (V : Ω' → C) (e : ∀ x, F.label x = V (f x)) : RawSingletonFrame Ω' A where
  read j := f (F.read j)
  label := V
  at_read j := (F.at_read j).trans (e (F.read j))
  injective := h.comp F.injective

set_option backward.isDefEq.respectTransparency false in
theorem RawSingletonTrace.relabel {Ω : Type w} {Ω' : Type*} {A B : Family C}
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Ω B}
    (f : Ω → Ω') (h : Function.Injective f)
    (V W : Ω' → C) (e : ∀ x, F.label x = V (f x)) (d : ∀ x, G.label x = W (f x))
    {p : ∀ x, F.label x ⟶ G.label x} (q : ∀ x, V x ⟶ W x) {v : Hom ℙ A B}
    (hv : RawSingletonTrace F G p v) (hq : ∀ x, HEq (p x) (q (f x))) :
    RawSingletonTrace (F.relabel f h V e) (G.relabel f h W d) q v := by
  obtain ⟨k,c,rfl,hk,hc⟩ := hv
  exact ⟨k,c,rfl,fun i => congrArg f (hk i),fun j => (hc j).trans (hq (G.read j))⟩

set_option backward.isDefEq.respectTransparency false in
theorem RawSingletonTrace.changeFrame {Ω : Type w} {A B : Family C}
    {F F' : RawSingletonFrame Ω A} {G G' : RawSingletonFrame Ω B}
    {p : ∀ x, F.label x ⟶ G.label x} {q : ∀ x, F'.label x ⟶ G'.label x} {f : Hom ℙ A B}
    (hf : RawSingletonTrace F G p f)
    (hF : ∀ i, F.read i = F'.read i) (hG : ∀ i, G.read i = G'.read i)
    (hq : ∀ x, HEq (p x) (q x)) :
    RawSingletonTrace F' G' q f := by
  obtain ⟨e,c,rfl,he,hc⟩ := hf
  refine ⟨e,c,rfl,?_,?_⟩
  · exact fun i => (hG (e i)).symm.trans ((he i).trans (hF i))
  · intro j
    have h {a b : Ω} (e : a = b) : HEq (q a) (q b) := by subst b; rfl
    exact (hc j).trans ((hq (G.read j)).trans (h (hG j)))


set_option backward.isDefEq.respectTransparency false in
theorem native_hom_eq_of_cell_heq {A B : Family C} (p q : Hom ℙ A B) (h : p.addr = q.addr)
    (k : ∀ j, HEq (p.cell j) (q.cell j)) : p = q := by
  have e := nativeHom_heq_of_positions p q rfl rfl
    (fun i => congrFun h i) (fun j => k j)
  exact eq_of_heq e

theorem nativeSingletonMap_cell_heq {A B : Family C}
    (e : Fin A.n ≃ Fin B.n) (p : ∀ j, A.val (e.symm j) ⟶ B.val j) (j : Fin B.n) :
    HEq ((nativeSingletonMap e p).cell j) ((ρ_ (A.val (e.symm j))).hom ≫ p j) := by
  let d : standardPushObj e A.val j = (A.val (e.symm j) ⊗ Zₐ) :=
    congrArg (fold 𝒮 Zₐ A.val) (equiv_fibreList e j)
  change HEq ((eqToHom d ≫ (ρ_ (A.val (e.symm j))).hom) ≫ p j) _
  rw [Category.assoc]
  exact hom_source_pin_heq d _


set_option backward.isDefEq.respectTransparency false in
theorem RawSingletonTrace.retarget {Ω : Type w} {A B A' B' : Family C}
    {F : RawSingletonFrame Ω A} {G : RawSingletonFrame Ω B}
    {F' : RawSingletonFrame Ω A'} {G' : RawSingletonFrame Ω B'}
    {p : ∀ x, F.label x ⟶ G.label x} {q : ∀ x, F'.label x ⟶ G'.label x}
    {f : Hom ℙ A B} {g : Hom ℙ A' B'}
    (hf : RawSingletonTrace F G p f) (e : A = A') (d : B = B') (h : HEq f g)
    (a : ∀ i, F.read i = F'.read (Fin.cast (congrArg Family.n e) i))
    (b : ∀ i, G.read i = G'.read (Fin.cast (congrArg Family.n d) i))
    (c : ∀ x, HEq (p x) (q x)) :
    RawSingletonTrace F' G' q g := by
  subst A'; subst B'
  have u : f = g := eq_of_heq h
  subst g
  exact hf.changeFrame a b c

set_option backward.isDefEq.respectTransparency false in
theorem RawSingletonTrace.ident {Ω : Type w} {A : Family C} (F : RawSingletonFrame Ω A) :
    RawSingletonTrace F F (fun x => 𝟙 (F.label x)) (Hom.ident A) := by
  refine ⟨Equiv.refl _, fun j => 𝟙 (A.val j), (nativeSingletonMap_ident A).symm, fun _ => rfl, ?_⟩
  intro j
  exact structural_id_heq (K:=coeff (C:=C)) (F.at_read j)

set_option backward.isDefEq.respectTransparency false in
omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem rawWordFrame_read_cast {X : Type w} {Y : Type z} (A : Y → C)
    (f : X → Y) (xs : List X) (ys : List Y) (h : xs.map f = ys)
    (i : Fin (wordFamily (A ∘ f) xs).n) :
    f xs[i] = ys[Fin.cast (congrArg Family.n (wordFamily_read_eq A f xs ys h)) i] :=
  retag_word_get f xs h i


omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem rawFrame_read_reverse {Ω : Type w} {A B : Family C}
    (F : RawSingletonFrame Ω A) (G : RawSingletonFrame Ω B) (e : A = B)
    (h : ∀ i, F.read i = G.read (Fin.cast (congrArg Family.n e) i)) (j : Fin B.n) :
    G.read j = F.read (Fin.cast (congrArg Family.n e.symm) j) := by
  subst B
  exact (h j).symm

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
