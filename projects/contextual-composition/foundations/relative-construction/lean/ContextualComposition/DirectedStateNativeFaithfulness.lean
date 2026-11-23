module

public import ContextualComposition.DirectedStateUniversal
public import ContextualComposition.StateWindowCategory

/-! Faithfulness for any strict Cat-valued state bifunctor. Surround the process by arbitrary incoming and outgoing state maps. A slide changes the factorization of this surrounding state path; strict functoriality identifies the two resulting observations. At the identity window native maps are recovered. No individual action is required to be faithful. -/

@[expose] public section
namespace ContextualComposition.DirectedStateNativeFaithfulness

open CategoryTheory Opposite DirectedStateBalance StateWindowCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w d

section Transport
variable {C : Type*} [Category* C] {A B D A' B' D' : C}

def IsCast (f : A ⟶ B) : Prop := ∃ e : A=B, f=eqToHom e
def Conjugate (f : A ⟶ B) (g : A' ⟶ B') : Prop :=
  ∃ (a : A=A') (b : B=B'), f ≫ eqToHom b = eqToHom a ≫ g

theorem IsCast.comp {f : A ⟶ B} {g : B ⟶ D} : IsCast f → IsCast g → IsCast (f ≫ g) := by
  rintro ⟨rfl,rfl⟩ ⟨rfl,rfl⟩; exact ⟨rfl,Category.id_comp _⟩
theorem IsCast.unique {f g : A ⟶ B} : IsCast f → IsCast g → f=g := by rintro ⟨h,rfl⟩ ⟨_,rfl⟩; rfl
theorem IsCast.map {E : Type*} [Category* E] (H : C ⥤ E) {f : A ⟶ B} : IsCast f → IsCast (H.map f) := by
  rintro ⟨rfl,rfl⟩; exact ⟨rfl,H.map_id _⟩

theorem Conjugate.refl (f : A ⟶ B) : Conjugate f f := ⟨rfl,rfl,(Category.comp_id _).trans (Category.id_comp _).symm⟩
theorem Conjugate.eq {f g : A ⟶ B} : Conjugate f g → f=g := by
  rintro ⟨a,b,e⟩; simpa only [eqToHom_refl,Category.comp_id,Category.id_comp] using e
theorem Conjugate.trans {f : A ⟶ B} {g : A' ⟶ B'} {h : D ⟶ D'} :
    Conjugate f g → Conjugate g h → Conjugate f h := by
  rintro ⟨rfl,rfl,e⟩ ⟨rfl,rfl,e'⟩
  simp only [eqToHom_refl,Category.comp_id,Category.id_comp] at e e'
  exact (e.trans e') ▸ Conjugate.refl _
theorem Conjugate.symm {f : A ⟶ B} {g : A' ⟶ B'} : Conjugate f g → Conjugate g f := by
  rintro ⟨rfl,rfl,e⟩; simp only [eqToHom_refl,Category.comp_id,Category.id_comp] at e
  exact e ▸ Conjugate.refl _
theorem Conjugate.trimRight (f : A ⟶ B) {g : B ⟶ D} : IsCast g → Conjugate (f ≫ g) f := by
  rintro ⟨rfl,rfl⟩; simpa only [eqToHom_refl,Category.comp_id] using Conjugate.refl f
theorem Conjugate.trimLeft {f : A ⟶ B} (g : B ⟶ D) : IsCast f → Conjugate (f ≫ g) g := by
  rintro ⟨rfl,rfl⟩; simpa only [eqToHom_refl,Category.id_comp] using Conjugate.refl g
theorem Conjugate.actions {E : Type*} [Category* E] {H K : E ⥤ C} (e : H=K) {x y : E} (f : x ⟶ y) :
    Conjugate (H.map f) (K.map f) := by subst K; exact Conjugate.refl _
end Transport

variable {S : Type u} [Category.{v} S] (G : Sᵒᵖ × S ⥤ Cat.{w,d}) (a b : S)
abbrev F := strict G
abbrev W := Object a b (atPair (F G) a b)

theorem strictComp {i i' i'' j j' j'' : S} (h : i' ⟶ i) (h' : i'' ⟶ i') (k : j ⟶ j') (k' : j' ⟶ j'') :
    action (F G) (h' ≫ h) (k ≫ k') = action (F G) h k ⋙ action (F G) h' k' :=
  congrArg Cat.Hom.toFunctor (G.map_comp (pairMap h k) (pairMap h' k'))

def observe (i : S) (x : atPair (F G) i i) : W G a b :=
  ⟨i,fun p => (action (F G) p.1 p.2).obj x⟩

theorem unchanged {i : S} (p q : Window a b i) (l : p.1 ≫ 𝟙 i = q.1) (r : 𝟙 i ≫ q.2 = p.2) : p=q :=
  Prod.ext ((Category.comp_id _).symm.trans l) (r.symm.trans (Category.id_comp _))

def localMap {i : S} {x y : atPair (F G) i i} (α : x ⟶ y) : observe G a b i x ⟶ observe G a b i y where
  state := 𝟙 i
  cell p q l r := (action (F G) p.1 p.2).map α ≫ eqToHom (congrArg (observe G a b i y).observe (unchanged a b p q l r))

theorem local_source {i : S} {x y : atPair (F G) i i} (α : x ⟶ y) (p q : Window a b i) (l r) :
    Conjugate ((localMap G a b α).cell p q l r) ((action (F G) p.1 p.2).map α) :=
  Conjugate.trimRight _ ⟨_,rfl⟩

theorem local_target {i : S} {x y : atPair (F G) i i} (α : x ⟶ y) (p q : Window a b i) (l r) :
    Conjugate ((localMap G a b α).cell p q l r) ((action (F G) q.1 q.2).map α) := by
  obtain rfl := unchanged a b p q l r
  exact local_source _ _ _ _ _ _ _ _

theorem local_cast {i : S} {x y : atPair (F G) i i} {α : x ⟶ y} (e : IsCast α) (p q : Window a b i) (l r) :
    IsCast ((localMap G a b α).cell p q l r) := (e.map _).comp ⟨_,rfl⟩

def fiber (i : S) : atPair (F G) i i ⥤ W G a b where
  obj := observe G a b i
  map := localMap G a b
  map_id x := Hom.ext rfl (fun p q l r l' r' => (local_cast G a b ⟨rfl,rfl⟩ p q l r).unique
    ⟨congrArg (observe G a b i x).observe (unchanged a b p q l' r'),rfl⟩)
  map_comp {x y z} α β := by
    apply Hom.ext (Category.id_comp _).symm
    intro p q l r l' r'
    have eq : p=q := unchanged a b p q l r
    subst q
    change (action (F G) p.1 p.2).map (α ≫ β) ≫ eqToHom _ = _
    rw [eqToHom_refl,Category.comp_id,Functor.map_comp]
    let m : Window a b i := (p.1 ≫ 𝟙 i,𝟙 i ≫ p.2)
    have hm : m=p := Prod.ext (Category.comp_id _) (Category.id_comp _)
    have aux (j : Window a b i) (e : j=p) (l₁ r₁ l₂ r₂) :
        (action (F G) p.1 p.2).map α ≫ (action (F G) p.1 p.2).map β =
        (localMap G a b α).cell p j l₁ r₁ ≫ (localMap G a b β).cell j p l₂ r₂ := by
      subst j
      change _ = (_ ≫ eqToHom _) ≫ (_ ≫ eqToHom _)
      simp only [eqToHom_refl,Category.comp_id]
    exact aux m hm _ _ _ _

theorem common_action {i j : S} (h : i ⟶ j) (p : Window a b i) (q : Window a b j)
    (l : p.1 ≫ h = q.1) (r : h ≫ q.2 = p.2) :
    action (F G) h (𝟙 i) ⋙ action (F G) p.1 p.2 = action (F G) (𝟙 j) h ⋙ action (F G) q.1 q.2 := by
  rw [← strictComp,← strictComp,Category.id_comp,Category.comp_id,l,r]

def slip {i j : S} (h : i ⟶ j) (x : atPair (F G) j i) :
    (fiber G a b i).obj ((action (F G) h (𝟙 i)).obj x) ⟶ (fiber G a b j).obj ((action (F G) (𝟙 j) h).obj x) where
  state := h
  cell p q l r := eqToHom (congrArg (fun K => K.obj x) (common_action G a b h p q l r))

def Structural {U V : W G a b} (f : U ⟶ V) : Prop := ∀ p q l r, IsCast (f.cell p q l r)

theorem structural_native {i : S} {x y : atPair (F G) i i} {α : x ⟶ y} (h : IsCast α) :
    Structural G a b (localMap G a b α) := local_cast G a b h

theorem structural_comp {U V W : W G a b} {f : U ⟶ V} {g : V ⟶ W} (hf : Structural G a b f) (hg : Structural G a b g) :
    Structural G a b (f ≫ g) := fun p q l r =>
  (hf p _ rfl ((Category.assoc _ _ _).symm.trans r)).comp (hg _ q ((Category.assoc _ _ _).trans l) rfl)

theorem structural_eq {U V : W G a b} {f g : U ⟶ V} (h : f.state=g.state) (hf : Structural G a b f) (hg : Structural G a b g) :
    f=g := Hom.ext h (fun p q l r l' r' => (hf p q l r).unique (hg p q l' r'))

theorem structural_slide {i j : S} (h : i ⟶ j) (x : atPair (F G) j i) : Structural G a b (slip G a b h x) :=
  fun p q l r => ⟨congrArg (fun H => H.obj x) (common_action G a b h p q l r),rfl⟩

theorem slide_natural {i j : S} (h : i ⟶ j) {x y : atPair (F G) j i} (f : x ⟶ y) :
    localMap G a b ((action (F G) h (𝟙 i)).map f) ≫ slip G a b h y =
    slip G a b h x ≫ localMap G a b ((action (F G) (𝟙 j) h).map f) := by
  apply Hom.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  intro p q l r l' r'
  change p.1 ≫ (𝟙 i ≫ h) = q.1 at l
  change (𝟙 i ≫ h) ≫ q.2 = p.2 at r
  have hl : p.1 ≫ h = q.1 := (congrArg (p.1 ≫ ·) (Category.id_comp h).symm).trans l
  have hr : h ≫ q.2 = p.2 := (congrArg (· ≫ q.2) (Category.id_comp h).symm).trans r
  let m := (p.1 ≫ 𝟙 i,h ≫ q.2)
  let n := (p.1 ≫ h,𝟙 j ≫ q.2)
  have l₁ : m.1 ≫ h = q.1 := (congrArg (· ≫ h) (Category.comp_id p.1)).trans hl
  have r₁ : 𝟙 i ≫ m.2 = p.2 := by simpa [m] using hr
  have l₂ : n.1 ≫ 𝟙 j = q.1 := by simpa [n] using hl
  have r₂ : h ≫ n.2 = p.2 := by simpa [n] using hr
  let A := (action (F G) h (𝟙 i)).map f
  let B := (action (F G) (𝟙 j) h).map f
  have left := (Conjugate.trimRight ((localMap G a b A).cell p m rfl r₁) (structural_slide G a b h y m q l₁ rfl)).trans
    (local_source G a b A p m rfl r₁)
  have right := (Conjugate.trimLeft ((localMap G a b B).cell n q l₂ rfl) (structural_slide G a b h x p n rfl r₂)).trans
    (local_target G a b B n q l₂ rfl)
  exact (left.trans ((Conjugate.actions (common_action G a b h p q hl hr) f).trans right.symm)).eq

private theorem homCast {C D : Cat.{w,d}} {f g : C ⟶ D} (h : f=g) (x : C) :
    IsCast ((Cat.Hom.toNatIso (eqToIso h)).hom.app x) := by subst g; exact ⟨rfl,rfl⟩
private theorem invCast {C D : Cat.{w,d}} {f g : C ⟶ D} (h : f=g) (x : C) :
    IsCast ((Cat.Hom.toNatIso (eqToIso h)).inv.app x) := by subst g; exact ⟨rfl,rfl⟩
private theorem homEqApp {C D : Type*} [Category* C] [Category* D] {f g : C ⥤ D} (h : f=g) (x : C) :
    IsCast ((eqToIso h).hom.app x) := by subst g; exact ⟨rfl,rfl⟩
private theorem invEqApp {C D : Type*} [Category* C] [Category* D] {f g : C ⥤ D} (h : f=g) (x : C) :
    IsCast ((eqToIso h).inv.app x) := by subst g; exact ⟨rfl,rfl⟩

theorem structural_pre {i j k : S} (h : i ⟶ j) (g : j ⟶ k) (x : atPair (F G) k i) :
    IsCast ((preComp (F G) h g).hom.app x) := by
  apply IsCast.comp (homEqApp _ x)
  exact homCast (G.map_comp (pairMap g (𝟙 i)) (pairMap h (𝟙 i))) x

theorem structural_post {i j k : S} (h : i ⟶ j) (g : j ⟶ k) (x : atPair (F G) k i) :
    IsCast ((postComp (F G) h g).inv.app x) := by
  apply IsCast.comp _ (invEqApp _ x)
  exact invCast (G.map_comp (pairMap (𝟙 k) h) (pairMap (𝟙 k) g)) x

theorem structural_middle {i j k : S} (h : i ⟶ j) (g : j ⟶ k) (x : atPair (F G) k i) :
    IsCast ((middle (F G) h g).hom.app x) := by
  apply IsCast.comp (invCast (G.map_comp (pairMap g (𝟙 i)) (pairMap (𝟙 j) h)) x)
  apply IsCast.comp (homEqApp _ x)
  exact homCast (G.map_comp (pairMap (𝟙 k) h) (pairMap g (𝟙 j))) x

def detectorData : DirectedStateBalance.Cocone (F G) (W G a b) where
  fiber := fiber G a b
  bal h := ⟨slip G a b h,fun _ _ f => slide_natural G a b h f⟩
  unit x := structural_eq G a b rfl (structural_slide G a b _ x)
    (fun p q l r => ⟨congrArg (observe G a b _ _).observe (unchanged a b p q l r),rfl⟩)
  comp h g x := by
    apply structural_eq G a b
    · change h ≫ g = 𝟙 _ ≫ h ≫ 𝟙 _ ≫ g ≫ 𝟙 _
      simp
    · exact structural_slide G a b _ x
    · apply structural_comp G a b (structural_native G a b (structural_pre G h g x))
      apply structural_comp G a b (structural_slide G a b _ _)
      apply structural_comp G a b (structural_native G a b (structural_middle G h g x))
      exact structural_comp G a b (structural_slide G a b _ _) (structural_native G a b (structural_post G h g x))

/-- The detector at the unchanged state recovers the actual native arrow. This uses no faithfulness of either variable action. -/
theorem faithful (i : S) : (insertion (F G) i).Faithful where
  map_injective {x y} α β e := by
    let E := detectorData G i i
    have eq : localMap G i i α = localMap G i i β := (E.descend_generator (.native α)).symm.trans
      ((congrArg E.descend.map e).trans (E.descend_generator (.native β)))
    let p : Window i i i := (𝟙 i,𝟙 i)
    have both : (action (F G) (𝟙 i) (𝟙 i)).map α = (action (F G) (𝟙 i) (𝟙 i)).map β := by
      have he {f g : observe G i i i x ⟶ observe G i i i y} (k : f=g) (hf : f.state=𝟙 i) (hg : g.state=𝟙 i) :
          f.cell p p (by rw [hf]; exact Category.comp_id _) (by rw [hf]; exact Category.id_comp _) =
          g.cell p p (by rw [hg]; exact Category.comp_id _) (by rw [hg]; exact Category.id_comp _) := by subst g; rfl
      exact ((Category.comp_id _).symm.trans (he eq rfl rfl)).trans (Category.comp_id _)
    have iF : action (F G) (𝟙 i) (𝟙 i) = 𝟭 _ := congrArg Cat.Hom.toFunctor (G.map_id (op i,i))
    exact ((Conjugate.actions iF α).symm.trans (both ▸ (Conjugate.actions iF β))).eq

end ContextualComposition.DirectedStateNativeFaithfulness
