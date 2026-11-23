module

public import ContextualComposition.OrthogonalCornerCategory

/-! Intrinsic hypotheses for the orthogonal recognition of Štěpán,
Definitions 2.7.7, 3.3.9, 3.3.19 and 3.3.24. The right-identity comparison
can also be read as an opposite horizontal comparison between the midpoints. -/

@[expose] public section
namespace ContextualComposition.OrthogonalCornerRecognition
open CategoryTheory StrictCornerRecognition OrthogonalCornerCategory
universe u v w s
variable {O : Type u} [Category.{v} O] [Category.{w} (HObj O)]
variable (S : Faces.{u,v,w,s} O)
variable {a b c d i j k : O}

/-- The second bicartesian lifting condition factors a square through a
prescribed suffix of its top edge by horizontal pasting on the left. -/
structure HorizontalExtension {m : Horiz a b} {e : a ⟶ i} {v : b ⟶ c} {n : Horiz i c}
    (l : S.Sq m e v n) {r : Horiz d a} {w : d ⟶ j} {g : Horiz j c} (h : S.Sq (r ≫ m) w v g) where
  middle : Horiz j i
  factor : middle ≫ n = g
  face : S.Sq r w e middle
  pastes : HEq (S.hp face l) h

abbrev Basic (θ : i ⟶ j) (ψ : Horiz j i) := S.Sq (𝟙 _) θ (𝟙 i) ψ

structure Intrinsic where
  filled : Filled S
  horizontal_factors : ∀ {a b c d i j : O} {m : Horiz a b} {e : a ⟶ i} {v : b ⟶ c} {n : Horiz i c}
    (l : S.Sq m e v n) {r : Horiz d a} {w : d ⟶ j} {g : Horiz j c} (h : S.Sq (r ≫ m) w v g),
    Unique (HorizontalExtension S l h)
  horizontal_invariance : ∀ {a b c d : O} (g : (⟨a⟩ : HObj O) ≅ ⟨b⟩) (h : (⟨c⟩ : HObj O) ≅ ⟨d⟩)
    (v : b ⟶ d), Unique (Σ e : a ⟶ c, S.Sq g.hom e v h.hom)
  vertical_invariance : ∀ {a b c d : O} (e : a ≅ c) (v : b ≅ d) (n : Horiz c d),
    Unique (Σ m : Horiz a b, S.Sq m e.hom v.hom n)
  joint_monic : ∀ {a i j b : O} (e : a ⟶ i) (m : Horiz i b) {θ θ' : i ⟶ j} {ψ ψ' : Horiz j i},
    Basic S θ ψ → Basic S θ' ψ' → e ≫ θ = e ≫ θ' → ψ ≫ m = ψ' ≫ m → θ = θ' ∧ ψ = ψ'
  vertical_unit : ∀ {a b c d : O} {m : Horiz a b} {v : a ⟶ c} {w : b ⟶ d} {n : Horiz c d}
    (h : S.Sq m v w n), HEq (S.vp h (S.idV n)) h

variable (I : Intrinsic S)

/-- The two directed edges of the basic square compare the two boundaries
of a bottom-left corner. -/
structure Link (p q : Corner a b) where
  θ : p.mid ⟶ q.mid
  ψ : Horiz q.mid p.mid
  first : p.e ≫ θ = q.e
  second : ψ ≫ p.m = q.m
  basic : Basic S θ ψ

def StepLink {p q : Corner a b} (f : Step S p q) : Link S p q := by
  let h : S.Sq (𝟙 _ ≫ p.m) f.mid (𝟙 b) q.m := (Category.id_comp p.m).symm ▸ f.face
  let t := (I.horizontal_factors (S.idV p.m) h).default
  exact ⟨f.mid,t.middle,f.left_eq,t.factor,t.face⟩

def Link.toStep {p q : Corner a b} (t : Link S p q) : Step S p q where
  mid := t.θ
  left_eq := t.first
  face := by simpa [t.second] using S.hp t.basic (S.idV p.m)

def basicComp {θ : i ⟶ j} {θ' : j ⟶ k} {ψ : Horiz j i} {ψ' : Horiz k j}
    (h : Basic S θ ψ) (h' : Basic S θ' ψ') : Basic S (θ ≫ θ') (ψ' ≫ ψ) := by
  have l : S.Sq ψ θ' (𝟙 i) (ψ' ≫ ψ) := by simpa using S.hp h' (S.idV ψ)
  simpa [Basic] using S.vp h l

include I in
theorem flat {m : Horiz a b} {e : a ⟶ i} {v : b ⟶ c} {n : Horiz i c} :
    Subsingleton (S.Sq m e v n) := by
  constructor
  intro l h
  let hh : S.Sq m e (v ≫ 𝟙 c) n := cast (congrArg (fun k => S.Sq m e k n) (Category.comp_id v).symm) h
  let t := (I.filled.opcartesian l hh).default
  let p : Corner a c := ⟨i,e,n⟩
  let base : Step S p p := ⟨t.middle,t.factor,t.face⟩
  let z := StepLink S I base
  have hθ : t.middle = 𝟙 i := (I.joint_monic e n z.basic (S.idV (𝟙 _))
    (z.first.trans (Category.comp_id e).symm) (z.second.trans (Category.id_comp n).symm)).1
  have β : HEq t.face (S.idV n) := by
    let k := I.vertical_invariance (Iso.refl i) (Iso.refl c) n
    let face : S.Sq n (𝟙 i) (𝟙 c) n := cast (congrArg (fun k => S.Sq n k (𝟙 c) n) hθ) t.face
    have q := (k.uniq ⟨n,face⟩).trans (k.uniq ⟨n,S.idV n⟩).symm
    have q' : face = S.idV n := eq_of_heq (Sigma.mk.inj q).2
    have hf : HEq face t.face := cast_heq _ _
    exact hf.symm.trans (heq_of_eq q')
  have paste : HEq (S.vp l t.face) (S.vp l (S.idV n)) := by congr 1
  have hh' : HEq hh h := cast_heq _ _
  exact eq_of_heq ((I.vertical_unit l).symm.trans (paste.symm.trans (t.pastes.trans hh')))

abbrev V (e : a ⟶ b) := mk S (vert e)
abbrev H (m : Horiz a b) := mk S (horiz m)

theorem v_then_corner (e : a ⟶ b) (p : Corner b c) :
    compose S I.filled (V S e) (mk S p) = mk S ⟨p.mid,e ≫ p.e,p.m⟩ := by
  change postHorizontal S (postVertical S I.filled (mk S (vert e)) p.e) p.m = _
  rw [postVertical_mk S I.filled (vert e) (S.idH p.e)]
  change mk S ⟨_,e ≫ p.e, 𝟙 _ ≫ p.m⟩ = _
  rw [Category.id_comp]

theorem corner_then_h (p : Corner a b) (m : Horiz b c) :
    compose S I.filled (mk S p) (H S m) = mk S ⟨p.mid,p.e,p.m ≫ m⟩ := by
  change postHorizontal S (postVertical S I.filled (mk S p) (𝟙 b)) m = _
  rw [postV_id]
  rfl

/-- A map between two factorizations in the intrinsic corner category.
The midpoint may itself be any equivalence class of corners. -/
structure Diagonal (p q : Corner a b) where
  map : Ar S p.mid q.mid
  first : compose S I.filled (V S p.e) map = V S q.e
  second : compose S I.filled map (H S q.m) = H S p.m

def fromStep {p q : Corner a b} (t : Step S p q) : Diagonal S I p q where
  map := V S t.mid
  first := by rw [v_then_corner]; change mk S ⟨_,p.e ≫ t.mid,𝟙 _⟩ = _; rw [t.left_eq]; rfl
  second := by
    rw [corner_then_h]
    apply (eq_iff_step S I.filled _ _).mpr
    exact ⟨⟨(t.symm S I.filled).mid, (t.midIso S I.filled).hom_inv_id,
      by simpa [vert,horiz] using (t.symm S I.filled).face⟩⟩

theorem diagonal_unique {p q : Corner a b} (t : Step S p q) (x : Diagonal S I p q) :
    x.map = V S t.mid := by
  obtain ⟨x,h₁,h₂⟩ := x
  induction x using Quot.ind with
  | _ r =>
    change compose S I.filled (V S p.e) (mk S r) = V S q.e at h₁
    change compose S I.filled (mk S r) (H S q.m) = H S p.m at h₂
    rw [v_then_corner] at h₁
    rw [corner_then_h] at h₂
    obtain ⟨l⟩ := (eq_iff_step S I.filled _ _).mp h₁
    obtain ⟨z⟩ := (eq_iff_step S I.filled _ _).mp h₂
    let l₁ := StepLink S I l
    let l₂ := StepLink S I z
    let h := StepLink S I t
    have e₁ : (p.e ≫ r.e) ≫ l₁.θ = q.e := l₁.first
    have m₁ : l₁.ψ ≫ r.m = 𝟙 _ := l₁.second
    have e₂ : r.e ≫ l₂.θ = 𝟙 _ := l₂.first
    have m₂ : l₂.ψ ≫ (r.m ≫ q.m) = p.m := l₂.second
    have eq := I.joint_monic (p.e ≫ r.e) (r.m ≫ q.m) l₁.basic (basicComp S l₂.basic h.basic)
      (by erw [e₁, Category.assoc p.e, ← Category.assoc r.e, e₂, Category.id_comp, h.first])
      (by erw [Category.assoc h.ψ, m₂, h.second, ← Category.assoc l₁.ψ, m₁, Category.id_comp])
    have fit : r.e ≫ l₁.θ = t.mid := by erw [eq.1, ← Category.assoc, e₂, Category.id_comp]; rfl
    apply (eq_iff_step S I.filled r (vert t.mid)).mpr
    exact ⟨⟨l₁.θ, fit, l.face⟩⟩

@[instance_reducible] noncomputable def uniqueDiagonal (p q : Corner a b) (e : mk S p = mk S q) :
    Unique (Diagonal S I p q) := by
  let t := ((eq_iff_step S I.filled p q).mp e).some
  exact ⟨⟨fromStep S I t⟩, fun x => by
    have h := diagonal_unique S I t x
    cases x
    congr⟩

include I in
theorem vertical_injective {a b : O} : Function.Injective (V S : (a ⟶ b) → Ar S a b) := by
  intro e f h
  obtain ⟨t⟩ := (eq_iff_step S I.filled (vert e) (vert f)).mp h
  let k := I.horizontal_invariance (Iso.refl (⟨b⟩ : HObj O)) (Iso.refl _) (𝟙 b)
  have ht := congrArg Sigma.fst ((k.uniq ⟨t.mid,t.face⟩).trans (k.uniq ⟨𝟙 b,S.idV (𝟙 _)⟩).symm)
  have he : e ≫ t.mid = f := t.left_eq
  exact (Category.comp_id e).symm.trans ((congrArg (e ≫ ·) (show t.mid = 𝟙 b from ht)).symm.trans he)

include I in
theorem horizontal_injective {a b : O} : Function.Injective (H S : Horiz a b → Ar S a b) := by
  intro m n h
  obtain ⟨t⟩ := (eq_iff_step S I.filled (horiz m) (horiz n)).mp h
  have ht : t.mid = 𝟙 a := by simpa [horiz] using t.left_eq
  have hf : S.Sq m (𝟙 a) (𝟙 b) n := ht ▸ t.face
  let k := I.vertical_invariance (Iso.refl a) (Iso.refl b) n
  exact congrArg Sigma.fst ((k.uniq ⟨m,hf⟩).trans (k.uniq ⟨n,S.idV n⟩).symm)

abbrev Obj (a : O) : OrthogonalCornerCategory.Cnr S I.filled := ⟨a⟩

def verticalFunctor : O ⥤ OrthogonalCornerCategory.Cnr S I.filled where
  obj := Obj S I
  map := V S
  map_id _ := rfl
  map_comp e f := (v_then_corner S I e (vert f)).symm

def horizontalFunctor : HObj O ⥤ OrthogonalCornerCategory.Cnr S I.filled where
  obj a := Obj S I a.obj
  map := H S
  map_id _ := rfl
  map_comp f g := (corner_then_h S I (horiz f) g).symm

def verticalClass : MorphismProperty (OrthogonalCornerCategory.Cnr S I.filled) :=
  fun a b p => ∃ f : a.obj ⟶ b.obj, V S f = p
def horizontalClass : MorphismProperty (OrthogonalCornerCategory.Cnr S I.filled) :=
  fun a b p => ∃ f : Horiz a.obj b.obj, H S f = p

instance : (verticalClass S I).IsMultiplicative where
  id_mem a := ⟨𝟙 a.obj,rfl⟩
  comp_mem f g := by
    rintro ⟨e,rfl⟩ ⟨e',rfl⟩
    exact ⟨e ≫ e',(verticalFunctor S I).map_comp e e'⟩

instance : (horizontalClass S I).IsMultiplicative where
  id_mem a := ⟨𝟙 _,rfl⟩
  comp_mem f g := by
    rintro ⟨m,rfl⟩ ⟨m',rfl⟩
    exact ⟨m ≫ m',(horizontalFunctor S I).map_comp m m'⟩

/-- A class with invertible vertical leg has a purely horizontal representative. -/
noncomputable def horizontalize (p : Corner a b) (e : a ≅ p.mid) (he : e.hom = p.e) :
    {m : Horiz a b // H S m = mk S p} := by
  let l := (I.vertical_invariance e (Iso.refl b) p.m).default
  refine ⟨l.1,Quot.sound (r := fun x y => Nonempty (Step S x y)) ?_⟩
  exact ⟨⟨e.hom,(Category.id_comp _).trans he,l.2⟩⟩

/-- A class with invertible horizontal leg has a purely vertical representative. -/
noncomputable def verticalize (p : Corner a b) (m : (⟨p.mid⟩ : HObj O) ≅ ⟨b⟩) (hm : m.hom = p.m) :
    {e : a ⟶ b // V S e = mk S p} := by
  let l := (I.horizontal_invariance m (Iso.refl _) (𝟙 b)).default
  have hl : S.Sq p.m l.1 (𝟙 b) (𝟙 _) := hm ▸ l.2
  exact ⟨p.e ≫ l.1,(Quot.sound (r := fun x y => Nonempty (Step S x y)) ⟨⟨l.1,rfl,hl⟩⟩).symm⟩

theorem vertical_reflects_iso (e : a ⟶ b) [h : IsIso ((verticalFunctor S I).map e)] : IsIso e := by
  obtain ⟨q,l,r⟩ := h.out
  obtain ⟨p,rfl⟩ := Quot.exists_rep q
  change Corner b a at p
  change compose S I.filled (V S e) (mk S p) = V S (𝟙 a) at l
  rw [v_then_corner] at l
  obtain ⟨t⟩ := (eq_iff_step S I.filled _ _).mp l
  let g : b ⟶ a := p.e ≫ t.mid
  have eq : mk S p = V S g := Quot.sound (r := fun x y => Nonempty (Step S x y)) ⟨⟨t.mid,rfl,t.face⟩⟩
  refine ⟨g, ?_, ?_⟩
  · change e ≫ p.e ≫ t.mid = _
    exact (Category.assoc ..).symm.trans t.left_eq
  · apply vertical_injective S I
    change (verticalFunctor S I).map (g ≫ e) = _
    rw [Functor.map_comp]
    change compose S I.filled (V S g) (V S e) = V S (𝟙 b)
    rw [← eq]; exact r

theorem horizontal_reflects_iso (m : Horiz a b) [h : IsIso ((horizontalFunctor S I).map m)] : IsIso m := by
  obtain ⟨q,l,r⟩ := h.out
  obtain ⟨p,rfl⟩ := Quot.exists_rep q
  change Corner b a at p
  change compose S I.filled (mk S p) (H S m) = H S (𝟙 _) at r
  have r' := r
  rw [corner_then_h] at r'
  obtain ⟨t⟩ := (eq_iff_step S I.filled _ _).mp r'
  let k : p.mid ≅ b := t.midIso S I.filled
  have ik : p.e ≫ k.hom = 𝟙 b := t.left_eq
  have he : k.inv = p.e := by
    calc k.inv = (p.e ≫ k.hom) ≫ k.inv := by rw [ik,Category.id_comp]
         _ = p.e := by simp
  let n := horizontalize S I p k.symm he
  refine ⟨n.val, ?_, ?_⟩ <;> apply horizontal_injective S I
  · change (horizontalFunctor S I).map (m ≫ n.val) = _
    rw [Functor.map_comp]
    change compose S I.filled (H S m) (H S n.val) = H S (𝟙 _)
    rw [n.property]; exact l
  · change (horizontalFunctor S I).map (n.val ≫ m) = _
    rw [Functor.map_comp]
    change compose S I.filled (H S n.val) (H S m) = H S (𝟙 _)
    rw [n.property]; exact r

include I in
/-- A basic comparison identifies the two edge representatives with
mutually inverse arrows in the corner category. -/
theorem basic_horizontal_iso {θ : i ⟶ j} {ψ : Horiz j i} (h : Basic S θ ψ) : IsIso ψ := by
  let p : Corner i i := ⟨j,θ,ψ⟩
  let step : Step S (horiz (𝟙 (⟨i⟩ : HObj O))) p := ⟨θ,Category.id_comp _,h⟩
  let k : i ≅ j := step.midIso S I.filled
  have fac : (verticalFunctor S I).map k.hom ≫ (horizontalFunctor S I).map ψ = 𝟙 (Obj S I i) := by
    have ek : k.hom = θ := rfl
    rw [ek]
    change compose S I.filled (V S θ) (H S ψ) = V S (𝟙 i)
    exact (comp_from_legs S I.filled θ ψ).trans (Quot.sound (r := fun x y => Nonempty (Step S x y)) ⟨step⟩).symm
  have eq : (horizontalFunctor S I).map ψ = ((verticalFunctor S I).mapIso k).inv := by
    apply (cancel_epi ((verticalFunctor S I).mapIso k).hom).mp
    exact fac.trans ((verticalFunctor S I).mapIso k).hom_inv_id.symm
  have : IsIso ((horizontalFunctor S I).map ψ) := eq.symm ▸ ((verticalFunctor S I).mapIso k).isIso_inv
  exact horizontal_reflects_iso S I ψ

theorem vertical_iff_iso_horizontal_leg (p : Corner a b) :
    verticalClass S I (show Obj S I a ⟶ Obj S I b from mk S p) ↔ IsIso p.m := by
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨t⟩ := (eq_iff_step S I.filled (vert e) p).mp he
    let l := StepLink S I t
    have : IsIso l.ψ := basic_horizontal_iso S I l.basic
    have eq : l.ψ = p.m := (Category.comp_id _).symm.trans l.second
    exact eq ▸ this
  · intro h
    exact ⟨(verticalize S I p (asIso p.m) rfl).val,(verticalize S I p (asIso p.m) rfl).property⟩

theorem horizontal_iff_iso_vertical_leg (p : Corner a b) :
    horizontalClass S I (show Obj S I a ⟶ Obj S I b from mk S p) ↔ IsIso p.e := by
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨t⟩ := (eq_iff_step S I.filled (horiz m) p).mp hm
    let k : a ≅ p.mid := t.midIso S I.filled
    have eq : k.hom = p.e := by change t.mid = p.e; exact (Category.id_comp _).symm.trans t.left_eq
    exact eq ▸ k.isIso_hom
  · intro h
    exact ⟨(horizontalize S I p (asIso p.e) rfl).val,(horizontalize S I p (asIso p.e) rfl).property⟩

private theorem iso_factors {D : Type*} [Category* D] {x y z : D} (u : x ⟶ y) (v : y ⟶ z) [IsIso (u ≫ v)]
    (rigid : ∀ f : y ⟶ y, u ≫ f = u → f ≫ v = v → f = 𝟙 y) : IsIso u ∧ IsIso v := by
  let k := CategoryTheory.inv (u ≫ v)
  have l : (u ≫ v) ≫ k = 𝟙 x := IsIso.hom_inv_id _
  have r : k ≫ (u ≫ v) = 𝟙 z := IsIso.inv_hom_id _
  have h₁ : u ≫ (v ≫ k ≫ u) = u := by rw [← Category.assoc u,← Category.assoc,l,Category.id_comp]
  have h₂ : (v ≫ k ≫ u) ≫ v = v := by rw [Category.assoc,Category.assoc,r,Category.comp_id]
  have h := rigid _ h₁ h₂
  exact ⟨⟨v ≫ k, (Category.assoc ..).symm.trans l, (Category.assoc ..).trans h⟩,
    ⟨k ≫ u,h,(Category.assoc ..).trans r⟩⟩

theorem common_is_iso {x y : OrthogonalCornerCategory.Cnr S I.filled} (f : x ⟶ y) :
    verticalClass S I f ∧ horizontalClass S I f → IsIso f := by
  rintro ⟨⟨e,rfl⟩,⟨m,h⟩⟩
  obtain ⟨t⟩ := (eq_iff_step S I.filled (horiz m) (vert e)).mp h
  let k : x.obj ≅ y.obj := t.midIso S I.filled
  have he : k.hom = e := by change t.mid = e; simpa [horiz,vert] using t.left_eq
  change IsIso ((verticalFunctor S I).map e)
  rw [← he]; infer_instance

theorem iso_common {x y : OrthogonalCornerCategory.Cnr S I.filled} (f : x ⟶ y) [hf : IsIso f] :
    verticalClass S I f ∧ horizontalClass S I f := by
  obtain ⟨p,rfl⟩ := Quot.exists_rep f
  let u : x ⟶ Obj S I p.mid := V S p.e
  let v : Obj S I p.mid ⟶ y := H S p.m
  have uv : u ≫ v = mk S p := comp_from_legs S I.filled p.e p.m
  have : IsIso (u ≫ v) := uv.symm ▸ hf
  have parts := iso_factors u v (fun g hl hr => by
    let d : Diagonal S I p p := ⟨g,hl,hr⟩
    exact diagonal_unique S I (Step.identity S p) d)
  have : IsIso ((verticalFunctor S I).map p.e) := parts.1
  have : IsIso ((horizontalFunctor S I).map p.m) := parts.2
  have : IsIso p.e := vertical_reflects_iso S I p.e
  have : IsIso p.m := horizontal_reflects_iso S I p.m
  exact ⟨⟨(verticalize S I p (asIso p.m) rfl).val,(verticalize S I p (asIso p.m) rfl).property⟩,
    ⟨(horizontalize S I p (asIso p.e) rfl).val,(horizontalize S I p (asIso p.e) rfl).property⟩⟩

abbrev FCorner (x y : OrthogonalCornerCategory.Cnr S I.filled) :=
  FactorizationDoubleEnvelope.Corner (verticalClass S I) (horizontalClass S I) x y

noncomputable def raw {x y : OrthogonalCornerCategory.Cnr S I.filled} (p : FCorner S I x y) : Corner x.obj y.obj :=
  ⟨p.mid.obj,p.he.choose,p.hm.choose⟩

theorem raw_decode {x y : OrthogonalCornerCategory.Cnr S I.filled} (p : FCorner S I x y) :
    mk S (raw S I p) = p.decode _ _ := by
  have e : V S (raw S I p).e = p.e := p.he.choose_spec
  have m : H S (raw S I p).m = p.m := p.hm.choose_spec
  change mk S (raw S I p) = compose S I.filled p.e p.m
  rw [← e, ← m]
  exact (comp_from_legs S I.filled _ _).symm

def comparisonEquiv {x y : OrthogonalCornerCategory.Cnr S I.filled} (p q : FCorner S I x y) :
    FactorizationDoubleEnvelope.Comparison (verticalClass S I) (horizontalClass S I) p q ≃
    Diagonal S I (raw S I p) (raw S I q) := by
  have ep : V S (raw S I p).e = p.e := p.he.choose_spec
  have eq : V S (raw S I q).e = q.e := q.he.choose_spec
  have mp : H S (raw S I p).m = p.m := p.hm.choose_spec
  have mq : H S (raw S I q).m = q.m := q.hm.choose_spec
  refine ⟨fun f => ⟨f.map,?_,?_⟩,fun f => ⟨f.map,?_,?_⟩,fun _ => rfl,fun _ => rfl⟩
  · rw [ep,eq]; exact f.first
  · rw [mq,mp]; exact f.second
  · change compose S I.filled p.e f.map = q.e
    rw [← ep,← eq]; exact f.first
  · change compose S I.filled f.map q.m = p.m
    rw [← mp,← mq]; exact f.second

/-- The two classes on the reconstructed category satisfy the three
factorization-side requirements of Štěpán 3.3.8. -/
noncomputable def factorization :
    FactorizationDoubleEnvelope.OrthogonalData (verticalClass S I) (horizontalClass S I) where
  factors := by
    intro x y f
    let p := Quot.out f
    refine ⟨Obj S I p.mid,V S p.e,H S p.m,?_,⟨p.e,rfl⟩,⟨p.m,rfl⟩⟩
    exact (comp_from_legs S I.filled p.e p.m).trans (Quot.out_eq f)
  comparison p q e := by
    have h := (raw_decode S I p).trans (e.trans (raw_decode S I q).symm)
    letI := uniqueDiagonal S I _ _ h
    exact (comparisonEquiv S I p q).unique
  common f := ⟨common_is_iso S I f,fun h => letI := h; iso_common S I f⟩

/-- The native square, including its uniqueness, is recovered in the
marked ordinary envelope after the intrinsic reconstruction. -/
noncomputable def squareEquiv {m : Horiz a b} {e : a ⟶ i} {v : b ⟶ c} {n : Horiz i c} :
    S.Sq m e v n ≃ (compose S I.filled (H S m) (V S v) = compose S I.filled (V S e) (H S n)) where
  toFun h := (square_iff S I.filled).mp ⟨h⟩
  invFun h := ((square_iff S I.filled).mpr h).some
  left_inv _ := (flat S I).allEq _ _
  right_inv _ := rfl

noncomputable def verticalEquiv (x y : OrthogonalCornerCategory.Cnr S I.filled) :
    (x.obj ⟶ y.obj) ≃ {p : x ⟶ y // verticalClass S I p} :=
  Equiv.ofBijective (fun e => ⟨V S e,e,rfl⟩)
    ⟨fun _ _ h => vertical_injective S I (congrArg Subtype.val h),fun ⟨_,e,rfl⟩ => ⟨e,rfl⟩⟩

noncomputable def horizontalEquiv (x y : OrthogonalCornerCategory.Cnr S I.filled) :
    Horiz x.obj y.obj ≃ {p : x ⟶ y // horizontalClass S I p} :=
  Equiv.ofBijective (fun m => ⟨H S m,m,rfl⟩)
    ⟨fun _ _ h => horizontal_injective S I (congrArg Subtype.val h),fun ⟨_,m,rfl⟩ => ⟨m,rfl⟩⟩

end ContextualComposition.OrthogonalCornerRecognition
