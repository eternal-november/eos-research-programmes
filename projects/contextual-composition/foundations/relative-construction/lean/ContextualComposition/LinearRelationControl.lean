module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Prod

/-! The linear positive control in the finite reduction report, §4. Subspaces represent linear relations. The pushout quotient by the image of the difference of the legs retains a single linear gluing witness. -/

@[expose] public section

namespace ContextualComposition.LinearRelationControl

universe u
variable {K A B C E W Y Z T : Type u} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup E] [Module K E]
  [AddCommGroup W] [Module K W] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup T] [Module K T]

/-- A subspace domain, a surjective linear block map and a linear selector. -/
structure Presentation (K A B Y : Type u) [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup Y] [Module K Y] where
  domain : Submodule K A
  block : B →ₗ[K] Y
  onto : Function.Surjective block
  selected : domain →ₗ[K] Y

def Presentation.relation (P : Presentation K A B Y) : Submodule K (A × B) where
  carrier x := ∃ ha : x.1 ∈ P.domain, P.selected ⟨x.1, ha⟩ = P.block x.2
  zero_mem' := ⟨P.domain.zero_mem, (map_zero P.selected).trans (map_zero P.block).symm⟩
  add_mem' := by
    rintro x y ⟨hx, ex⟩ ⟨hy, ey⟩
    exact ⟨P.domain.add_mem hx hy, (map_add P.selected (⟨x.1,hx⟩ : P.domain) ⟨y.1,hy⟩).trans
      ((congrArg₂ (· + ·) ex ey).trans (map_add P.block x.2 y.2).symm)⟩
  smul_mem' := by
    rintro k x ⟨hx, ex⟩
    exact ⟨P.domain.smul_mem k hx, (map_smul P.selected k (⟨x.1,hx⟩ : P.domain)).trans
      ((congrArg (k • ·) ex).trans (map_smul P.block k x.2).symm)⟩

def source (R : Submodule K (A × B)) : Submodule K A where
  carrier a := ∃ b, (a, b) ∈ R
  zero_mem' := ⟨0, R.zero_mem⟩
  add_mem' := by
    rintro a a' ⟨b, h⟩ ⟨b', h'⟩
    exact ⟨b + b', R.add_mem h h'⟩
  smul_mem' := by
    rintro k a ⟨b, h⟩
    exact ⟨k • b, R.smul_mem k h⟩

def zeroRow (R : Submodule K (A × B)) : Submodule K B :=
  R.comap (LinearMap.inr K A B)

private theorem class_eq (R : Submodule K (A × B)) {a : A} {b b' : B}
    (hb : (a,b) ∈ R) (hb' : (a,b') ∈ R) : (zeroRow R).mkQ b = (zeroRow R).mkQ b' := by
  apply (Submodule.Quotient.eq (zeroRow R)).mpr
  change (0, b - b') ∈ R
  simpa only [Prod.mk_sub_mk, sub_self] using R.sub_mem hb hb'

noncomputable def selector (R : Submodule K (A × B)) : source R →ₗ[K] B ⧸ zeroRow R where
  toFun a := (zeroRow R).mkQ (show ∃ b, (a.val,b) ∈ R from a.property).choose
  map_add' a a' := by
    let ex (x : source R) : ∃ b, (x.val,b) ∈ R := x.property
    exact (class_eq R (ex (a+a')).choose_spec (R.add_mem (ex a).choose_spec (ex a').choose_spec)).trans (map_add _ _ _)
  map_smul' k a := by
    let ex (x : source R) : ∃ b, (x.val,b) ∈ R := x.property
    exact (class_eq R (ex (k • a)).choose_spec (R.smul_mem k (ex a).choose_spec)).trans (map_smul _ _ _)

noncomputable def recover (R : Submodule K (A × B)) : Presentation K A B (B ⧸ zeroRow R) :=
  ⟨source R, (zeroRow R).mkQ, (zeroRow R).mkQ_surjective, selector R⟩

theorem recover_relation (R : Submodule K (A × B)) : (recover R).relation = R := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨h, e⟩
    let ex : ∃ b', (a,b') ∈ R := h
    have hd := (Submodule.Quotient.eq (zeroRow R)).mp e
    change (0, ex.choose - b) ∈ R at hd
    simpa only [Prod.mk_sub_mk, sub_zero, sub_sub_cancel] using R.sub_mem ex.choose_spec hd
  · intro h
    let ex : ∃ b', (a,b') ∈ R := ⟨b,h⟩
    exact ⟨ex, class_eq R ex.choose_spec h⟩

theorem source_relation (P : Presentation K A B Y) : source P.relation = P.domain := by
  ext a
  constructor
  · rintro ⟨b, h, _⟩; exact h
  · intro h
    obtain ⟨b, e⟩ := P.onto (P.selected ⟨a,h⟩)
    exact ⟨b, h, e.symm⟩

theorem zeroRow_relation (P : Presentation K A B Y) : zeroRow P.relation = LinearMap.ker P.block := by
  ext b
  constructor
  · rintro ⟨h,e⟩
    exact e.symm.trans (map_zero P.selected)
  · intro h
    exact ⟨P.domain.zero_mem, (map_zero P.selected).trans h.symm⟩

variable (q : E →ₗ[K] W) (g : E →ₗ[K] Z)

/-- The subspace of identifications in the direct-sum quotient. -/
def gluing : Submodule K (W × Z) := LinearMap.range (q.prod (-g))

abbrev Pushout := (W × Z) ⧸ gluing q g

def left : W →ₗ[K] Pushout q g := (gluing q g).mkQ.comp (LinearMap.inl K W Z)
def right : Z →ₗ[K] Pushout q g := (gluing q g).mkQ.comp (LinearMap.inr K W Z)

theorem single_witness (w : W) (z : Z) :
    left q g w = right q g z ↔ ∃ e, q e = w ∧ g e = z := by
  change (Submodule.Quotient.mk (w, 0) : Pushout q g) = Submodule.Quotient.mk (0, z) ↔ _
  rw [Submodule.Quotient.eq]
  change (∃ e, (q e, -g e) = (w,0) - (0,z)) ↔ _
  simp only [Prod.mk_sub_mk, sub_zero, zero_sub, Prod.mk.injEq, neg_inj]

def descend (l : W →ₗ[K] T) (r : Z →ₗ[K] T) (h : ∀ e, l (q e) = r (g e)) :
    Pushout q g →ₗ[K] T := (gluing q g).liftQ (l.coprod r) (by
  rintro _ ⟨e,rfl⟩
  change l (q e) + r (-g e) = 0
  rw [map_neg, h, add_neg_cancel])

theorem descend_left (l : W →ₗ[K] T) (r : Z →ₗ[K] T) (h : ∀ e, l (q e) = r (g e)) (w : W) :
    descend q g l r h (left q g w) = l w := by
  change l w + r 0 = l w
  rw [map_zero, add_zero]

theorem descend_right (l : W →ₗ[K] T) (r : Z →ₗ[K] T) (h : ∀ e, l (q e) = r (g e)) (z : Z) :
    descend q g l r h (right q g z) = r z := by
  change l 0 + r z = r z
  rw [map_zero, zero_add]

theorem descend_unique (l : W →ₗ[K] T) (r : Z →ₗ[K] T) (h : ∀ e, l (q e) = r (g e))
    (k : Pushout q g →ₗ[K] T) (hl : ∀ w, k (left q g w) = l w) (hr : ∀ z, k (right q g z) = r z) :
    k = descend q g l r h := by
  apply LinearMap.ext
  intro x
  obtain ⟨⟨w,z⟩,rfl⟩ := (gluing q g).mkQ_surjective x
  have eq : (gluing q g).mkQ (w,z) = left q g w + right q g z := by
    change _ = (gluing q g).mkQ (w,0) + (gluing q g).mkQ (0,z)
    rw [← map_add]; simp
  rw [eq, map_add, map_add, hl, hr, descend_left, descend_right]

variable (P : Presentation K A B Y) (Q : Presentation K B C Z)

def middle : Q.domain →ₗ[K] Y := P.block.comp Q.domain.subtype

abbrev Labels := Pushout (middle P Q).rangeRestrict Q.selected

def compDomain : Submodule K A where
  carrier a := ∃ ha : a ∈ P.domain, P.selected ⟨a,ha⟩ ∈ LinearMap.range (middle P Q)
  zero_mem' := ⟨P.domain.zero_mem, (show P.selected 0 ∈ LinearMap.range (middle P Q) by simp)⟩
  add_mem' := by
    rintro a a' ⟨ha, e⟩ ⟨ha', e'⟩
    exact ⟨P.domain.add_mem ha ha', (map_add P.selected (⟨a,ha⟩ : P.domain) ⟨a',ha'⟩) ▸ (LinearMap.range (middle P Q)).add_mem e e'⟩
  smul_mem' := by
    rintro k a ⟨ha,e⟩
    exact ⟨P.domain.smul_mem k ha, (map_smul P.selected k (⟨a,ha⟩ : P.domain)) ▸ (LinearMap.range (middle P Q)).smul_mem k e⟩

noncomputable def activeSelector : compDomain P Q →ₗ[K] LinearMap.range (middle P Q) where
  toFun a := ⟨P.selected ⟨a.val,a.property.choose⟩, a.property.choose_spec⟩
  map_add' a a' := Subtype.ext (map_add P.selected (⟨a.val,a.property.choose⟩ : P.domain) ⟨a'.val,a'.property.choose⟩)
  map_smul' k a := Subtype.ext (map_smul P.selected k (⟨a.val,a.property.choose⟩ : P.domain))

theorem right_surjective (hq : Function.Surjective q) : Function.Surjective (right q g) := by
  intro x
  obtain ⟨⟨w,z⟩, rfl⟩ := (gluing q g).mkQ_surjective x
  obtain ⟨e,rfl⟩ := hq w
  refine ⟨g e + z, ?_⟩
  rw [map_add, ← (single_witness q g (q e) (g e)).mpr ⟨e,rfl,rfl⟩]
  change (gluing q g).mkQ (q e,0) + (gluing q g).mkQ (0,z) = _
  rw [← map_add]; simp

noncomputable def comp : Presentation K A C (Labels P Q) where
  domain := compDomain P Q
  selected := (left _ _).comp (activeSelector P Q)
  block := (right _ _).comp Q.block
  onto := (right_surjective _ _ (by rintro ⟨_,e,rfl⟩; exact ⟨e,rfl⟩)).comp Q.onto

/-- The normalized linear pushout recovers ordinary relational composition with an actual intermediate vector. -/
theorem comp_relation (a : A) (c : C) :
    (a,c) ∈ (comp P Q).relation ↔ ∃ b : B, (a,b) ∈ P.relation ∧ (b,c) ∈ Q.relation := by
  constructor
  · rintro ⟨h,e⟩
    obtain ⟨u, hu, hv⟩ := (single_witness _ _ _ _).mp e
    exact ⟨u.val, ⟨h.choose, (congrArg Subtype.val hu).symm⟩, u.property, hv⟩
  · rintro ⟨b, ⟨ha, ep⟩, hb, eq⟩
    have h : a ∈ compDomain P Q := ⟨ha, ⟨b,hb⟩, ep.symm⟩
    exact ⟨h, (single_witness _ _ _ _).mpr ⟨⟨b,hb⟩, Subtype.ext ep.symm, eq⟩⟩

theorem comp_assoc_relation {D U : Type u} [AddCommGroup D] [Module K D]
    [AddCommGroup U] [Module K U] (S : Presentation K C D U) :
    (comp (comp P Q) S).relation = (comp P (comp Q S)).relation := by
  ext ⟨a,d⟩
  constructor
  · intro h
    obtain ⟨c, hc, hd⟩ := (comp_relation _ _ _ _).mp h
    obtain ⟨b, hb, hc'⟩ := (comp_relation _ _ _ _).mp hc
    exact (comp_relation _ _ _ _).mpr ⟨b, hb, (comp_relation _ _ _ _).mpr ⟨c,hc',hd⟩⟩
  · intro h
    obtain ⟨b, hb, hd⟩ := (comp_relation _ _ _ _).mp h
    obtain ⟨c, hc, hd'⟩ := (comp_relation _ _ _ _).mp hd
    exact (comp_relation _ _ _ _).mpr ⟨c,(comp_relation _ _ _ _).mpr ⟨b,hb,hc⟩,hd'⟩

section Squares

variable {A' B' : Type u} [AddCommGroup A'] [Module K A'] [AddCommGroup B'] [Module K B']
variable (P' : Presentation K A' B' Z) (s : A →ₗ[K] A') (t : B →ₗ[K] B')

/-- A native square has an induced linear map of domains over s and a forward linear quotient map. -/
structure Cell where
  domainMap : ∀ a ∈ P.domain, s a ∈ P'.domain
  labelMap : Y →ₗ[K] Z
  block_comm : ∀ b, labelMap (P.block b) = P'.block (t b)
  selected_comm : ∀ d, labelMap (P.selected d) = P'.selected ⟨s d.val, domainMap _ d.property⟩

variable {P P' s t}

theorem Cell.map_relation (cell : Cell P P' s t) {a b} :
    (a,b) ∈ P.relation → (s a,t b) ∈ P'.relation := by
  rintro ⟨ha,eq⟩
  exact ⟨cell.domainMap a ha,(cell.selected_comm ⟨a,ha⟩).symm.trans ((congrArg cell.labelMap eq).trans (cell.block_comm b))⟩

/-- The zero row forces kernel preservation, so preservation of the relation alone constructs the forward grade map. -/
noncomputable def cellOfRelation
    (h : ∀ a b, (a,b) ∈ P.relation → (s a,t b) ∈ P'.relation) : Cell P P' s t := by
  let f : B →ₗ[K] Z := P'.block.comp t
  have hk (b : B) (hb : P.block b = 0) : f b = 0 := by
    have hz : (0,b) ∈ P.relation := ⟨P.domain.zero_mem, (map_zero P.selected).trans hb.symm⟩
    have hz' : (0,t b) ∈ P'.relation := by simpa only [map_zero] using h _ _ hz
    exact ((zeroRow_relation P') ▸ (show t b ∈ zeroRow P'.relation from hz') : t b ∈ LinearMap.ker P'.block)
  have heq (x y : B) (e : P.block x = P.block y) : f x = f y := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hk _ (by rw [map_sub, e, sub_self])
  let rep (i : Y) := (P.onto i).choose
  have hr (i : Y) : P.block (rep i) = i := (P.onto i).choose_spec
  let l : Y →ₗ[K] Z := {
    toFun := fun i => f (rep i)
    map_add' := fun i j => (heq _ (rep i + rep j) (by rw [hr, map_add, hr, hr])).trans (map_add f _ _)
    map_smul' := fun k i => (heq _ (k • rep i) (by rw [hr, map_smul, hr])).trans (map_smul f _ _) }
  have hl (b : B) : l (P.block b) = f b := heq _ b (hr _)
  have hd (a : A) (ha : a ∈ P.domain) : s a ∈ P'.domain := by
    obtain ⟨b, e⟩ := P.onto (P.selected ⟨a,ha⟩)
    exact (h a b ⟨ha,e.symm⟩).choose
  refine ⟨hd,l,hl,?_⟩
  intro d
  obtain ⟨b,e⟩ := P.onto (P.selected d)
  obtain ⟨_,hc⟩ := h d.val b ⟨d.property,e.symm⟩
  exact ((congrArg l e.symm).trans (hl b)).trans hc.symm

instance : Subsingleton (Cell P P' s t) where
  allEq c d := by
    have e : c.labelMap = d.labelMap := by
      apply LinearMap.ext; intro y
      obtain ⟨b,rfl⟩ := P.onto y
      exact (c.block_comm b).trans (d.block_comm b).symm
    cases c; cases d; cases e; rfl

theorem native_square_iff : Nonempty (Cell P P' s t) ↔ ∀ a b, (a,b) ∈ P.relation → (s a,t b) ∈ P'.relation :=
  ⟨fun ⟨f⟩ _ _ => f.map_relation, fun h => ⟨cellOfRelation h⟩⟩

end Squares

/-- Inverse native squares over the original endpoints, including the quotient-label inverse equations. -/
structure Iso (P : Presentation K A B Y) (P' : Presentation K A B Z) where
  forward : Cell P P' LinearMap.id LinearMap.id
  backward : Cell P' P LinearMap.id LinearMap.id
  left_inv : ∀ y, backward.labelMap (forward.labelMap y) = y
  right_inv : ∀ z, forward.labelMap (backward.labelMap z) = z

noncomputable def isoOfRelationEq {P : Presentation K A B Y} {P' : Presentation K A B Z}
    (h : P.relation = P'.relation) : Iso P P' := by
  let f : Cell P P' LinearMap.id LinearMap.id := cellOfRelation (fun _ _ e => h ▸ e)
  let g : Cell P' P LinearMap.id LinearMap.id := cellOfRelation (fun _ _ e => h.symm ▸ e)
  refine ⟨f,g,?_,?_⟩
  · intro y
    obtain ⟨b,rfl⟩ := P.onto y
    exact (congrArg g.labelMap (f.block_comm b)).trans (g.block_comm b)
  · intro z
    obtain ⟨b,rfl⟩ := P'.onto z
    exact (congrArg f.labelMap (g.block_comm b)).trans (f.block_comm b)

/-- Rebuilding from the relation retains the entire presentation up to inverse endpoint-fixing squares. -/
noncomputable def recoveryIso (P : Presentation K A B Y) : Iso (recover P.relation) P :=
  isoOfRelationEq (recover_relation P.relation)

section Controls

def partialMap (D : Submodule K A) (f : D →ₗ[K] B) : Presentation K A B B :=
  ⟨D, LinearMap.id, Function.surjective_id, f⟩

variable (D : Submodule K A) (f : D →ₗ[K] B) (U : Submodule K B) (k : U →ₗ[K] C)

/-- The ordinary pullback domain of two partial linear functions. -/
def partialDomain : Submodule K A where
  carrier a := ∃ h : a ∈ D, f ⟨a,h⟩ ∈ U
  zero_mem' := ⟨D.zero_mem, (show f 0 ∈ U by simp)⟩
  add_mem' := by
    rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
    exact ⟨D.add_mem ha hb, (map_add f (⟨a,ha⟩ : D) ⟨b,hb⟩) ▸ U.add_mem ea eb⟩
  smul_mem' := by
    rintro c a ⟨ha,ea⟩
    exact ⟨D.smul_mem c ha, (map_smul f c (⟨a,ha⟩ : D)) ▸ U.smul_mem c ea⟩

noncomputable def pullbackLeg : partialDomain D f U →ₗ[K] U where
  toFun a := ⟨f ⟨a.val,a.property.choose⟩, a.property.choose_spec⟩
  map_add' a b := Subtype.ext (map_add f (⟨a.val,a.property.choose⟩ : D) ⟨b.val,b.property.choose⟩)
  map_smul' c a := Subtype.ext (map_smul f c (⟨a.val,a.property.choose⟩ : D))

noncomputable def partialControl :
    Iso (comp (partialMap D f) (partialMap U k))
        (partialMap (partialDomain D f U) (k.comp (pullbackLeg D f U))) := by
  apply isoOfRelationEq
  ext ⟨a,c⟩
  rw [comp_relation]
  constructor
  · rintro ⟨b, ⟨ha,hb⟩, hu,hc⟩
    change f ⟨a,ha⟩ = b at hb
    have hu' : f ⟨a,ha⟩ ∈ U := hb.symm ▸ hu
    exact ⟨⟨ha,hu'⟩, (congrArg k (show (⟨f ⟨a,ha⟩,hu'⟩ : U) = ⟨b,hu⟩ from Subtype.ext hb)).trans hc⟩
  · rintro ⟨⟨ha,hu⟩,hc⟩
    exact ⟨f ⟨a,ha⟩,⟨ha,rfl⟩,hu,hc⟩

/-- A total content arrow is a linear cospan with a surjective target leg. -/
def totalCospan (l : A →ₗ[K] Y) (r : B →ₗ[K] Y) (hr : Function.Surjective r) : Presentation K A B Y :=
  ⟨⊤,r,hr,l.comp (⊤ : Submodule K A).subtype⟩

variable (l : A →ₗ[K] Y) (r : B →ₗ[K] Y) (hr : Function.Surjective r)
  (m : B →ₗ[K] Z) (n : C →ₗ[K] Z) (hn : Function.Surjective n)

/-- The total-domain recipe recovers native cospan composition by the full linear pushout, with its two induced legs. -/
noncomputable def totalControl :
    Iso (comp (totalCospan l r hr) (totalCospan m n hn))
        (totalCospan ((left r m).comp l) ((right r m).comp n) ((right_surjective r m hr).comp hn)) := by
  apply isoOfRelationEq
  ext ⟨a,c⟩
  rw [comp_relation]
  constructor
  · rintro ⟨b, ⟨_,hb⟩, _,hc⟩
    exact ⟨trivial,(single_witness r m _ _).mpr ⟨b,hb.symm,hc⟩⟩
  · rintro ⟨_,h⟩
    obtain ⟨b,eb,ec⟩ := (single_witness r m (l a) (n c)).mp h
    exact ⟨b,⟨trivial,eb.symm⟩,trivial,ec⟩

end Controls

end ContextualComposition.LinearRelationControl
