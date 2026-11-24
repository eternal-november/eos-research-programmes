import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Basic

/-!
# Settlement windows for immutable grant atoms

One atom per issued job in a single history. An atom carries a set of exposed
jobs (the issue prefix in the protocol) and a separate set of certified
retirements (certified prefixes, not individual above-frontier receipts).
No protocol or clock implementation is imported into this file.
-/

namespace SwarmSettlement

universe u v w

structure History (Job : Type u) (Right : Type v) (Time : Type w) where
  right : Job → Right
  time : Job → Time
  exposes : Job → Set Job
  certifies : Job → Set Job

variable {Job : Type u} {Right : Type v} {Time : Type w} [LinearOrder Time]

/-- Same-right spends are ordered by time. No distinct-time premise is imposed
on jobs on different rights. -/
def Earlier (h : History Job Right Time) (a b : Job) : Prop :=
  h.right a = h.right b ∧ h.time a < h.time b

/-- Independent premises of the two-atom necessity argument. Chronology is only
required for same-right certificates, and thus includes non-self-certification. -/
structure Lawful (h : History Job Right Time) : Prop where
  selfExposed : ∀ j, j ∈ h.exposes j
  strictSameRight : ∀ {g j}, h.right j = h.right g →
    j ∈ h.certifies g → h.time j < h.time g
  sameRightTimeInjective : ∀ {a b}, h.right a = h.right b →
    h.time a = h.time b → a = b

/-- A view is any subset of grant atoms chosen from the same immutable history. -/
def Exposed (h : History Job Right Time) (G : Set Job) (j : Job) : Prop :=
  ∃ g ∈ G, j ∈ h.exposes g

def Certified (h : History Job Right Time) (G : Set Job) (j : Job) : Prop :=
  ∃ g ∈ G, j ∈ h.certifies g

def Counted (h : History Job Right Time) (G : Set Job) (j : Job) : Prop :=
  Exposed h G j ∧ ¬ Certified h G j

/-- Required evidence can omit earlier spends of a revealed job already retired
by this atom. This is a condition on the evidence semantics, not an encoding. -/
def CoversPriorSpends (h : History Job Right Time) : Prop :=
  ∀ ⦃g b⦄, b ∈ h.exposes g → b ∉ h.certifies g →
    ∀ ⦃a⦄, Earlier h a b → a ∈ h.certifies g

def AllViewsRightUnique (h : History Job Right Time) : Prop :=
  ∀ G : Set Job, Set.InjOn h.right {j | Counted h G j}

omit [LinearOrder Time] in
theorem exposed_union {h : History Job Right Time} {G H : Set Job} {j : Job} :
    Exposed h (G ∪ H) j ↔ Exposed h G j ∨ Exposed h H j := by
  constructor
  · rintro ⟨g, hg | hg, hw⟩
    · exact Or.inl ⟨g, hg, hw⟩
    · exact Or.inr ⟨g, hg, hw⟩
  · rintro (⟨g,hg,hw⟩ | ⟨g,hg,hw⟩)
    · exact ⟨g, Or.inl hg, hw⟩
    · exact ⟨g, Or.inr hg, hw⟩

omit [LinearOrder Time] in
theorem certified_union {h : History Job Right Time} {G H : Set Job} {j : Job} :
    Certified h (G ∪ H) j ↔ Certified h G j ∨ Certified h H j := by
  constructor
  · rintro ⟨g, hg | hg, hw⟩
    · exact Or.inl ⟨g, hg, hw⟩
    · exact Or.inr ⟨g, hg, hw⟩
  · rintro (⟨g,hg,hw⟩ | ⟨g,hg,hw⟩)
    · exact ⟨g, Or.inl hg, hw⟩
    · exact ⟨g, Or.inr hg, hw⟩

theorem earlier_not_both_counted {h : History Job Right Time}
    (cover : CoversPriorSpends h) {G : Set Job} {a b : Job}
    (earlier : Earlier h a b) (aCounted : Counted h G a) (bCounted : Counted h G b) :
    False := by
  obtain ⟨g, hg, exposed⟩ := bCounted.1
  have notSettled : b ∉ h.certifies g := fun hc => bCounted.2 ⟨g,hg,hc⟩
  exact aCounted.2 ⟨g,hg,cover exposed notSettled earlier⟩

/-- Missing evidence yields an explicit two-atom view retaining both jobs. -/
theorem two_atom_counterview {h : History Job Right Time} (law : Lawful h)
    {g a b : Job} (earlier : Earlier h a b)
    (bExposed : b ∈ h.exposes g) (bNotCertified : b ∉ h.certifies g)
    (aNotCertified : a ∉ h.certifies g) :
    Counted h ({g,a} : Set Job) a ∧ Counted h ({g,a} : Set Job) b := by
  have atA : a ∈ ({g,a} : Set Job) := Or.inr rfl
  have atG : g ∈ ({g,a} : Set Job) := Or.inl rfl
  have aSelf : a ∉ h.certifies a := fun hc =>
    (lt_irrefl _) (law.strictSameRight rfl hc)
  have bAfter : b ∉ h.certifies a := fun hc =>
    (not_lt_of_ge (le_of_lt earlier.2)) (law.strictSameRight earlier.1.symm hc)
  constructor
  · refine ⟨⟨a,atA,law.selfExposed a⟩, ?_⟩
    rintro ⟨i, hi, hc⟩
    rcases hi with hi | hi
    · exact aNotCertified (hi ▸ hc)
    · exact aSelf (hi ▸ hc)
  · refine ⟨⟨g,atG,bExposed⟩, ?_⟩
    rintro ⟨i, hi, hc⟩
    rcases hi with hi | hi
    · exact bNotCertified (hi ▸ hc)
    · exact bAfter (hi ▸ hc)

theorem all_views_right_unique_iff {h : History Job Right Time} (law : Lawful h) :
    AllViewsRightUnique h ↔ CoversPriorSpends h := by
  constructor
  · intro unique g b expose notCert a earlier
    by_contra aNotCert
    obtain ⟨ha,hb⟩ := two_atom_counterview law earlier expose notCert aNotCert
    have e : a = b := unique {g,a} ha hb earlier.1
    exact (ne_of_lt earlier.2) (congrArg h.time e)
  · intro cover G a ha b hb sameRight
    rcases lt_trichotomy (h.time a) (h.time b) with lt | eq | gt
    · exact False.elim (earlier_not_both_counted cover ⟨sameRight,lt⟩ ha hb)
    · exact law.sameRightTimeInjective sameRight eq
    · exact False.elim (earlier_not_both_counted cover ⟨sameRight.symm,gt⟩ hb ha)

/-- For a finite right type every counted-ID subtype has cardinal at most
the number of rights, even if the ambient job type is not finite. -/
noncomputable def countedEmbedding {h : History Job Right Time}
    (unique : AllViewsRightUnique h) (G : Set Job) :
    {j : Job // Counted h G j} ↪ Right :=
  ⟨fun j => h.right j.val, fun x y e => Subtype.ext (unique G x.property y.property e)⟩

omit [LinearOrder Time] in
theorem finset_width_bound [Fintype Right] {h : History Job Right Time}
    (unique : AllViewsRightUnique h) (G : Set Job) (S : Finset Job)
    (allCounted : ∀ j ∈ S, Counted h G j) : S.card ≤ Fintype.card Right := by
  rw [← Fintype.card_coe S]
  exact Fintype.card_le_of_injective (fun j : S => h.right j.val)
    (fun x y e => Subtype.ext (unique G (allCounted x x.property) (allCounted y y.property) e))

theorem finset_width_bound_of_coverage [Fintype Right] {h : History Job Right Time}
    (law : Lawful h) (cover : CoversPriorSpends h) (G : Set Job) (S : Finset Job)
    (allCounted : ∀ j ∈ S, Counted h G j) : S.card ≤ Fintype.card Right :=
  finset_width_bound ((all_views_right_unique_iff law).2 cover) G S allCounted

open scoped BigOperators

/-- Tag each finite issuer interval with its own namespace. -/
abbrev TaggedWindow {Issuer : Type*} (F U : Issuer → ℕ) :=
  Σ i : Issuer, {n : ℕ // n ∈ Finset.Ioc (F i) (U i)}

omit [LinearOrder Time] in
theorem tagged_window_card {Issuer : Type*} [Fintype Issuer] (F U : Issuer → ℕ) :
    Fintype.card (TaggedWindow F U) = ∑ i, (U i - F i) := by
  rw [Fintype.card_sigma]
  congr 1
  ext i
  rw [Fintype.card_coe, Nat.card_Ioc]

/-- The protocol interpretation supplies the injection from tagged interval
positions to genuine job identities and proves those jobs counted in this
view. The conclusion then bounds the exact sum of issuer widths. -/
theorem issuer_width_bound [Fintype Right] {Issuer : Type*} [Fintype Issuer]
    {h : History Job Right Time} (law : Lawful h)
    (cover : CoversPriorSpends h) (G : Set Job) (F U : Issuer → ℕ)
    (jobAt : TaggedWindow F U ↪ Job)
    (positionsCounted : ∀ x, Counted h G (jobAt x)) :
    (∑ i, (U i - F i)) ≤ Fintype.card Right := by
  rw [← tagged_window_card F U]
  have unique := (all_views_right_unique_iff law).2 cover
  exact Fintype.card_le_of_injective (fun x => h.right (jobAt x))
    (fun x y e => jobAt.injective (unique G (positionsCounted x) (positionsCounted y) e))

omit [LinearOrder Time] in
/-- The grant-only mark can be smaller than the certified prefix. Normalize
issuance as the larger mark. The one-view prefix facts are semantic premises;
this theorem is the exact counted-position interpretation they entail. -/
theorem counted_iff_normalized_window {Issuer : Type*}
    {h : History Job Right Time} (G : Set Job) (slot : Job → Issuer × ℕ)
    (grantMark F : Issuer → ℕ)
    (exposedPrefix : ∀ j, Exposed h G j ↔ (slot j).2 ≤ grantMark (slot j).1)
    (certifiedPrefix : ∀ j, Certified h G j ↔ (slot j).2 ≤ F (slot j).1)
    (j : Job) :
    Counted h G j ↔ (slot j).2 ∈ Finset.Ioc (F (slot j).1)
      (max (grantMark (slot j).1) (F (slot j).1)) := by
  rw [Counted, exposedPrefix, certifiedPrefix, Finset.mem_Ioc, not_le]
  constructor
  · rintro ⟨hg,hf⟩
    exact ⟨hf, hg.trans (le_max_left _ _)⟩
  · rintro ⟨hf,hm⟩
    rcases le_max_iff.mp hm with hg | hc
    · exact ⟨hg,hf⟩
    · exact False.elim ((not_le_of_gt hf) hc)

/-- Prefix semantics plus attainment of every interval position supplies the
window bridge. No correspondence between two unrelated plant histories is
asserted. -/
theorem issuer_width_bound_from_prefixes [Fintype Right]
    {Issuer : Type*} [Fintype Issuer]
    {h : History Job Right Time} (law : Lawful h) (cover : CoversPriorSpends h)
    (G : Set Job) (slot : Job → Issuer × ℕ) (grantMark F : Issuer → ℕ)
    (exposedPrefix : ∀ j, Exposed h G j ↔ (slot j).2 ≤ grantMark (slot j).1)
    (certifiedPrefix : ∀ j, Certified h G j ↔ (slot j).2 ≤ F (slot j).1)
    (attained : ∀ x : TaggedWindow F (fun i => max (grantMark i) (F i)),
      ∃ j, slot j = (x.1, x.2.val)) :
    (∑ i, (max (grantMark i) (F i) - F i)) ≤ Fintype.card Right := by
  classical
  choose job position using attained
  have injective : Function.Injective job := by
    intro x y e
    have same : (x.1, x.2.val) = (y.1, y.2.val) :=
      (position x).symm.trans ((congrArg slot e).trans (position y))
    rcases x with ⟨i,m⟩
    rcases y with ⟨j,n⟩
    have he : i = j := congrArg Prod.fst same
    subst j
    have hm : m = n := Subtype.ext (congrArg Prod.snd same)
    cases hm
    rfl
  refine issuer_width_bound law cover G F (fun i => max (grantMark i) (F i))
    ⟨job,injective⟩ ?_
  intro x
  apply (counted_iff_normalized_window G slot grantMark F exposedPrefix certifiedPrefix (job x)).2
  simp [position x]

section PrefixPublication
variable {Issuer : Type*} [DecidableEq Issuer]

/-- In the prefix specialization each issued job has a positive slot. The
settlement bound is the certified contiguous prefix, not an individual receipt. -/
structure PrefixAtoms (h : History Job Right Time) where
  slot : Job → Issuer × ℕ
  certMark : Job → Issuer → ℕ
  positive : ∀ j, 0 < (slot j).2
  exposeIff : ∀ g j, j ∈ h.exposes g ↔
    (slot j).1 = (slot g).1 ∧ (slot j).2 ≤ (slot g).2
  certifyIff : ∀ g j, j ∈ h.certifies g ↔ (slot j).2 ≤ certMark g (slot j).1

/-- Grant-only publication does not obtain its width credit by also exposing
an unsupported issue mark. This is the maximum of authentic delivered grant
headers, while settlement evidence is taken from the same delivered atoms. -/
def publishedGrantMark {h : History Job Right Time}
    (p : PrefixAtoms (Issuer := Issuer) h) (G : Finset Job) (i : Issuer) : ℕ :=
  G.sup fun g => if i = (p.slot g).1 then (p.slot g).2 else 0

def publishedCertifiedMark {h : History Job Right Time}
    (p : PrefixAtoms (Issuer := Issuer) h) (G : Finset Job) (i : Issuer) : ℕ :=
  G.sup fun g => p.certMark g i

omit [LinearOrder Time] in
theorem exposed_iff_publishedGrantMark {h : History Job Right Time}
    (p : PrefixAtoms (Issuer := Issuer) h) (G : Finset Job) (j : Job) :
    Exposed h (G : Set Job) j ↔
      (p.slot j).2 ≤ publishedGrantMark p G (p.slot j).1 := by
  rw [publishedGrantMark, Finset.le_sup_iff (p.positive j)]
  constructor
  · rintro ⟨g, hg, hgj⟩
    obtain ⟨hi,hn⟩ := (p.exposeIff g j).mp hgj
    exact ⟨g,hg,by simpa [hi] using hn⟩
  · rintro ⟨g, hg, hn⟩
    by_cases hi : (p.slot j).1 = (p.slot g).1
    · exact ⟨g,hg,(p.exposeIff g j).mpr ⟨hi,by simpa [hi] using hn⟩⟩
    · exact False.elim ((not_le_of_gt (p.positive j)) (by simpa [hi] using hn))

omit [LinearOrder Time] [DecidableEq Issuer] in
theorem certified_iff_publishedCertifiedMark {h : History Job Right Time}
    (p : PrefixAtoms (Issuer := Issuer) h) (G : Finset Job) (j : Job) :
    Certified h (G : Set Job) j ↔
      (p.slot j).2 ≤ publishedCertifiedMark p G (p.slot j).1 := by
  rw [publishedCertifiedMark, Finset.le_sup_iff (p.positive j)]
  constructor
  · exact fun ⟨g,hg,hgj⟩ => ⟨g,hg,(p.certifyIff g j).mp hgj⟩
  · exact fun ⟨g,hg,hgj⟩ => ⟨g,hg,(p.certifyIff g j).mpr hgj⟩

/-- On a finite delivered grant view, the concrete issued mark is the maximum
of grant-only issuance and the certified prefix. All positions in the counted
interval must correspond to jobs; the protocol enforces this by consecutive
issuer slots and authentic grants. -/
theorem published_issuer_width_bound [Fintype Right] [Fintype Issuer]
    {h : History Job Right Time} (law : Lawful h) (cover : CoversPriorSpends h)
    (p : PrefixAtoms (Issuer := Issuer) h) (G : Finset Job)
    (attained : ∀ x : TaggedWindow (publishedCertifiedMark p G)
      (fun i => max (publishedGrantMark p G i) (publishedCertifiedMark p G i)),
      ∃ j, p.slot j = (x.1,x.2.val)) :
    (∑ i, (max (publishedGrantMark p G i) (publishedCertifiedMark p G i) -
      publishedCertifiedMark p G i)) ≤ Fintype.card Right :=
  issuer_width_bound_from_prefixes law cover (G : Set Job) p.slot
    (publishedGrantMark p G) (publishedCertifiedMark p G)
    (exposed_iff_publishedGrantMark p G) (certified_iff_publishedCertifiedMark p G) attained

/-- A consecutive namespace history gives the attainment premise without
any width assumption: a counted position lies below a delivered grant head,
since it is strictly above the certified prefix. -/
theorem published_issuer_width_bound_of_no_holes [Fintype Right] [Fintype Issuer]
    {h : History Job Right Time} (law : Lawful h) (cover : CoversPriorSpends h)
    (p : PrefixAtoms (Issuer := Issuer) h) (G : Finset Job)
    (noHoles : ∀ g n, 0 < n → n ≤ (p.slot g).2 →
      ∃ j, p.slot j = ((p.slot g).1,n)) :
    (∑ i, (max (publishedGrantMark p G i) (publishedCertifiedMark p G i) -
      publishedCertifiedMark p G i)) ≤ Fintype.card Right := by
  apply published_issuer_width_bound law cover p G
  rintro ⟨i,n,hn⟩
  obtain ⟨above,below⟩ := Finset.mem_Ioc.mp hn
  have positive : 0 < n := (Nat.zero_le _).trans_lt above
  have b : n ≤ publishedGrantMark p G i := by
    rcases le_max_iff.mp below with hg | hc
    · exact hg
    · exact False.elim ((not_le_of_gt above) hc)
  rw [publishedGrantMark, Finset.le_sup_iff positive] at b
  obtain ⟨g,_,hg⟩ := b
  by_cases hi : i = (p.slot g).1
  · obtain ⟨j,hj⟩ := noHoles g n positive (by simpa [hi] using hg)
    exact ⟨j,by simpa [hi] using hj⟩
  · exact False.elim ((not_le_of_gt positive) (by simpa [hi] using hg))

omit [LinearOrder Time] [DecidableEq Issuer] in
theorem normalized_width_mono_extra_certification [Fintype Issuer]
    (grantMark F F' : Issuer → ℕ) (more : ∀ i, F i ≤ F' i) :
    (∑ i, (max (grantMark i) (F' i) - F' i)) ≤
      ∑ i, (max (grantMark i) (F i) - F i) := by
  classical
  have normalize (u f : ℕ) : max u f - f = u - f := by omega
  simp only [normalize]
  generalize (Finset.univ : Finset Issuer) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact Nat.add_le_add (Nat.sub_le_sub_left (more i) (grantMark i)) ih

end PrefixPublication

#print axioms exposed_union
#print axioms certified_union
#print axioms earlier_not_both_counted
#print axioms two_atom_counterview
#print axioms all_views_right_unique_iff
#print axioms countedEmbedding
#print axioms finset_width_bound
#print axioms finset_width_bound_of_coverage
#print axioms tagged_window_card
#print axioms issuer_width_bound
#print axioms counted_iff_normalized_window
#print axioms issuer_width_bound_from_prefixes
#print axioms exposed_iff_publishedGrantMark
#print axioms certified_iff_publishedCertifiedMark
#print axioms published_issuer_width_bound
#print axioms published_issuer_width_bound_of_no_holes
#print axioms normalized_width_mono_extra_certification

end SwarmSettlement
