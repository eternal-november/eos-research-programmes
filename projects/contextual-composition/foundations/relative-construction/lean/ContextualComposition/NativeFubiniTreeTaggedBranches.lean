module
public import ContextualComposition.NativeFubiniTreeCircuitPaths
@[expose] public section

/-! The full dependent branch value travels with its occurrence tag.
Different typed histories are not collapsed to coefficient labels. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I : C} {Tag : Type w} {T : Bi (coeff (C:=C))}

abbrev TaggedBranch (I : C) := (d : OrderedDependentAugData I) × d.Branch

def Tagging.branches : {a : DependentFubiniTree I} → Tagging Tag a → a.Address → List (Tag × TaggedBranch I)
  | _, .unit, _ => []
  | _, .leaf d t, z => [(t,⟨d,z⟩)]
  | _, .fork a b, z => branches a z.1 ++ branches b z.2

theorem Tagging.branches_tags {a : DependentFubiniTree I} (s : Tagging Tag a) (z : a.Address) :
    (s.branches z).map Prod.fst = s.expr.leaves := by
  induction s with
  | unit => rfl
  | leaf => rfl
  | fork p q hp hq =>
    exact (List.map_append ..).trans (congrArg₂ List.append (hp z.1) (hq z.2))

variable {R : Type*}
omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem lookup_tag_unique (l : List (Tag × R)) (hn : (l.map Prod.fst).Nodup)
    (t : Tag) (x y : R) (hx : (t,x) ∈ l) (hy : (t,y) ∈ l) : x = y := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    have hn := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hx with e|e <;> rcases List.mem_cons.mp hy with f|f
    · exact congrArg Prod.snd (e.trans f.symm)
    · have et : t = a.1 := @congrArg (Tag × R) Tag (t,x) a Prod.fst e
      have h : a.1 ∈ l.map Prod.fst := List.mem_map.mpr ⟨(t,y),f,et⟩
      exact (hn.1 h).elim
    · have et : t = a.1 := @congrArg (Tag × R) Tag (t,y) a Prod.fst f
      have h : a.1 ∈ l.map Prod.fst := List.mem_map.mpr ⟨(t,x),e,et⟩
      exact (hn.1 h).elim
    · exact ih hn.2 e f

theorem Tagging.address_eq {a : DependentFubiniTree I} (s : Tagging Tag a) (z w : a.Address)
    (h : ∀ (t : Tag) (x y : TaggedBranch I), (t,x) ∈ s.branches z → (t,y) ∈ s.branches w → x = y) :
    z = w := by
  induction s with
  | unit => exact @Subsingleton.elim PUnit.{u+1} inferInstance z w
  | leaf d t =>
    exact eq_of_heq (Sigma.mk.inj (h t ⟨d,z⟩ ⟨d,w⟩ List.mem_cons_self List.mem_cons_self)).2
  | fork p q hp hq =>
    exact Prod.ext (hp z.1 w.1 (fun t x y h₀ h₁ => h t x y
      (List.mem_append_left _ h₀) (List.mem_append_left _ h₁)))
      (hq z.2 w.2 (fun t x y h₀ h₁ => h t x y (List.mem_append_right _ h₀) (List.mem_append_right _ h₁)))

theorem AssocMove.tagForward_branches {a b : DependentFubiniTree I} (p : AssocMove a b)
    (s : Tagging Tag a) (z : a.Address) :
    (s.branches z).Perm ((p.tagForward s).target.branches ((p.tagForward s).read z)) := by
  induction p with
  | root _ _ _ =>
    cases s with | fork ab c =>
      cases ab with | fork a b =>
        exact List.Perm.of_eq (List.append_assoc (a.branches z.1.1) (b.branches z.1.2) (c.branches z.2))
  | left p _ ih =>
    cases s with | fork a c => exact (ih a z.1).append_right (c.branches z.2)
  | right _ p ih =>
    cases s with | fork c a => exact (ih a z.2).append_left (c.branches z.1)

theorem AssocMove.tagBackward_branches {a b : DependentFubiniTree I} (p : AssocMove a b)
    (s : Tagging Tag b) (z : b.Address) :
    (s.branches z).Perm ((p.tagBackward s).target.branches ((p.tagBackward s).read z)) := by
  induction p with
  | root _ _ _ =>
    cases s with | fork a bc =>
      cases bc with | fork b c =>
        exact List.Perm.of_eq (List.append_assoc (a.branches z.1) (b.branches z.2.1) (c.branches z.2.2)).symm
  | left p _ ih =>
    cases s with | fork a c => exact (ih a z.1).append_right (c.branches z.2)
  | right _ p ih =>
    cases s with | fork c a => exact (ih a z.2).append_left (c.branches z.1)

theorem StructuralMove.tagForward_branches {a b : DependentFubiniTree I} (p : StructuralMove a b)
    (s : Tagging Tag a) (z : a.Address) :
    (s.branches z).Perm ((p.tagForward s).target.branches ((p.tagForward s).read z)) := by
  induction p with
  | assoc p => exact p.tagForward_branches s z
  | swap _ _ =>
    cases s with | fork a b =>
      exact List.perm_append_comm
  | eraseRight _ =>
    cases s with | fork a u =>
      cases u
      exact List.Perm.of_eq (List.append_nil (a.branches z.1))
  | left p _ ih =>
    cases s with | fork a c => exact (ih a z.1).append_right (c.branches z.2)
  | right _ p ih =>
    cases s with | fork c a => exact (ih a z.2).append_left (c.branches z.1)

theorem StructuralMove.tagBackward_branches {a b : DependentFubiniTree I} (p : StructuralMove a b)
    (s : Tagging Tag b) (z : b.Address) :
    (s.branches z).Perm ((p.tagBackward s).target.branches ((p.tagBackward s).read z)) := by
  induction p with
  | assoc p => exact p.tagBackward_branches s z
  | swap _ _ =>
    cases s with | fork b a =>
      exact List.perm_append_comm
  | eraseRight _ => exact List.Perm.of_eq (List.append_nil (s.branches z)).symm
  | left p _ ih =>
    cases s with | fork a c => exact (ih a z.1).append_right (c.branches z.2)
  | right _ p ih =>
    cases s with | fork c a => exact (ih a z.2).append_left (c.branches z.1)

theorem StructuralPath.tagTransport_branches {a b : DependentFubiniTree I} (p : StructuralPath a b)
    (s : Tagging Tag a) (z : a.Address) :
    (s.branches z).Perm ((p.tagTransport s).target.branches ((p.tagTransport s).read z)) := by
  induction p with
  | ident _ => exact List.Perm.refl _
  | next f g ih =>
    exact (f.tagForward_branches s z).trans (ih (f.tagForward s).target ((f.tagForward s).read z))
  | prev f g ih =>
    exact (f.tagBackward_branches s z).trans (ih (f.tagBackward s).target ((f.tagBackward s).read z))

theorem StructuralPath.read_eq_of_tags {a b : DependentFubiniTree I} (p q : StructuralPath a b)
    (s : Tagging Tag a) (hn : s.expr.leaves.Nodup)
    (h : (p.tagTransport s).target = (q.tagTransport s).target) :
    (p.tagTransport s).read = (q.tagTransport s).read := by
  apply Equiv.ext
  intro z
  have hn' : ((s.branches z).map Prod.fst).Nodup := s.branches_tags z ▸ hn
  apply Tagging.address_eq (p.tagTransport s).target
  intro t x y hx hy
  exact lookup_tag_unique (s.branches z) hn' t x y
    ((p.tagTransport_branches s z).mem_iff.mpr hx)
    ((q.tagTransport_branches s z).mem_iff.mpr (h ▸ hy))

def TaggedBranch.coeff (z : TaggedBranch I) : C := T.obj (z.1.V z.2.1) (z.1.A z.2.1 z.2.2)

theorem Tagging.matches_of_branch {a : DependentFubiniTree I} (s : Tagging Tag a) (z : a.Address) (V : Tag → C)
    (h : ∀ t x, (t,x) ∈ s.branches z → V t = TaggedBranch.coeff (T:=T) x) : s.Matches (T:=T) V z := by
  induction s with
  | unit => exact True.intro
  | leaf d t => exact h t ⟨d,z⟩ List.mem_cons_self
  | fork p q hp hq =>
    exact ⟨hp z.1 (fun t x hz => h t x (List.mem_append_left _ hz)),
      hq z.2 (fun t x hz => h t x (List.mem_append_right _ hz))⟩

theorem Tagging.exists_labels {a : DependentFubiniTree I} (s : Tagging Tag a)
    (hn : s.expr.leaves.Nodup) (z : a.Address) :
    ∃ V : Tag → C, s.Matches (T:=T) V z := by
  classical
  let l := s.branches z
  let V (t : Tag) : C :=
    if k : ∃ b, (t,b) ∈ l then TaggedBranch.coeff (T:=T) (Classical.choose k) else I
  refine ⟨V,s.matches_of_branch z V ?_⟩
  intro t b hb
  have h₀ : ∃ x, (t,x) ∈ l := ⟨b,hb⟩
  have h₁ : (l.map Prod.fst).Nodup := s.branches_tags z ▸ hn
  have h₂ := lookup_tag_unique l h₁ t (Classical.choose h₀) b (Classical.choose_spec h₀) hb
  unfold V
  rw [dite_eq_left h₀, h₂]

def resourceArity : DependentFubiniTree I → Nat
  | .unit => 0
  | .leaf _ => 1
  | .fork a b => resourceArity a + resourceArity b

/-- Canonical fresh tags count resource leaf occurrences, not unit vertices. -/
def tagsFrom (n : Nat) : (a : DependentFubiniTree I) → Tagging Nat a
  | .unit => .unit
  | .leaf A => .leaf A n
  | .fork a b => .fork (tagsFrom n a) (tagsFrom (n + resourceArity a) b)

theorem tagsFrom_leaves : (a : DependentFubiniTree I) → (n : Nat) →
    (tagsFrom n a).expr.leaves = List.range' n (resourceArity a)
  | .unit, _ => rfl
  | .leaf _, _ => rfl
  | .fork a b, n =>
    (congrArg₂ List.append (tagsFrom_leaves a n) (tagsFrom_leaves b (n + resourceArity a))).trans
      List.range'_append_1

theorem tagsFrom_nodup (a : DependentFubiniTree I) (n : Nat) : (tagsFrom n a).expr.leaves.Nodup :=
  (tagsFrom_leaves a n).symm ▸ List.nodup_range'

theorem Tagging.leaf_length {a : DependentFubiniTree I} (s : Tagging Tag a) :
    s.expr.leaves.length = resourceArity a := by
  induction s with
  | unit => rfl
  | leaf => rfl
  | fork p q hp hq => exact List.length_append.trans (congrArg₂ Nat.add hp hq)

theorem Tagging.eq_of_leaves {a : DependentFubiniTree I} (s t : Tagging Tag a)
    (h : s.expr.leaves = t.expr.leaves) : s = t := by
  induction s with
  | unit => cases t; rfl
  | leaf A x =>
    cases t with | leaf _ y =>
      have e := (List.cons.inj h).1
      subst y
      rfl
  | @fork a b s₀ s₁ i₀ i₁ =>
    cases t with | fork t₀ t₁ =>
      change s₀.expr.leaves ++ s₁.expr.leaves = t₀.expr.leaves ++ t₁.expr.leaves at h
      have e₀ := congrArg (List.take (resourceArity a)) h
      rw [List.take_left' s₀.leaf_length, List.take_left' t₀.leaf_length] at e₀
      have e₁ := congrArg (List.drop (resourceArity a)) h
      rw [List.drop_left' s₀.leaf_length, List.drop_left' t₀.leaf_length] at e₁
      rw [i₀ t₀ e₀, i₁ t₁ e₁]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
