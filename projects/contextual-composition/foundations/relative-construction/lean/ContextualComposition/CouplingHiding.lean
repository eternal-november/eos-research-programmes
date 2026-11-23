module
public import ContextualComposition.CouplingChains
public import ContextualComposition.CouplingPossibilities

/-! Hiding the common bit admits the full endpoint possibility relation where the original diagonal couplings exclude it. -/

@[expose] public section
namespace ContextualComposition.CouplingHiding
open CouplingPullbacks AllCouplings CouplingChains CouplingPossibilities
set_option backward.isDefEq.respectTransparency false

theorem diagonal_excludes_full : ¬ Comp possibilities diagonal diagonal full := by
  rintro ⟨s,s₁,s₂,s₃⟩
  have all : (false,true) ∈ (push possibilities xz s).val := s₃ ▸ (show (false,true) ∈ full.val from trivial)
  obtain ⟨t,ht,outer⟩ := all
  change (t.1,t.2.2) = (false,true) at outer
  have h₁ : xy t ∈ diagonal.val := s₁ ▸ (show xy t ∈ (push possibilities xy s).val from ⟨t,ht,rfl⟩)
  have h₂ : yz t ∈ diagonal.val := s₂ ▸ (show yz t ∈ (push possibilities yz s).val from ⟨t,ht,rfl⟩)
  have same : t.1 = t.2.2 := h₁.trans h₂
  have lo : t.1 = false := congrArg (fun p : Bool × Bool => p.1) outer
  have hi : t.2.2 = true := congrArg (fun p : Bool × Bool => p.2) outer
  exact Bool.noConfusion (lo.symm.trans (same.trans hi))

def bit : Effect possibilities := ⟨Bool,⟨Set.univ,⟨false,trivial⟩⟩⟩
def star : Effect possibilities := ⟨Unit,⟨Set.univ,⟨(),trivial⟩⟩⟩
def keep : StateMap possibilities bit bit := ⟨id,push_id _ _⟩
def hide : StateMap possibilities bit star where
  run _ := ()
  preserves := by
    apply Subtype.ext
    ext y
    exact ⟨fun _ => trivial,fun _ => ⟨false,trivial,Subsingleton.elim () (y : Unit)⟩⟩

theorem diagonal_id : (identity possibilities bit).val = diagonal := by
  apply Subtype.ext
  ext ⟨x,y⟩
  constructor
  · rintro ⟨i,_,h⟩
    exact (congrArg Prod.fst h).symm.trans (congrArg Prod.snd h)
  · intro h
    exact ⟨x,trivial,Prod.ext rfl h⟩

def independent : Hom possibilities bit bit :=
  ⟨full,by
    have h := same_marginals
    have hh := (identity possibilities bit).property
    rw [diagonal_id] at hh
    constructor
    · exact ((pair_left possibilities full).symm.trans ((congrArg (fun p => p.val.1) h.symm).trans
        (pair_left possibilities diagonal))).trans hh.1
    · exact ((pair_right possibilities full).symm.trans ((congrArg (fun p => p.val.2) h.symm).trans
        (pair_right possibilities diagonal))).trans hh.2⟩

/-- The full joint on the unchanged outer bits separates the two composition relations. -/
theorem hiding_strict :
    ¬ compose possibilities (identity possibilities bit) (identity possibilities bit) independent ∧
    compose possibilities (change possibilities keep hide (identity possibilities bit))
      (change possibilities hide keep (identity possibilities bit)) (change possibilities keep keep independent) := by
  constructor
  · change ¬ Comp possibilities (identity possibilities bit).val (identity possibilities bit).val full
    rw [diagonal_id]; exact diagonal_excludes_full
  · let s : Poss (Bool × Unit × Bool) := ⟨Set.univ,⟨(false,(),false),trivial⟩⟩
    refine ⟨s,?_,?_,?_⟩
    · change push possibilities xy s = push possibilities (Prod.map id (fun _ : Bool => ())) (identity possibilities bit).val
      rw [diagonal_id]
      apply Subtype.ext
      ext ⟨x,y⟩
      exact ⟨fun _ => ⟨(x,x),rfl,Prod.ext rfl (Subsingleton.elim _ _)⟩,
        fun _ => ⟨(x,y,false),trivial,rfl⟩⟩
    · change push possibilities yz s = push possibilities (Prod.map (fun _ : Bool => ()) id) (identity possibilities bit).val
      rw [diagonal_id]
      apply Subtype.ext
      ext ⟨x,y⟩
      exact ⟨fun _ => ⟨(y,y),rfl,Prod.ext (Subsingleton.elim _ _) rfl⟩,
        fun _ => ⟨(false,x,y),trivial,rfl⟩⟩
    · change push possibilities xz s = push possibilities (Prod.map id id) full
      apply Subtype.ext
      ext ⟨x,y⟩
      exact ⟨fun _ => ⟨(x,y),trivial,rfl⟩,fun _ => ⟨(x,(),y),trivial,rfl⟩⟩

end ContextualComposition.CouplingHiding
