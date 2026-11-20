module
public import ContextualComposition.StrictSpanAlgebra
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelFold
open CategoryTheory SpanApex NativeBlocks
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {B : Type b} [Category.{max b w} B] {P : Endpoints.{b,max b w,b,max b w} B} (S : P.Split)
abbrev primitive := power S 1
variable (M : Ops (primitive S))

def snoc {n : Nat} (E : Over (power S n) (primitive S)) : Over (power S (n+1)) (primitive S) where
  functor := join M (NativeAssoc.front S n ⋙ E.functor) (NativeAssoc.last S n)
    ((congrArg (NativeAssoc.front S n ⋙ ·) E.dest).trans (NativeAssoc.boundary S n))
  source := (join_src M _ _ _).trans
    ((congrArg (NativeAssoc.front S n ⋙ ·) E.source).trans (NativeAssoc.last_src S n))
  dest := (join_dst M _ _ _).trans (NativeAssoc.last_dst S n)

/-- A diagrammatic comb on the actual native apex and native morphisms.
The singleton is literally the given primitive grade functor. -/
def comb : (n : Nat) → Over (power S n) (primitive S)
  | 0 => M.unit
  | 1 => StrictSpanAlgebra.id _
  | n+2 => snoc S M (comb (n+1))

def eval : Over (whole S) (primitive S) where
  functor := Sigma.desc fun n => (comb S M n).functor
  source := by
    fapply Functor.ext
    · rintro ⟨n,x⟩; exact Functor.congr_obj (comb S M n).source x
    · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (comb S M n).source f
  dest := by
    fapply Functor.ext
    · rintro ⟨n,x⟩; exact Functor.congr_obj (comb S M n).dest x
    · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (comb S M n).dest f

theorem eval_at (n : Nat) : incl S n ⋙ (eval S M).functor = (comb S M n).functor := rfl
theorem eval_zero : incl S 0 ⋙ (eval S M).functor = M.unit.functor := rfl
theorem eval_one : incl S 1 ⋙ (eval S M).functor = 𝟭 _ := rfl

variable {X : Type b} [Category.{max b w} X]

def read (p : NativeAssoc.Path S X) := p.2 ⋙ (comb S M p.1).functor
theorem read_src (p : NativeAssoc.Path S X) :
    read S M p ⋙ (primitive S).source = NativeAssoc.src S p :=
  congrArg (p.2 ⋙ ·) (comb S M p.1).source
theorem read_dst (p : NativeAssoc.Path S X) :
    read S M p ⋙ (primitive S).dest = NativeAssoc.dst S p :=
  congrArg (p.2 ⋙ ·) (comb S M p.1).dest
theorem read_tagged (p : NativeAssoc.Path S X) :
    NativeAssoc.tagged S p ⋙ (eval S M).functor = read S M p := rfl
theorem firstFront : NativeAssoc.front S 0 = left P := rfl
theorem firstLast : NativeAssoc.last S 0 = 𝟭 (Apex P) := rfl

theorem snoc_zero (L : Laws M) : snoc S M (n := 0) M.unit = comb S M 1 := by
  apply overExt
  change join M (NativeAssoc.front S 0 ⋙ M.unit.functor) (NativeAssoc.last S 0) _ = 𝟭 _
  exact (joinEq M (congrArg (· ⋙ M.unit.functor) (firstFront S)) (firstLast S)).trans (L.left (𝟭 _))

theorem eval_snoc (L : Laws M) (n : Nat) :
    comb S M (n+1) = snoc S M (comb S M n) := by
  cases n with
  | zero => exact (snoc_zero S M L).symm
  | succ n => rfl

theorem read_grow (L : Laws M) (p : NativeAssoc.Path S X) (G : X ⥤ Apex P)
    (h : NativeAssoc.dst S p = G ⋙ left P) :
    read S M (NativeAssoc.grow S p G h) =
      join M (read S M p) G ((read_dst S M p).trans h) := by
  let F := (NativeAssoc.grow S p G h).2
  have e : read S M (NativeAssoc.grow S p G h) = F ⋙ (snoc S M (comb S M p.1)).functor :=
    congrArg (fun k : Over (power S (p.1+1)) (primitive S) => F ⋙ k.functor) (eval_snoc S M L p.1)
  refine e.trans ((join_before M F _ _ _).trans ?_)
  exact joinEq M (congrArg (· ⋙ (comb S M p.1).functor) (NativeAssoc.grow_pre S p G h))
    (NativeAssoc.grow_last S p G h)

open NativeAssoc in
/-- Induction over the *right block*, with any fixed left block.
The equality is between actual functors and retains every native grade square. -/
theorem read_join (L : Laws M) (p q : NativeAssoc.Path S X)
    (h : NativeAssoc.dst S p = NativeAssoc.src S q) :
    read S M (NativeAssoc.join S p q h) =
      join M (read S M p) (read S M q) ((read_dst S M p).trans (h.trans (read_src S M q).symm)) := by
  revert h
  apply NativeAssoc.pathInd S (M := fun q => ∀ h : NativeAssoc.dst S p = NativeAssoc.src S q,
    read S M (NativeAssoc.join S p q h) = join M (read S M p) (read S M q)
      ((read_dst S M p).trans (h.trans (read_src S M q).symm))) _ _ q
  · intro A h
    refine (congrArg (read S M) (right_nil S p A h)).trans ?_
    exact (L.right (read S M p)).symm.trans
      (joinEq M rfl (congrArg (one M) ((read_dst S M p).trans h)))
  · intro q G k ih h
    have hq := h.trans (grow_src S q G k)
    have z := congrArg (read S M) (join_grow S p q G hq k)
    refine z.trans ((read_grow S M L _ G _).trans ?_)
    let e := (read_dst S M p).trans (hq.trans (read_src S M q).symm)
    let d := (read_dst S M q).trans k
    refine (joinEq M (e' := (join_dst M _ _ e).trans d) (ih hq) rfl).trans ?_
    refine (L.assoc (read S M p) (read S M q) G e d).trans ?_
    exact joinEq M rfl (read_grow S M L q G k).symm

end ContextualComposition.GrothendieckStep.StrictTelFold
