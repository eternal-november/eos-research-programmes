module
public import ContextualComposition.WordTrace
/-! Compute the same directed word from the native snoc apices and from the head-recursive packed evaluator. The square-to-snoc calculation records the endpoint transport of the last grade. The cut calculation uses the two projections of the actual strict native cut, not addition of tags. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeTrace
open CategoryTheory Opposite TelescopeSquares SpanApex NativeBlocks NativePacked BlockEvaluation WordTrace
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
def word : (n : Nat) → Edge (power S n).apex → List (Atom (P := P))
  | 0,_ => []
  | n+1,z => word n (Edge.map (NativeAssoc.front S n) z) ++ [Edge.map (NativeAssoc.last S n) z]
theorem castAtom {A D A' D' : B} (l : A = A') (r : D = D') (a : A ⟶ D) (b : A' ⟶ D') (h : HEq a b)
    (p : P.grades.obj (op A)) (q : P.grades.obj (op D)) (f : p ⟶ (P.grades.map a.op).toFunctor.obj q) :
    atom b (gradeArrowCast l r a b h p q f) = atom a f := by subst A'; subst D'; cases eq_of_heq h; rfl
def decoded (n : Nat) (z : Edge (chainApex S n)) := atoms z.hom.1 z.src.2 z.dst.2 z.hom.2
theorem decode_word : (n : Nat) → (z : Edge (power S (n+1)).apex) →
    decoded S n (Edge.map (powerComparison S n) z) = word S (n+1) z
  | 0,_ => rfl
  | n+1,z => by
    let g := Edge.map gradeProjection z
    let m := powerPoints S n
    let M := powerArrows S n
    let p := payload _ _ z.src
    let q := payload _ _ z.dst
    let f := (M.arrows _ _ g.hom)
    let hp := (m.dest_eq g.src).symm
    let hq := (m.dest_eq g.dst).symm
    let a := (power S (n+1)).dest.map g.hom
    let b := terminalMap f.2
    let j := (M.outgoing g.hom).symm
    let k := gradeArrowCast hp hq a b j p q (payloadMap z.hom)
    have T := atoms_snoc f.1 (m.decode g.src).2 (m.decode g.dst).2 (gradeCast hp p) (gradeCast hq q) ⟨f.2,k⟩
    exact T.trans (congrArg₂ (· ++ ·) (decode_word n g) (congrArg ([·]) (castAtom hp hq a b j p q (payloadMap z.hom))))
variable (Y : Pr (B := B))
abbrev leaf {K : Type*} [Category* K] (e : K ⥤ B) := second (BoundaryPaste.projectionData Y) e
theorem leaf_total {K L : Type*} [Category* K] [Category* L] (r : K ⥤ L) (d : L ⥤ B) {e : K ⥤ B}
    (h : r ⋙ d = e) : SpanPayload.totalMap Y r d h ⋙ leaf Y d = leaf Y e := by subst e; rfl
theorem read_global : (n : Nat) → (z : Edge (Total Y (power S n).dest)) →
    read S Y n (Edge.map (global S Y n) z) = (word S n (Edge.map gradeProjection z),Edge.map (leaf Y _) z)
  | 0,_ => rfl
  | n+1,z => by
    let V := SpanPayload.Power.global S n Y
    let w := Edge.map V z
    have h := read_treat S Y (gradeMap w.hom).1 (grade _ _ w.src).2 (grade _ _ w.dst).2
      (payload _ _ w.src) (payload _ _ w.dst) (NativeCleavage.Evaluation.raw S Y w.hom)
    apply h.trans
    apply Prod.ext
    · let e := SpanPayload.total_projection Y (powerComparison S n) _ (comparison_dest S n)
      exact (congrArg (fun F => decoded S n (Edge.map F z)) e).trans (decode_word S n (Edge.map gradeProjection z))
    · exact congrArg (fun F => Edge.map F z) (leaf_total Y (powerComparison S n) _ (comparison_dest S n))
theorem cut_first (n m : Nat) : (blocks S n (m+1)).first = NativeAssoc.front S (n+m) ⋙ (blocks S n m).first := by cases n <;> cases m <;> rfl
theorem cut_rest (n m : Nat) : (blocks S n (m+1)).rest ⋙ NativeAssoc.front S m = NativeAssoc.front S (n+m) ⋙ (blocks S n m).rest := by
  cases n <;> cases m <;> exact Cut.nextRest_pre S _
theorem cut_tip (n m : Nat) : (blocks S n (m+1)).rest ⋙ NativeAssoc.last S m = NativeAssoc.last S (n+m) := by
  cases n <;> cases m <;> exact Cut.nextRest_grade S _
theorem word_cut (n : Nat) : (m : Nat) → (z : Edge (power S (n+m)).apex) →
    word S n (Edge.map (blocks S n m).first z) ++ word S m (Edge.map (blocks S n m).rest z) = word S (n+m) z
  | 0,z => List.append_nil _
  | m+1,z => by
    let F := NativeAssoc.front S (n+m)
    have a := congrArg (fun H => word S n (Edge.map H z)) (cut_first S n m)
    have b := congrArg (fun H => word S m (Edge.map H z)) (cut_rest S n m)
    have d := congrArg (fun H => Edge.map H z) (cut_tip S n m)
    exact (congrArg₂ (· ++ ·) a (congrArg₂ (· ++ ·) b (congrArg ([·]) d))).trans
      ((List.append_assoc ..).symm.trans (congrArg (· ++ [_]) (word_cut n m (Edge.map F z))))
end ContextualComposition.GrothendieckStep.NativeTrace
