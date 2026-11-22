module

public import ContextualComposition.DistributorShuffle

@[expose] public section

/-! Binary native Fubini on the common ragged branch presentation. There
are four independently addressed sums: parent x, parent y, continuation at x,
continuation at y. All four whole-fibre arrows remain opaque. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z U : C}
variable (M : Middle T U) (G : Gather S T Z) (L : LeftGather S T Z)
abbrev lhsB (a c d : C) := (Lin.left L a).comp (Lin.right G (T.obj c d))
abbrev rhsB (a c d : C) := (Lin.right G d).comp (Lin.left L (T.obj a c))
abbrev lhsD (a b c : C) := (Lin.left L c).comp (Lin.left L (T.obj a b))
abbrev rhsD (a b c : C) := (Lin.left L b).comp (Lin.left L (T.obj a c))
structure MedialInner : Prop where
  b (a c d : C) : LinSquare (lhsB G L a c d) (rhsB G L a c d) (fun b => M.cell a b c d)
  d (a b c : C) : LinSquare (lhsD L a b c) (rhsD L a b c) (fun d => M.cell a b c d)
variable (a c : C) (bs ds : List C)
def lhsInner :=
  K.seq (act S Z (fun b => (lhsD L a b c).collect id ds) bs)
    ((lhsB G L a c (fold S Z id ds)).collect id bs)
def rhsInner :=
  K.seq (act S Z (fun b => (rhsD L a b c).collect id ds) bs)
    ((rhsB G L a c (fold S Z id ds)).collect id bs)
theorem inner_rect (H : MedialInner M G L) :
    K.seq (lhsInner G L a c bs ds) (M.cell a (fold S Z id bs) c (fold S Z id ds)) =
    K.seq (actRect (S:=S) (Z:=Z) bs ds (fun b d => M.cell a b c d))
      (rhsInner G L a c bs ds) := by
  unfold lhsInner rhsInner actRect
  rw [K.assoc, (H.b a c _).collect id bs, ← K.assoc, act_seq]
  simp only [id_eq, (H.d a _ c).collect id ds]
  rw [← act_seq, K.assoc]

variable {X Y : Type w} (V : X → C) (W : Y → C) (xs : List X) (ys : List Y)
variable (B : X → List C) (D : Y → List C) (b d : C)
variable (β : ∀ x, K.Hom (fold S Z id (B x)) b) (θ : ∀ y, K.Hom (fold S Z id (D y)) d)
variable {a' c' : C} (α : K.Hom (fold S Z V xs) a') (γ : K.Hom (fold S Z W ys) c')
/-- Independent-then-dependent normalized schedule: aggregate the inner
rectangles, perform the separate continuations, gather outer resources,
apply separate outer merges, then shuffle the terminal resource pair. -/
def separate :=
  K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => lhsInner G L (V x) (W y) (B x) (D y)))
    (K.seq (actRect (S:=S) (Z:=Z) xs ys
      (fun x y => T.map (T.map (K.id (V x)) (β x)) (T.map (K.id (W y)) (θ y))))
      (K.seq (lhsGather G L V W xs ys b d)
        (K.seq (T.map (T.map α (K.id b)) (T.map γ (K.id d))) (M.cell a' b c' d))))
/-- Joint normalized schedule: shuffle at the actual leaf, gather the
continuation product and apply its actual pair of native merges first;
gather the parent product and apply its two parent maps last. -/
def together :=
  K.seq (actRect (S:=S) (Z:=Z) xs ys
    (fun x y => actRect (S:=S) (Z:=Z) (B x) (D y) (fun v w => M.cell (V x) v (W y) w)))
    (K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => rhsInner G L (V x) (W y) (B x) (D y)))
      (K.seq (actRect (S:=S) (Z:=Z) xs ys
        (fun x y => T.map (T.map (K.id (V x)) (K.id (W y))) (T.map (β x) (θ y))))
        (K.seq (rhsGather G L V W xs ys b d) (T.map (T.map α γ) (T.map (K.id b) (K.id d))))))

theorem ragged_binary (H : MedialLinear M G L) (P : MedialInner M G L) :
    separate M G L V W xs ys B D b d β θ α γ = together M G L V W xs ys B D b d β θ α γ := by
  unfold separate together
  rw [rectangle_dependent M G L V W xs ys b d H _ _ β θ α γ, ← K.assoc, actRect_seq]
  simp only [inner_rect M G L _ _ _ _ P]
  rw [← actRect_seq, K.assoc]
end ContextualComposition.NativeFinitePush.DependentFibre
