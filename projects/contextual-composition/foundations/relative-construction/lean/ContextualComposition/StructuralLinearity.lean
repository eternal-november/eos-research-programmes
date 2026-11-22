module
public import ContextualComposition.PartitionInverse
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v
variable {C : Type u} {K : Coeff.{u,v} C} {S : Bi K} {Z : C}
variable {F G D : Lin S Z} {η : ∀ a, K.Hom (F.obj a) (G.obj a)} {θ : ∀ a, K.Hom (G.obj a) (D.obj a)}
theorem LinSquare.seq (h : LinSquare F G η) (j : LinSquare G D θ) :
    LinSquare F D (fun a => K.seq (η a) (θ a)) where
  nil := by rw [← K.assoc, h.nil, j.nil]
  cons a b := by
    rw [← K.assoc, h.cons, K.assoc, j.cons, ← K.assoc, ← S.map_seq]
theorem LinSquare.whiskerIn (P : Lin S Z) (h : LinSquare F G η)
    (natural : ∀ {a b} (p : K.Hom a b), K.seq (F.map p) (η b) = K.seq (η a) (G.map p)) :
    LinSquare (P.comp F) (P.comp G) (fun a => η (P.obj a)) where
  nil := by
    change K.seq (K.seq F.nil (F.map P.nil)) (η (P.obj Z)) = K.seq G.nil (G.map P.nil)
    rw [K.assoc, natural, ← K.assoc, h.nil]
  cons a b := by
    change K.seq (K.seq (F.cons (P.obj a) (P.obj b)) (F.map (P.cons a b)))
        (η (P.obj (S.obj a b))) = K.seq (S.map _ _)
        (K.seq (G.cons (P.obj a) (P.obj b)) (G.map (P.cons a b)))
    rw [K.assoc, natural, ← K.assoc, h.cons, K.assoc]
theorem LinSquare.whiskerOut (P : Lin S Z) (h : LinSquare F G η) (n : LinNatural P) :
    LinSquare (F.comp P) (G.comp P) (fun a => P.map (η a)) where
  nil := by
    change K.seq (K.seq P.nil (P.map F.nil)) (P.map (η Z)) = K.seq P.nil (P.map G.nil)
    rw [K.assoc, ← P.seq, h.nil]
  cons a b := by
    change K.seq (K.seq (P.cons _ _) (P.map (F.cons a b))) (P.map (η (S.obj a b))) =
      K.seq (S.map (P.map (η a)) (P.map (η b))) (K.seq (P.cons _ _) (P.map (G.cons a b)))
    rw [K.assoc, ← P.seq, h.cons, P.seq, ← K.assoc, ← n.bin, K.assoc]
variable {T : Bi K} (R : Gather S T Z) (L : LeftGather S T Z)
structure TensorPrimitive (T : Bi K) where
  assoc (a b c : C) : K.Hom (T.obj (T.obj a b) c) (T.obj a (T.obj b c))
  unassoc (a b c : C) : K.Hom (T.obj a (T.obj b c)) (T.obj (T.obj a b) c)
  swap (a b : C) : K.Hom (T.obj a b) (T.obj b a)
  assoc_nat {a b c d e f : C} (p : K.Hom a d) (q : K.Hom b e) (r : K.Hom c f) :
    K.seq (T.map (T.map p q) r) (assoc d e f) = K.seq (assoc a b c) (T.map p (T.map q r))
  unassoc_nat {a b c d e f : C} (p : K.Hom a d) (q : K.Hom b e) (r : K.Hom c f) :
    K.seq (T.map p (T.map q r)) (unassoc d e f) = K.seq (unassoc a b c) (T.map (T.map p q) r)
  swap_nat {a b c d : C} (p : K.Hom a c) (q : K.Hom b d) :
    K.seq (T.map p q) (swap c d) = K.seq (swap a b) (T.map q p)
variable (P : TensorPrimitive T)
abbrev rf := Lin.right R
abbrev lf := Lin.left L
/-- Local compatibility of each three-factor associator and the braiding
with one additive variable, with associator orientation as in the rig.
Both binary sums and the additive zero are tested by each LinSquare. -/
structure PrimitiveLinearity : Prop where
  ar (b c : C) : LinSquare ((rf R b).comp (rf R c)) (rf R (T.obj b c)) (fun a => P.assoc a b c)
  am (a c : C) : LinSquare ((lf L a).comp (rf R c)) ((rf R c).comp (lf L a)) (fun b => P.assoc a b c)
  al (a b : C) : LinSquare (lf L (T.obj a b)) ((lf L b).comp (lf L a)) (fun c => P.assoc a b c)
  ur (b c : C) : LinSquare (rf R (T.obj b c)) ((rf R b).comp (rf R c)) (fun a => P.unassoc a b c)
  um (a c : C) : LinSquare ((rf R c).comp (lf L a)) ((lf L a).comp (rf R c)) (fun b => P.unassoc a b c)
  ul (a b : C) : LinSquare ((lf L b).comp (lf L a)) (lf L (T.obj a b)) (fun c => P.unassoc a b c)
  sr (b : C) : LinSquare (rf R b) (lf L b) (fun a => P.swap a b)
  sl (a : C) : LinSquare (lf L a) (rf R a) (fun b => P.swap a b)
def zigMiddle (a b c d : C) :=
  K.seq (P.assoc a b (T.obj c d))
    (K.seq (T.map (K.id a) (P.unassoc b c d))
      (K.seq (T.map (K.id a) (T.map (P.swap b c) (K.id d)))
        (K.seq (T.map (K.id a) (P.assoc c b d)) (P.unassoc a c (T.obj b d)))))

variable (Q : PrimitiveLinearity R L P) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
include Q in
theorem zigX (b c d : C) :
    LinSquare (leftX R b c d) (rightX R b c d) (fun a => zigMiddle P a b c d) := by
  refine (Q.ar b (T.obj c d)).seq (?_ : LinSquare (rf R (T.obj b (T.obj c d))) _ _)
  refine (rightLinear R (P.unassoc b c d)).seq ?_
  refine (rightLinear R (T.map (P.swap b c) (K.id d))).seq ?_
  exact (rightLinear R (P.assoc c b d)).seq (Q.ur c (T.obj b d))
theorem Lin.comp_assoc (A B D : Lin S Z) : (A.comp B).comp D = A.comp (B.comp D) := by
  have h₀ : K.seq D.nil (D.map (K.seq B.nil (B.map A.nil))) =
      K.seq (K.seq D.nil (D.map B.nil)) (D.map (B.map A.nil)) := by rw [D.seq, K.assoc]
  have h₁ (a b : C) : K.seq (D.cons (B.obj (A.obj a)) (B.obj (A.obj b)))
      (D.map (K.seq (B.cons (A.obj a) (A.obj b)) (B.map (A.cons a b)))) =
      K.seq (K.seq (D.cons (B.obj (A.obj a)) (B.obj (A.obj b))) (D.map (B.cons (A.obj a) (A.obj b))))
        (D.map (B.map (A.cons a b))) := by rw [D.seq, K.assoc]
  unfold Lin.comp
  congr 1
  exact funext fun a => funext fun b => h₁ a b
theorem LinSquare.rebracketTarget {A B D E : Lin S Z}
    {t : ∀ a, K.Hom (E.obj a) (D.obj (B.obj (A.obj a)))}
    (h : LinSquare E (A.comp (B.comp D)) t) : LinSquare E ((A.comp B).comp D) t where
  nil := by
    have q : (A.comp (B.comp D)).nil = ((A.comp B).comp D).nil := by
      change K.seq (K.seq D.nil (D.map B.nil)) (D.map (B.map A.nil)) =
        K.seq D.nil (D.map (K.seq B.nil (B.map A.nil)))
      rw [D.seq, K.assoc]
    exact h.nil.trans q
  cons a b := by
    have q : (A.comp (B.comp D)).cons a b = ((A.comp B).comp D).cons a b := by
      change K.seq (K.seq (D.cons _ _) (D.map (B.cons _ _))) (D.map (B.map (A.cons a b))) =
        K.seq (D.cons _ _) (D.map (K.seq (B.cons _ _) (B.map (A.cons a b))))
      rw [D.seq, K.assoc]
    exact (h.cons a b).trans (congrArg (K.seq _) q)
theorem LinSquare.rebracketSource {A B D E : Lin S Z}
    {t : ∀ a, K.Hom (D.obj (B.obj (A.obj a))) (E.obj a)}
    (h : LinSquare (A.comp (B.comp D)) E t) : LinSquare ((A.comp B).comp D) E t where
  nil := by
    change K.seq (K.seq D.nil (D.map (K.seq B.nil (B.map A.nil)))) (t Z) = E.nil
    rw [D.seq, ← K.assoc D.nil]
    exact h.nil
  cons a b := by
    change K.seq (K.seq (D.cons _ _) (D.map (K.seq (B.cons _ _) (B.map (A.cons a b))))) (t _) = _
    rw [D.seq, ← K.assoc (D.cons _ _)]
    exact h.cons a b
include Q NR NL in
theorem zigY (a b d : C) :
    LinSquare (leftY R L a b d) (rightY R L a b d) (fun c => zigMiddle P a b c d) := by
  have h1 := (Q.al a b).whiskerIn (rf R d) (fun p => by simpa only [T.map_id] using P.assoc_nat (K.id a) (K.id b) p)
  have h2 := (Q.um b d).whiskerOut (lf L a) (NL.inner a)
  have h3 := (((Q.sl b).whiskerOut (rf R d) (rightNatural R NR d)).whiskerOut (lf L a) (NL.inner a))
  have h4 := (Q.ar b d).whiskerOut (lf L a) (NL.inner a)
  have h5 := Q.um a (T.obj b d)
  have h1 := h1.rebracketTarget
  exact h1.seq (h2.seq (h3.seq (h4.seq h5)))
include Q NR NL in
theorem zigB (a c d : C) :
    LinSquare (lhsB R L a c d) (rhsB R L a c d) (fun b => zigMiddle P a b c d) := by
  have h1 := Q.am a (T.obj c d)
  have h2 := (Q.ur c d).whiskerOut (lf L a) (NL.inner a)
  have h3 := (((Q.sr c).whiskerOut (rf R d) (rightNatural R NR d)).whiskerOut (lf L a) (NL.inner a))
  have h4 := (Q.am c d).whiskerOut (lf L a) (NL.inner a)
  have h5 := (Q.ul a c).whiskerIn (rf R d) (fun p => by simpa only [T.map_id] using P.unassoc_nat (K.id a) (K.id c) p)
  have h5 := h5.rebracketSource
  exact h1.seq (h2.seq (h3.seq (h4.seq h5)))
include Q NL in
theorem zigD (a b c : C) :
    LinSquare (lhsD L a b c) (rhsD L a b c) (fun d => zigMiddle P a b c d) := by
  have h1 := (Q.al a b).whiskerIn (lf L c) (fun p => by simpa only [T.map_id] using P.assoc_nat (K.id a) (K.id b) p)
  have h2 := (Q.ul b c).whiskerOut (lf L a) (NL.inner a)
  have h3 := (NL.outer (P.swap b c)).whiskerOut (lf L a) (NL.inner a)
  have h4 := (Q.al c b).whiskerOut (lf L a) (NL.inner a)
  have h5 := (Q.ul a c).whiskerIn (lf L b) (fun p => by simpa only [T.map_id] using P.unassoc_nat (K.id a) (K.id c) p)
  have h1 := h1.rebracketTarget
  have h5 := h5.rebracketSource
  exact h1.seq (h2.seq (h3.seq (h4.seq h5)))
theorem LinSquare.reverse (h : LinSquare F G η) (i : ∀ a, Inv (η a)) :
    LinSquare G F (fun a => (i a).inv) where
  nil := by rw [← h.nil, K.assoc, (i Z).hi, K.seq_id]
  cons a b := by
    apply (i (S.obj a b)).cancelR
    rw [K.assoc, (i (S.obj a b)).ih, K.seq_id, K.assoc, h.cons,
      ← K.assoc, ← S.map_seq, (i a).ih, (i b).ih, S.map_id, K.id_seq]

/-- Only forward tensor associator and braiding compatibility. The inverse
diagrams and all middle-four diagrams are derived, not independent fields. -/
structure ForwardPrimitive : Prop where
  ar (b c : C) : LinSquare ((rf R b).comp (rf R c)) (rf R (T.obj b c)) (fun a => P.assoc a b c)
  am (a c : C) : LinSquare ((lf L a).comp (rf R c)) ((rf R c).comp (lf L a)) (fun b => P.assoc a b c)
  al (a b : C) : LinSquare (lf L (T.obj a b)) ((lf L b).comp (lf L a)) (fun c => P.assoc a b c)
  sr (b : C) : LinSquare (rf R b) (lf L b) (fun a => P.swap a b)
  sl (a : C) : LinSquare (lf L a) (rf R a) (fun b => P.swap a b)
def assocIso (hi : ∀ a b c, K.seq (P.assoc a b c) (P.unassoc a b c) = K.id _)
    (ih : ∀ a b c, K.seq (P.unassoc a b c) (P.assoc a b c) = K.id _) (a b c : C) :
    Inv (P.assoc a b c) := ⟨P.unassoc a b c,hi a b c,ih a b c⟩
theorem ForwardPrimitive.upgrade (h : ForwardPrimitive R L P)
    (hi : ∀ a b c, K.seq (P.assoc a b c) (P.unassoc a b c) = K.id _)
    (ih : ∀ a b c, K.seq (P.unassoc a b c) (P.assoc a b c) = K.id _) :
    PrimitiveLinearity R L P :=
  ⟨h.ar,h.am,h.al,fun b c => (h.ar b c).reverse (fun a => assocIso P hi ih a b c),
    fun a c => (h.am a c).reverse (fun b => assocIso P hi ih a b c),
    fun a b => (h.al a b).reverse (fun c => assocIso P hi ih a b c),h.sr,h.sl⟩
include Q NR NL in
theorem all_middle_linearity {U : C} (M : Middle T U) (present : ∀ a b c d, M.cell a b c d = zigMiddle P a b c d) :
    MedialLinear M R L ∧ MedialInner M R L := by
  exact ⟨⟨fun b c d => by simpa only [present] using zigX R L P Q b c d,
           fun a b d => by simpa only [present] using zigY R L P Q NR NL a b d⟩,
         ⟨fun a c d => by simpa only [present] using zigB R L P Q NR NL a c d,
           fun a b c => by simpa only [present] using zigD R L P Q NL a b c⟩⟩
end ContextualComposition.NativeFinitePush.DependentFibre
