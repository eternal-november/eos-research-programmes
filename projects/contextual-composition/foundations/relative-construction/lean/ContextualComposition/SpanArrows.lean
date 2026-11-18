module
public import ContextualComposition.ChainSnoc
@[expose] public section
namespace ContextualComposition.GrothendieckStep.SpanApex
open CategoryTheory Opposite TelescopeSquares
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B}

abbrev PathHom {n : Nat} (x y : Points (P := P) n) := Σ a : x.1 ⟶ y.1, Square a x.2 y.2

def lastHom {n : Nat} {x y : Points (P := P) n} (p : P.grades.obj (op (endpoint x.2)))
    (q : P.grades.obj (op (endpoint y.2))) :
    (Σ f : PathHom x y, p ⟶ (P.grades.map (terminalMap f.2).op).toFunctor.obj q) ≃
      PathHom ⟨x.1,Snoc.append x.2 p⟩ ⟨y.1,Snoc.append y.2 q⟩ :=
  (show _ ≃ (Σ a : x.1 ⟶ y.1, DecoratedHom P.grades a x.2 y.2 p q) from
    ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,fun _ => rfl,fun _ => rfl⟩).trans
    (Equiv.sigmaCongrRight (fun a => Snoc.squares a x.2 y.2 p q))

def gradeArrowCast {A D A' D' : B} (l : A = A') (r : D = D') (a : A ⟶ D) (b : A' ⟶ D')
    (h : HEq a b) (p : P.grades.obj (op A)) (q : P.grades.obj (op D)) :
    (p ⟶ (P.grades.map a.op).toFunctor.obj q) ≃
      (gradeCast l p ⟶ (P.grades.map b.op).toFunctor.obj (gradeCast r q)) := by
  subst A'; subst D'; cases eq_of_heq h; exact Equiv.refl _

theorem next_gradeArrowCast {A D A' D' : B} (l : A = A') (r : D = D') (a : A ⟶ D) (b : A' ⟶ D')
    (h : HEq a b) (p : P.grades.obj (op A)) (q : P.grades.obj (op D))
    (f : p ⟶ (P.grades.map a.op).toFunctor.obj q) :
    HEq (next b (gradeArrowCast l r a b h p q f)) (next a f) := by
  subst A'; subst D'; cases eq_of_heq h; rfl

structure ArrowModel {n : Nat} {V : TwoLegs.{b,w,u,v} B} (m : PointModel (P := P) n V) where
  arrows (x y : V.apex) : (x ⟶ y) ≃ PathHom (m.decode x) (m.decode y)
  incoming {x y : V.apex} (f : x ⟶ y) : HEq ((arrows x y f).1) (V.source.map f)
  outgoing {x y : V.apex} (f : x ⟶ y) : HEq (terminalMap (arrows x y f).2) (V.dest.map f)

variable (S : P.Split)
def primitiveArrows : ArrowModel (primitivePoints (P := P) S) where
  arrows x y := (homEquiv x y).trans (Equiv.sigmaCongrRight (fun _ =>
    ⟨fun k => ⟨k,PUnit.unit⟩,fun h => h.1,fun _ => rfl,fun _ => rfl⟩))
  incoming _ := HEq.rfl
  outgoing _ := HEq.rfl

variable {n : Nat} {V : TwoLegs.{b,w,u,v} B} {m : PointModel (P := P) n V}
def stepArrows (M : ArrowModel m) (x y : (append P S V).apex) :
    (x ⟶ y) ≃ PathHom ((pointStep S m).decode x) ((pointStep S m).decode y) :=
  (homEquiv x y).trans ((Equiv.sigmaCongr (M.arrows (grade _ _ x) (grade _ _ y))
    (fun k => gradeArrowCast (m.dest_eq (grade _ _ x)).symm (m.dest_eq (grade _ _ y)).symm
      (V.dest.map k) (terminalMap (M.arrows _ _ k).2) (M.outgoing k).symm (payload _ _ x) (payload _ _ y))).trans
    (lastHom (gradeCast (m.dest_eq (grade _ _ x)).symm (payload _ _ x))
      (gradeCast (m.dest_eq (grade _ _ y)).symm (payload _ _ y))))

def successorArrows (M : ArrowModel m) : ArrowModel (pointStep S m) where
  arrows := stepArrows S M
  incoming f := M.incoming (gradeMap f)
  outgoing {x y} f := (Snoc.terminal_append _ _ _ _ _ _).trans
    (next_gradeArrowCast (m.dest_eq (grade _ _ x)).symm (m.dest_eq (grade _ _ y)).symm
      (V.dest.map (gradeMap f)) (terminalMap (M.arrows _ _ (gradeMap f)).2)
      (M.outgoing (gradeMap f)).symm (payload _ _ x) (payload _ _ y) (payloadMap f))

def powerArrows : (n : Nat) → ArrowModel (powerPoints (P := P) S n)
  | 0 => primitiveArrows S
  | n+1 => successorArrows S (powerArrows n)

private theorem rebase_heq {A D : B} {n : Nat} {x : Chain P n A} {y : Chain P n D} {a b : A ⟶ D}
    (h : a = b) (t : Square a x y) : HEq (rebaseSquare h t) t := by subst b; rfl

/-- Restrict the total bijection to an independently prescribed incoming base arrow.
The native side lies over that arrow after the two object endpoint equalities. -/
def overArrow (M : ArrowModel m) (x y : V.apex)
    (a : (m.decode x).1 ⟶ (m.decode y).1) :
    {f : x ⟶ y // HEq (V.source.map f) a} ≃ Square a (m.decode x).2 (m.decode y).2 where
  toFun f := rebaseSquare (eq_of_heq ((M.incoming f.1).trans f.2)) (M.arrows x y f.1).2
  invFun t := ⟨(M.arrows x y).symm ⟨a,t⟩,by
    refine (M.incoming _).symm.trans ?_
    rw [(M.arrows x y).apply_symm_apply]⟩
  left_inv f := by
    apply Subtype.ext
    apply (M.arrows x y).injective
    rw [(M.arrows x y).apply_symm_apply]
    apply Sigma.ext (eq_of_heq ((M.incoming f.1).trans f.2)).symm
    exact rebase_heq _ _
  right_inv t := by
    apply eq_of_heq
    refine (rebase_heq _ _).trans ?_
    exact (Sigma.ext_iff.mp ((M.arrows x y).apply_symm_apply ⟨a,t⟩)).2

theorem overArrow_terminal (M : ArrowModel m) (x y : V.apex) (a : (m.decode x).1 ⟶ (m.decode y).1)
    (f : {g : x ⟶ y // HEq (V.source.map g) a}) :
    HEq (terminalMap (u := a) (t := (m.decode x).2) (z := (m.decode y).2) (overArrow M x y a f))
      (V.dest.map f.1) :=
  (heq_of_eq (terminal_rebase _ _)).trans (M.outgoing f.1)

theorem last_rebase {A D : B} {a b : A ⟶ D} (h : a = b) (t : Chain P n A) (z : Chain P n D)
    (x : P.grades.obj (op (endpoint t))) (y : P.grades.obj (op (endpoint z))) (f : DecoratedHom P.grades a t z x y) :
    Snoc.squares b t z x y (rebaseDecorated P.grades h f) = rebaseSquare h (Snoc.squares a t z x y f) := by
  subst b; rfl

set_option backward.isDefEq.respectTransparency false in
theorem last_identity : {n : Nat} → {A : B} → (t : Chain P n A) → (x : P.grades.obj (op (endpoint t))) →
    Snoc.squares (𝟙 A) t t x x (decoratedId S P.grades t x) = squareId S (Snoc.append t x)
  | 0, _, .nil _, _ => rfl
  | n+1, A, .cons p t, x => by
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    change Snoc.squares _ t t x x (tailPart P.grades (decoratedId S P.grades (.cons p t) x)) =
      rebaseSquare _ (squareId S (Snoc.append t x))
    rw [tail_identity P.grades S p t x,last_rebase,@last_identity n]

set_option backward.isDefEq.respectTransparency false in
theorem last_paste : {n : Nat} → {A D E : B} → {a : A ⟶ D} → {b : D ⟶ E} →
    (t : Chain P n A) → (z : Chain P n D) → (w : Chain P n E) →
    (x : P.grades.obj (op (endpoint t))) → (y : P.grades.obj (op (endpoint z))) → (v : P.grades.obj (op (endpoint w))) →
    (f : DecoratedHom P.grades a t z x y) → (g : DecoratedHom P.grades b z w y v) →
    Snoc.squares (a ≫ b) t w x v (decoratedComp S P.grades f g) =
      squareComp S (Snoc.squares a t z x y f) (Snoc.squares b z w y v g)
  | 0, _, _, _, _, _, .nil _, .nil _, .nil _, _, _, _, _, _ => rfl
  | n+1, _, _, _, _, _, .cons p t, .cons q z, .cons r w, x, y, v, f, g => by
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    change Snoc.squares _ t w x v (tailPart P.grades (decoratedComp S P.grades f g)) =
      rebaseSquare _ (squareComp S (Snoc.squares _ t z x y (tailPart P.grades f)) (Snoc.squares _ z w y v (tailPart P.grades g)))
    rw [tail_paste P.grades S f g,last_rebase,@last_paste n]

def pathId (x : Points (P := P) n) : PathHom x x := ⟨𝟙 _,squareId S x.2⟩

def pathPaste {x y z : Points (P := P) n} (f : PathHom x y) (g : PathHom y z) : PathHom x z :=
  ⟨f.1 ≫ g.1,squareComp S f.2 g.2⟩

private theorem cast_id_heq {A A' : B} (l : A = A') (a : A ⟶ A) (b : A' ⟶ A') (h : HEq a b)
    (p : P.grades.obj (op A)) (k : p ⟶ (P.grades.map a.op).toFunctor.obj p) (j : HEq k (𝟙 p)) :
    HEq (gradeArrowCast l l a b h p p k) (𝟙 (gradeCast l p)) := by
  subst A'; cases eq_of_heq h; exact j

private theorem native_id_heq {K : Type*} [Category* K] {e : K ⥤ B} (x : Total P.grades e) :
    HEq (payloadMap (𝟙 x)) (𝟙 (payload P.grades e x)) := by
  change HEq ((Grothendieck.Hom.fiber (𝟙 x.unop)).unop) _
  rw [Grothendieck.id_fiber]
  refine HEq.trans (heq_of_eq (eqToHom_unop (C := (P.grades.obj (op (e.obj (grade _ _ x))) : Type _)) _)) ?_
  exact eqToHom_heq_id_dom _ _ _

theorem step_id (M : ArrowModel m) (law : ∀ x, M.arrows x x (𝟙 x) = pathId S (m.decode x))
    (x : (append P S V).apex) :
    (successorArrows S M).arrows x x (𝟙 x) = pathId S ((pointStep S m).decode x) := by
  let k := grade P.grades V.dest x
  let p := gradeCast (P := P) (m.dest_eq k).symm (payload P.grades V.dest x)
  let j : Σ f : PathHom (m.decode k) (m.decode k), p ⟶ (P.grades.map (terminalMap f.2).op).toFunctor.obj p :=
    ⟨⟨𝟙 _,(decoratedId S P.grades (m.decode k).2 p).1⟩,(decoratedId S P.grades (m.decode k).2 p).2⟩
  have hj : lastHom p p j = pathId S ((pointStep S m).decode x) := by
    apply Sigma.ext (by rfl)
    exact heq_of_eq (last_identity S _ _)
  rw [← hj]
  apply congrArg (lastHom p p)
  refine Sigma.ext (law k) ?_
  refine (cast_id_heq _ _ _ _ _ _ (native_id_heq x)).trans ?_
  exact (show HEq (decoratedId S P.grades (m.decode k).2 p).2 (𝟙 p) from eqToHom_heq_id_dom _ _ (by rw [terminal_id,op_id,P.grades.map_id]; rfl)).symm

theorem power_id : (n : Nat) → (x : (positivePowers P S n).apex) →
    (powerArrows S n).arrows x x (𝟙 x) = pathId S ((powerPoints S n).decode x)
  | 0, x => by
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    refine Sigma.ext ?_ ?_
    · apply eq_of_heq
      exact (native_id_heq x).trans (show HEq (headId (P := P) (payload _ _ x)) (𝟙 _) from eqToHom_heq_id_dom _ _ _).symm
    · exact HEq.rfl
  | n+1, x => step_id S _ (power_id n) x

private theorem dropFinal {C : Type*} [Category* C] {x y z z' : C} (f : x ⟶ y) (g : y ⟶ z) (h : z = z') :
    HEq (f ≫ g ≫ eqToHom h) (f ≫ g) := by subst z'; simp

private theorem cast_grade_comp {A D E A' D' E' : B} (l : A = A') (m : D = D') (r : E = E')
    (a : A ⟶ D) (b : D ⟶ E) (c : A ⟶ E) (a' : A' ⟶ D') (b' : D' ⟶ E') (c' : A' ⟶ E')
    (ha : HEq a a') (hb : HEq b b') (hc : HEq c c')
    (p : P.grades.obj (op A)) (q : P.grades.obj (op D)) (s : P.grades.obj (op E))
    (k : p ⟶ (P.grades.map a.op).toFunctor.obj q) (j : q ⟶ (P.grades.map b.op).toFunctor.obj s)
    (h : (P.grades.map a.op).toFunctor.obj ((P.grades.map b.op).toFunctor.obj s) = (P.grades.map c.op).toFunctor.obj s) :
    HEq (gradeArrowCast l r c c' hc p s (k ≫ (P.grades.map a.op).toFunctor.map j ≫ eqToHom h))
      ((gradeArrowCast l m a a' ha p q k) ≫ (P.grades.map a'.op).toFunctor.map (gradeArrowCast m r b b' hb q s j)) := by
  subst A'; subst D'; subst E'; cases eq_of_heq ha; cases eq_of_heq hb; cases eq_of_heq hc
  exact dropFinal _ _ _

def prefixData (M : ArrowModel m) {x y : (append P S V).apex} (f : x ⟶ y) :
    Σ h : PathHom (m.decode (grade _ _ x)) (m.decode (grade _ _ y)),
      gradeCast (m.dest_eq (grade _ _ x)).symm (payload _ _ x) ⟶
        (P.grades.map (terminalMap h.2).op).toFunctor.obj (gradeCast (m.dest_eq (grade _ _ y)).symm (payload _ _ y)) :=
  ⟨M.arrows _ _ (gradeMap f),gradeArrowCast _ _ _ _ (M.outgoing (gradeMap f)).symm _ _ (payloadMap f)⟩

def pasteData {n : Nat} {x y z : Points (P := P) n}
    {p : P.grades.obj (op (endpoint x.2))} {q : P.grades.obj (op (endpoint y.2))} {r : P.grades.obj (op (endpoint z.2))}
    (f : Σ h : PathHom x y, p ⟶ (P.grades.map (terminalMap h.2).op).toFunctor.obj q)
    (g : Σ h : PathHom y z, q ⟶ (P.grades.map (terminalMap h.2).op).toFunctor.obj r) :
    Σ h : PathHom x z, p ⟶ (P.grades.map (terminalMap h.2).op).toFunctor.obj r :=
  ⟨pathPaste S f.1 g.1,(decoratedComp S P.grades (⟨f.1.2,f.2⟩ : DecoratedHom P.grades f.1.1 x.2 y.2 p q)
    (⟨g.1.2,g.2⟩ : DecoratedHom P.grades g.1.1 y.2 z.2 q r)).2⟩

theorem lastHom_paste {n : Nat} {x y z : Points (P := P) n} {p : P.grades.obj (op (endpoint x.2))}
    {q : P.grades.obj (op (endpoint y.2))} {r : P.grades.obj (op (endpoint z.2))}
    (f : Σ h : PathHom x y, p ⟶ (P.grades.map (terminalMap h.2).op).toFunctor.obj q)
    (g : Σ h : PathHom y z, q ⟶ (P.grades.map (terminalMap h.2).op).toFunctor.obj r) :
    lastHom p r (pasteData S f g) = pathPaste S (lastHom p q f) (lastHom q r g) :=
  Sigma.ext (by rfl) (heq_of_eq (last_paste S x.2 y.2 z.2 p q r ⟨f.1.2,f.2⟩ ⟨g.1.2,g.2⟩))

set_option backward.isDefEq.respectTransparency false in
theorem step_paste (M : ArrowModel m)
    (law : ∀ {x y z : V.apex} (f : x ⟶ y) (g : y ⟶ z),
      M.arrows _ _ (f ≫ g) = pathPaste S (M.arrows _ _ f) (M.arrows _ _ g))
    {x y z : (append P S V).apex} (f : x ⟶ y) (g : y ⟶ z) :
    (successorArrows S M).arrows _ _ (f ≫ g) =
      pathPaste S ((successorArrows S M).arrows _ _ f) ((successorArrows S M).arrows _ _ g) := by
  change lastHom _ _ (prefixData S M (f ≫ g)) = pathPaste S (lastHom _ _ (prefixData S M f)) (lastHom _ _ (prefixData S M g))
  rw [← lastHom_paste S (prefixData S M f) (prefixData S M g)]
  apply congrArg
  refine Sigma.ext (law (gradeMap f) (gradeMap g)) ?_
  change HEq (gradeArrowCast _ _ _ _ _ _ _ (payloadMap (f ≫ g))) (_ ≫ _ ≫ eqToHom _)
  rw [payload_comp]
  refine (cast_grade_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans (dropFinal _ _ _).symm

theorem power_paste : (n : Nat) → {x y z : (positivePowers P S n).apex} → (f : x ⟶ y) → (g : y ⟶ z) →
    (powerArrows S n).arrows _ _ (f ≫ g) = pathPaste S ((powerArrows S n).arrows _ _ f) ((powerArrows S n).arrows _ _ g)
  | 0, _, _, _, f, g => by
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    refine Sigma.ext (payload_comp f g) ?_
    exact HEq.rfl
  | n+1, _, _, _, f, g => step_paste S _ (@power_paste n) f g

@[instance_reducible] def chainCategory (n : Nat) : Category (Points (P := P) (n+1)) where
  Hom := PathHom
  id := pathId S
  comp := pathPaste S
  id_comp {x y} f := by
    obtain ⟨x,rfl⟩ := (powerPoints S n).decode.surjective x
    obtain ⟨y,rfl⟩ := (powerPoints S n).decode.surjective y
    obtain ⟨k,rfl⟩ := ((powerArrows S n).arrows x y).surjective f
    change pathPaste S (pathId S _) _ = _
    rw [← power_id S n x,← power_paste,Category.id_comp]
  comp_id {x y} f := by
    obtain ⟨x,rfl⟩ := (powerPoints S n).decode.surjective x
    obtain ⟨y,rfl⟩ := (powerPoints S n).decode.surjective y
    obtain ⟨k,rfl⟩ := ((powerArrows S n).arrows x y).surjective f
    change pathPaste S _ (pathId S _) = _
    rw [← power_id S n y,← power_paste,Category.comp_id]
  assoc {x y z w} f g h := by
    obtain ⟨x,rfl⟩ := (powerPoints S n).decode.surjective x
    obtain ⟨y,rfl⟩ := (powerPoints S n).decode.surjective y
    obtain ⟨z,rfl⟩ := (powerPoints S n).decode.surjective z
    obtain ⟨w,rfl⟩ := (powerPoints S n).decode.surjective w
    obtain ⟨i,rfl⟩ := ((powerArrows S n).arrows x y).surjective f
    obtain ⟨j,rfl⟩ := ((powerArrows S n).arrows y z).surjective g
    obtain ⟨k,rfl⟩ := ((powerArrows S n).arrows z w).surjective h
    change pathPaste S (pathPaste S _ _) _ = pathPaste S _ (pathPaste S _ _)
    simp only [← power_paste,Category.assoc]

def chainApex (n : Nat) := @Cat.of (Points (P := P) (n+1)) (chainCategory S n)

def powerComparison (n : Nat) : (positivePowers P S n).apex ⥤ chainApex S n where
  obj := (powerPoints S n).decode
  map := (powerArrows S n).arrows _ _ 
  map_id := power_id S n
  map_comp := power_paste S n

instance powerFull (n : Nat) : (powerComparison S n).Full where
  map_surjective := ((powerArrows S n).arrows _ _).surjective
instance powerFaithful (n : Nat) : (powerComparison S n).Faithful where
  map_injective {x y} := ((powerArrows S n).arrows x y).injective
instance powerEssSurj (n : Nat) : (powerComparison S n).EssSurj where
  mem_essImage x := ⟨(powerPoints S n).decode.symm x,⟨eqToIso ((powerPoints S n).decode.apply_symm_apply x)⟩⟩
instance powerIsEquivalence (n : Nat) : (powerComparison S n).IsEquivalence where

noncomputable def powerEquivalence (n : Nat) : (positivePowers P S n).apex ≌ chainApex S n :=
  (powerComparison S n).asEquivalence

def chainSource (n : Nat) : chainApex S n ⥤ B where
  obj x := x.1
  map f := f.1

def chainDest (n : Nat) : chainApex S n ⥤ B where
  obj x := endpoint x.2
  map f := terminalMap f.2
  map_id x := terminal_id S x.2
  map_comp f g := terminal_comp S f.2 g.2

private theorem square_of_heq {A D A' D' : B} (l : A = A') (r : D = D') (a : A ⟶ D) (b : A' ⟶ D') (h : HEq a b) :
    a = eqToHom l ≫ b ≫ eqToHom r.symm := by subst A'; subst D'; simp [eq_of_heq h]

theorem comparison_source (n : Nat) : powerComparison S n ⋙ chainSource S n = (positivePowers P S n).source :=
  Functor.ext (powerPoints S n).source_eq (fun x y f => square_of_heq ((powerPoints S n).source_eq x) ((powerPoints S n).source_eq y) _ _ ((powerArrows S n).incoming f))

theorem comparison_dest (n : Nat) : powerComparison S n ⋙ chainDest S n = (positivePowers P S n).dest :=
  Functor.ext (powerPoints S n).dest_eq (fun x y f => square_of_heq ((powerPoints S n).dest_eq x) ((powerPoints S n).dest_eq y) _ _ ((powerArrows S n).outgoing f))

end ContextualComposition.GrothendieckStep.SpanApex
