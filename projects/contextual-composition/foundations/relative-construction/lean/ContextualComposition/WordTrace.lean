module
public import ContextualComposition.CutCompositor
/-! For a moving-base arrow in a packed iterate, retain its full ordered list of primitive grade arrows (including both source and target objects) and its final moving-base payload arrow. A single layer is split with the native square equivalence, never by forgetting its dependent terminal arrow. The decoder is injective on bundled arrows, not just on vertical arrows or on objects. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.WordTrace
open CategoryTheory Opposite TelescopeSquares SpanApex NativeBlocks NativePacked BlockEvaluation
set_option backward.isDefEq.respectTransparency false
universe b w u v
/-- A directed arrow with both its objects retained. -/
structure Edge (K : Type*) [Category* K] where
  src : K
  dst : K
  hom : src ⟶ dst
namespace Edge
variable {K M R : Type*} [Category* K] [Category* M] [Category* R]
def map (F : K ⥤ M) (x : Edge K) : Edge M := ⟨F.obj x.src,F.obj x.dst,F.map x.hom⟩
theorem eq_of {a b : Edge K} (l : a.src = b.src) (r : a.dst = b.dst) (h : HEq a.hom b.hom) : a = b := by
  obtain ⟨a₁,b₁,f⟩ := a; obtain ⟨c,d,g⟩ := b; cases l; cases r; cases eq_of_heq h; rfl
theorem hom_heq {x y : Edge K} (e : x = y) : HEq x.hom y.hom := by cases e; rfl
theorem conjugate {a b c d : K} (l : a = c) (r : b = d) (f : a ⟶ b) (g : c ⟶ d) (h : HEq f g) : f = eqToHom l ≫ g ≫ eqToHom r.symm := by subst c; subst d; simp [eq_of_heq h]
theorem functor_ext {F G : K ⥤ M} (h : ∀ x, map F x = map G x) : F = G := by
  fapply Functor.ext
  · intro x; exact congrArg Edge.src (h ⟨x,x,𝟙 x⟩)
  · intro x y f
    have l := congrArg Edge.src (h ⟨x,y,f⟩)
    have r := congrArg Edge.dst (h ⟨x,y,f⟩)
    have j : HEq (F.map f) (G.map f) := hom_heq (h ⟨x,y,f⟩)
    exact conjugate l r _ _ j
end Edge
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
abbrev Pr := PackedCuts.Psh.{u,max u v,u,v} B
abbrev E (Y : Pr (B := B)) := Edge (Total Y (𝟭 B))
abbrev Atom := Edge (Apex P)
def cell (Y : Pr (B := B)) {a b : B} (u : a ⟶ b) (x : Y.obj (op a)) (y : Y.obj (op b))
    (f : x ⟶ (Y.map u.op).toFunctor.obj y) : E Y :=
  ⟨pair _ _ a x,pair _ _ b y,arrow u f⟩
def atom {a b : B} (u : a ⟶ b) {p : P.grades.obj (op a)} {q : P.grades.obj (op b)}
    (k : p ⟶ (P.grades.map u.op).toFunctor.obj q) : Atom (P := P) := cell P.grades u p q k
variable (Y : Pr (B := B))
def one (z : E (PackedFree.pow S Y 1)) : Atom (P := P) × E Y :=
  let a := gradeMap z.hom
  let x := payload _ _ z.src
  let y := payload _ _ z.dst
  let p := grade _ _ x
  let q := grade _ _ y
  let f := (squareEquiv Y S a (.cons p (.nil _)) (.cons q (.nil _)) (payload _ _ x) (payload _ _ y)).symm (payloadMap z.hom)
  (atom a f.1.1,cell Y (next a f.1.1) _ _ f.2)
theorem one_atom {a b : B} (u : a ⟶ b) {p : P.grades.obj (op a)} {q : P.grades.obj (op b)}
    (k : p ⟶ (P.grades.map u.op).toFunctor.obj q)
    (x : Y.obj (op ((P.extend a).obj p))) (y : Y.obj (op ((P.extend b).obj q)))
    (f : x ⟶ (Y.map (next u k).op).toFunctor.obj y) :
    one S Y (cell _ u (pair _ _ p x) (pair _ _ q y)
      (squareEquiv Y S u (.cons p (.nil _)) (.cons q (.nil _)) x y ⟨⟨k,PUnit.unit⟩,f⟩)) =
      (atom u k,cell Y (next u k) x y f) := by
  change (fun g : DecoratedHom Y u (.cons p (.nil _)) (.cons q (.nil _)) x y =>
    (atom u g.1.1,cell Y (next u g.1.1) x y g.2)) ((squareEquiv Y S u (.cons p (.nil _)) (.cons q (.nil _)) x y).symm ((squareEquiv Y S u (.cons p (.nil _)) (.cons q (.nil _)) x y) _)) = _
  rw [Equiv.symm_apply_apply]
def Over (a : Edge B) := Σ x : Y.obj (op a.src), Σ y : Y.obj (op a.dst), x ⟶ (Y.map a.hom.op).toFunctor.obj y
def bundle (a : Edge B) (x : Over Y a) : E Y := cell Y a.hom x.1 x.2.1 x.2.2
def unbundle (x : E Y) : Σ a : Edge B, Over Y a :=
  ⟨Edge.map gradeProjection x,payload _ _ x.src,payload _ _ x.dst,payloadMap x.hom⟩
theorem bundle_inj (a : Edge B) : Function.Injective (bundle Y a) := by
  intro x y h; exact (Sigma.mk.inj_iff.mp (show (⟨a,x⟩ : Σ a, Over Y a) = ⟨a,y⟩ from congrArg (unbundle Y) h)).2.eq
abbrev Pieces := Σ g : Atom (P := P), Over Y (Edge.map (right P S) g)
def put (h : Pieces S Y) : E (PackedFree.pow S Y 1) :=
  let g := h.1
  let q := gradeMap g.hom
  let p := payload _ _ g.src
  let r := payload _ _ g.dst
  cell _ q (pair _ _ p h.2.1) (pair _ _ r h.2.2.1)
    (squareEquiv Y S q (.cons p (.nil _)) (.cons r (.nil _)) _ _ ⟨⟨payloadMap g.hom,PUnit.unit⟩,h.2.2.2⟩)
def take (z : E (PackedFree.pow S Y 1)) : Pieces S Y :=
  let x := payload _ _ z.src
  let y := payload _ _ z.dst
  let p := grade _ _ x
  let q := grade _ _ y
  let a := gradeMap z.hom
  let f := (squareEquiv Y S a (.cons p (.nil _)) (.cons q (.nil _)) (payload _ _ x) (payload _ _ y)).symm (payloadMap z.hom)
  ⟨atom a f.1.1,payload _ _ x,payload _ _ y,f.2⟩
theorem put_take (z : E (PackedFree.pow S Y 1)) : put S Y (take S Y z) = z := by
  let x := payload _ _ z.src
  let y := payload _ _ z.dst
  let a := gradeMap z.hom
  let t : Chain P 1 _ := .cons (grade _ _ x) (.nil _)
  let w : Chain P 1 _ := .cons (grade _ _ y) (.nil _)
  let e := squareEquiv Y S a t w (payload _ _ x) (payload _ _ y)
  have h := e.apply_symm_apply (payloadMap z.hom)
  apply Edge.eq_of (a := put S Y (take S Y z)) (b := z) rfl rfl
  apply heq_of_eq
  exact congrArg (arrow (x := z.src) (y := z.dst) a) h
theorem one_injective : Function.Injective (one S Y) := by
  let emit (t : Pieces S Y) := (t.1,bundle Y (Edge.map (right P S) t.1) t.2)
  have hj : Function.Injective emit := by
    rintro ⟨g,x⟩ ⟨k,y⟩ e
    have h : g = k := congrArg Prod.fst e
    subst k; exact congrArg (Sigma.mk g) (bundle_inj Y _ (congrArg Prod.snd e))
  intro x y h
  exact (put_take S Y x).symm.trans ((congrArg (put S Y) (hj (a₁ := take S Y x) (a₂ := take S Y y) h)).trans (put_take S Y y))
abbrev Trace := List (Atom (P := P)) × E Y
def read : (n : Nat) → E (PackedFree.pow S Y n) → Trace (P := P) Y
  | 0,z => ([],z)
  | n+1,z => let t := one S (PackedFree.pow S Y n) z; let r := read n t.2; (t.1::r.1,r.2)
theorem read_injective : (n : Nat) → Function.Injective (read S Y n)
  | 0 => fun _ _ h => congrArg Prod.snd h
  | n+1 => by
    intro x y h
    apply one_injective S _
    have e := List.cons.inj (congrArg Prod.fst h)
    have k := congrArg Prod.snd h
    exact Prod.ext e.1 (read_injective n (Prod.ext e.2 k))
def atoms : {n : Nat} → {a b : B} → (u : a ⟶ b) → (t : Chain P n a) → (z : Chain P n b) → Square u t z → List (Atom (P := P))
  | 0,_,_,_,.nil _,.nil _,_ => []
  | _+1,_,_,u,.cons _ t,.cons _ z,f => atom u f.1 :: atoms (next u f.1) t z f.2
def treat {n a b} (u : a ⟶ b) (t : Chain P n a) (z : Chain P n b) (x : Y.obj (op (endpoint t))) (y : Y.obj (op (endpoint z)))
    (f : DecoratedHom Y u t z x y) : E (PackedFree.pow S Y n) :=
  cell _ u (realize Y S t x) (realize Y S z y) (squareEquiv Y S u t z x y f)
theorem read_treat : {n : Nat} → {a b : B} → (u : a ⟶ b) → (t : Chain P n a) → (z : Chain P n b) →
    (x : Y.obj (op (endpoint t))) → (y : Y.obj (op (endpoint z))) → (f : DecoratedHom Y u t z x y) →
    read S Y n (treat S Y u t z x y f) = (atoms u t z f.1,cell Y (terminalMap f.1) x y f.2)
  | 0,_,_,_,.nil _,.nil _,_,_,_ => rfl
  | n+1,_,_,u,.cons p t,.cons q z,x,y,f => by
    let k := f.1.1
    let t' : DecoratedHom Y (next u k) t z x y := ⟨f.1.2,f.2⟩
    have h : one S (PackedFree.pow S Y n) (treat S Y u (.cons p t) (.cons q z) x y f) =
        (atom u k,treat S Y (next u k) t z x y t') :=
      by
        convert one_atom S _ u k (realize Y S t x) (realize Y S z y) (squareEquiv Y S (next u k) t z x y t') using 2 <;> rfl
    unfold read
    rw [h]
    exact congrArg (fun w : Trace (P := P) Y => (atom u k :: w.1,w.2)) (read_treat (next u k) t z x y t')
theorem atoms_snoc : {n : Nat} → {a b : B} → (u : a ⟶ b) → (t : Chain P n a) → (z : Chain P n b) →
    (p : P.grades.obj (op (endpoint t))) → (q : P.grades.obj (op (endpoint z))) → (f : DecoratedHom P.grades u t z p q) →
    atoms u (Snoc.append t p) (Snoc.append z q) (Snoc.squares u t z p q f) = atoms u t z f.1 ++ [atom (terminalMap f.1) f.2]
  | 0,_,_,_,.nil _,.nil _,_,_,_ => rfl
  | _n+1,_,_,u,.cons _ t,.cons _ z,p,q,f =>
    congrArg (atom u f.1.1 :: ·) (atoms_snoc (next u f.1.1) t z p q ⟨f.1.2,f.2⟩)
def shift {G H : Pr (B := B)} (h : G = H) : E G → E H := by subst H; exact id
theorem shift_one {G H : Pr (B := B)} (h : G = H) (z : E (PackedFree.pow S G 1)) :
    one S H (shift (congrArg (fun K => PackedFree.pow S K 1) h) z) =
      ((one S G z).1,shift h (one S G z).2) := by subst H; rfl
def flattenRead (n m : Nat) (z : E (PackedCuts.family S Y n m)) : Trace (P := P) Y :=
  let p := read S (PackedFree.pow S Y m) n z
  let q := read S Y m p.2
  (p.1 ++ q.1,q.2)
theorem read_nested (m : Nat) : (n : Nat) → (z : E (PackedCuts.family S Y n m)) →
    read S Y (m+n) (shift (PackedFree.nested S Y m n) z) = flattenRead S Y n m z
  | 0,_ => rfl
  | n+1,z => by
    let H := PackedFree.nested S Y m n
    let t := one S (PackedCuts.family S Y n m) z
    have j := shift_one S H z
    change (fun (p : Atom (P := P) × E (PackedFree.pow S Y (m+n))) =>
      (p.1 :: (read S Y (m+n) p.2).1,(read S Y (m+n) p.2).2))
      (one S _ (shift (congrArg (fun K => PackedFree.pow S K 1) H) z)) = _
    rw [j]
    exact congrArg (fun w : Trace (P := P) Y => (t.1::w.1,w.2)) (read_nested m n t.2)
theorem read_transport {i j : Nat} (h : i = j) (x : E (PackedFree.pow S Y i)) :
    read S Y j (shift (congrArg (PackedFree.pow S Y) h) x) = read S Y i x := by subst j; rfl
theorem shift_trans {G H J : Pr (B := B)} (p : G = H) (q : H = J) (x : E G) :
    shift (p.trans q) x = shift q (shift p x) := by subst J; subst H; rfl
theorem read_order (n m : Nat) (z : E (PackedCuts.family S Y n m)) :
    read S Y (n+m) (shift (PackedCuts.sameLength S Y (n,m)) z) = flattenRead S Y n m z :=
  (congrArg (read S Y (n+m)) (shift_trans (PackedFree.nested S Y m n) (congrArg (PackedFree.pow S Y) (Nat.add_comm m n)) z)).trans
    ((read_transport S Y (Nat.add_comm m n) _).trans (read_nested S Y m n z))
end ContextualComposition.GrothendieckStep.WordTrace
