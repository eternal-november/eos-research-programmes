module

public import Init

@[expose] public section

/-! Native augmented families in the reverse-function rig (disjoint sum, product).
The total coefficient type retains the address of every token. No coproduct
injection in the coefficient category or component augmentation is assumed. -/
namespace ContextualComposition.OppositeTypeFamilies
universe u
structure Family where
  Pos : Type u
  Tok : Type u
  atPos : Tok → Pos
  mark : Tok

/-- From a position-indexed coefficient family and one global augmentation
(a point of the sum, i.e. a reverse function from the tensor unit). -/
def fromFibres (X : Type u) (V : X → Type u) (a : Sigma V) : Family :=
  ⟨X, Sigma V, Sigma.fst, a⟩

structure Hom (P Q : Family.{u}) where
  f : P.Pos → Q.Pos
  back : Q.Tok → P.Tok
  over : ∀ b, f (P.atPos (back b)) = Q.atPos b
  aug : back Q.mark = P.mark

@[ext] theorem Hom.ext {P Q : Family} {h k : Hom P Q}
    (f : h.f = k.f) (b : h.back = k.back) : h = k := by
  cases h; cases k; cases f; cases b; rfl

def id (P : Family) : Hom P P := ⟨fun x => x, fun a => a, fun _ => rfl, rfl⟩
def comp {P Q R : Family} (h : Hom P Q) (k : Hom Q R) : Hom P R :=
  ⟨fun x => k.f (h.f x), fun b => h.back (k.back b),
   fun b => (congrArg k.f (h.over _)).trans (k.over b), (congrArg h.back k.aug).trans h.aug⟩
theorem id_comp {P Q} (h : Hom P Q) : comp (id P) h = h := rfl
theorem comp_id {P Q} (h : Hom P Q) : comp h (id Q) = h := rfl
theorem assoc {P Q R S} (h : Hom P Q) (k : Hom Q R) (l : Hom R S) :
    comp (comp h k) l = comp h (comp k l) := rfl

/-- Recover exactly the whole-fibre reverse functions at a fixed carrier map.
Both subtypes retain the actual token and its address constraint. -/
def Blocks (P Q : Family) (f : P.Pos → Q.Pos) :=
  (j : Q.Pos) → {b : Q.Tok // Q.atPos b = j} → {a : P.Tok // f (P.atPos a) = j}

def Hom.blocks {P Q} (h : Hom P Q) : Blocks P Q h.f :=
  fun _ b => ⟨h.back b.val, (h.over _).trans b.property⟩
def ofBlocks {P Q} (f : P.Pos → Q.Pos) (a : Blocks P Q f)
    (e : (a _ ⟨Q.mark,rfl⟩).val = P.mark) : Hom P Q :=
  ⟨f, fun b => (a _ ⟨b,rfl⟩).val, fun b => (a _ ⟨b,rfl⟩).property, e⟩
theorem ofBlocks_blocks {P Q} (h : Hom P Q) :
    ofBlocks h.f h.blocks h.aug = h := rfl
theorem blocks_ofBlocks {P Q} (f : P.Pos → Q.Pos) (a : Blocks P Q f) (e) :
    (ofBlocks f a e).blocks = a := by
  funext j b
  rcases b with ⟨b,rfl⟩
  rfl

def unit : Family.{u} := ⟨PUnit, PUnit, fun _ => ⟨⟩, ⟨⟩⟩
def terminate (P : Family) : Hom P unit := ⟨fun _ => ⟨⟩, fun _ => P.mark, fun _ => rfl, rfl⟩
theorem terminal {P : Family} (h : Hom P unit) : h = terminate P := by
  apply Hom.ext
  · rfl
  · funext b; cases b; exact h.aug

/-- Replacing a total coefficient map by its literal address fibres preserves
the entire augmented family, not merely cardinalities or inhabitation. -/
def fibreModel (P : Family) : Family :=
  fromFibres P.Pos (fun x => {a : P.Tok // P.atPos a = x}) ⟨_,P.mark,rfl⟩
def toFibres (P : Family) : Hom P (fibreModel P) :=
  ⟨fun x => x, fun a => a.2.val, fun a => a.2.property, rfl⟩
def fromTotal (P : Family) : Hom (fibreModel P) P :=
  ⟨fun x => x, fun a => ⟨_,a,rfl⟩, fun _ => rfl, rfl⟩
theorem fibres_round (P : Family) : comp (toFibres P) (fromTotal P) = id P := rfl
theorem total_round (P : Family) : comp (fromTotal P) (toFibres P) = id (fibreModel P) := by
  apply Hom.ext
  · rfl
  · funext a; rcases a with ⟨_,a,rfl⟩; rfl

/-- The marked global token selects the outer summand and then the continuation's mark. -/
def dep (P : Family) (Q : P.Pos → Family.{u}) : Family :=
  ⟨(x : P.Pos) × (Q x).Pos, (a : P.Tok) × (Q (P.atPos a)).Tok,
   fun t => ⟨P.atPos t.1, (Q _).atPos t.2⟩, ⟨P.mark,(Q _).mark⟩⟩

def castTok {X} (Q : X → Family.{u}) {x y} (p : x = y) (b : (Q x).Tok) :
    (Q y).Tok := p ▸ b

def depMap {P R : Family} {Q : P.Pos → Family.{u}} {S : R.Pos → Family.{u}}
    (h : Hom P R) (k : ∀ x, Hom (Q x) (S (h.f x))) : Hom (dep P Q) (dep R S) where
  f z := ⟨h.f z.1, (k z.1).f z.2⟩
  back z := ⟨h.back z.1, (k _).back (castTok S (h.over z.1).symm z.2)⟩
  over := by
    rintro ⟨b,c⟩
    apply Sigma.ext (h.over b)
    change HEq ((k _).f ((Q _).atPos ((k _).back _))) ((S _).atPos c)
    apply HEq.trans (heq_of_eq ((k (P.atPos (h.back b))).over _))
    have go (x y) (p : x = y) (c : (S y).Tok) : HEq ((S x).atPos (castTok S p.symm c)) ((S y).atPos c) := by cases p; rfl
    exact go _ _ (h.over b) c
  aug := by
    apply Sigma.ext h.aug
    change HEq ((k _).back (castTok S _ (S _).mark)) (Q _).mark
    have transport (x y) (p : x = y) : castTok S p (S x).mark = (S y).mark := by cases p; rfl
    rw [transport, (k _).aug]
    have go (a b : P.Tok) (p : a = b) : HEq (Q (P.atPos a)).mark (Q (P.atPos b)).mark := by cases p; rfl
    exact go _ _ h.aug

def ind {E : Type u} (P : E → Family.{u}) : Family :=
  ⟨(i : E) → (P i).Pos, (i : E) → (P i).Tok, fun a i => (P i).atPos (a i), fun i => (P i).mark⟩
def indMap {E : Type u} {P R : E → Family.{u}} (h : ∀ i, Hom (P i) (R i)) : Hom (ind P) (ind R) :=
  ⟨fun x i => (h i).f (x i), fun b i => (h i).back (b i),
   fun b => funext fun i => (h i).over (b i), funext fun i => (h i).aug⟩
theorem ind_id {E} (P : E → Family) : indMap (fun i => id (P i)) = id (ind P) := rfl
theorem ind_comp {E} {P Q R : E → Family} (h : ∀ i, Hom (P i) (Q i)) (k : ∀ i, Hom (Q i) (R i)) :
    indMap (fun i => comp (h i) (k i)) = comp (indMap h) (indMap k) := rfl

variable {E : Type u} (P : E → Family.{u}) (Q : ∀ i, (P i).Pos → Family.{u})
def shuffle : Hom (ind fun i => dep (P i) (Q i)) (dep (ind P) fun x => ind fun i => Q i (x i)) :=
  ⟨fun t => ⟨fun i => (t i).1, fun i => (t i).2⟩,
   fun t i => ⟨t.1 i,t.2 i⟩, fun _ => rfl,rfl⟩
def unshuffle : Hom (dep (ind P) fun x => ind fun i => Q i (x i)) (ind fun i => dep (P i) (Q i)) :=
  ⟨fun t i => ⟨t.1 i,t.2 i⟩,
   fun t => ⟨fun i => (t i).1, fun i => (t i).2⟩, fun _ => rfl,rfl⟩
theorem shuffle_inv : comp (shuffle P Q) (unshuffle P Q) = id _ := rfl
theorem inv_shuffle : comp (unshuffle P Q) (shuffle P Q) = id _ := rfl

/-- Projection of transport of a tuple is transport in that coordinate. -/
theorem castInd {X : E → Type u} (S : ∀ i, X i → Family.{u})
    {x y : (i : E) → X i} (p : x = y) (b : (i : E) → (S i (x i)).Tok) (i : E) :
    (castTok (fun (t : (i : E) → X i) => ind fun j => S j (t j)) p b) i =
      castTok (S i) (congrFun p i) (b i) := by cases p; rfl

/-- Naturality in both the whole-fibre outer aggregations and all
address-dependent continuations, as equality of native arrows. -/
theorem shuffle_natural {R : E → Family.{u}} {S : ∀ i, (R i).Pos → Family.{u}}
    (h : ∀ i, Hom (P i) (R i)) (k : ∀ i x, Hom (Q i x) (S i ((h i).f x))) :
    comp (indMap fun i => depMap (h i) (k i)) (shuffle R S) =
    comp (shuffle P Q) (depMap (indMap h) fun x => indMap fun i => k i (x i)) := by
  apply Hom.ext
  · rfl
  · funext t i
    dsimp only [comp, depMap, indMap, shuffle]
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    exact congrArg (k i _).back (castInd S ((indMap h).over t.1).symm t.2 i).symm

theorem dep_id (A : Family.{u}) (B : A.Pos → Family.{u}) :
    depMap (id A) (fun x => id (B x)) = id (dep A B) := rfl

/-- Dependent sections commute with transport along base equality. -/
theorem cast_back {X Y : Type u} {Q : X → Family.{u}} {S : Y → Family.{u}}
    (f : X → Y) (k : ∀ x, Hom (Q x) (S (f x))) {x y : X} (p : x = y)
    (b : (S (f x)).Tok) :
    castTok Q p ((k x).back b) = (k y).back (castTok S (congrArg f p) b) := by cases p; rfl

theorem cast_trans {X : Type u} (Q : X → Family.{u}) {x y z : X}
    (p : x = y) (q : y = z) (b : (Q x).Tok) :
    castTok Q q (castTok Q p b) = castTok Q (p.trans q) b := by cases p; cases q; rfl

theorem dep_comp {A B C : Family.{u}} {X : A.Pos → Family.{u}}
    {Y : B.Pos → Family.{u}} {Z : C.Pos → Family.{u}}
    (h : Hom A B) (l : Hom B C) (k : ∀ x, Hom (X x) (Y (h.f x)))
    (m : ∀ y, Hom (Y y) (Z (l.f y))) :
    comp (depMap h k) (depMap l m) =
      depMap (comp h l) (fun x => comp (k x) (m (h.f x))) := by
  apply Hom.ext
  · rfl
  · funext t
    dsimp only [comp, depMap, indMap, shuffle]
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply congrArg (k _).back
    exact (cast_back l.f m (h.over (l.back t.1)).symm _).trans
      (congrArg (m _).back (cast_trans Z _ _ _))

/-- Change a single sigma-addressed tensor into a tensor of tensors. -/
def regroup {I : Type u} {J : I → Type u} (T : (z : Sigma J) → Family.{u}) :
    Hom (ind T) (ind fun i => ind fun j => T ⟨i,j⟩) :=
  ⟨fun t i j => t ⟨i,j⟩, fun t z => t z.1 z.2, fun _ => rfl, rfl⟩
def ungroup {I : Type u} {J : I → Type u} (T : (z : Sigma J) → Family.{u}) :
    Hom (ind fun i => ind fun j => T ⟨i,j⟩) (ind T) :=
  ⟨fun t z => t z.1 z.2, fun t i j => t ⟨i,j⟩, fun _ => rfl, rfl⟩
theorem regroup_inv {I : Type u} {J : I → Type u} (T : Sigma J → Family.{u}) :
    comp (regroup T) (ungroup T) = id _ := rfl
theorem inv_regroup {I : Type u} {J : I → Type u} (T : Sigma J → Family.{u}) :
    comp (ungroup T) (regroup T) = id _ := rfl

/-- Independent regrouping coherence of the augmented Fubini isomorphism;
the left route shuffles once per group and once outside, the right route
shuffles at the flat address and then regroups both layers. -/
theorem shuffle_regroup {I : Type u} {J : I → Type u}
    (A : Sigma J → Family.{u}) (B : ∀ z, (A z).Pos → Family.{u}) :
    comp (regroup fun z => dep (A z) (B z))
      (comp (indMap fun i => shuffle (fun j => A ⟨i,j⟩) (fun j => B ⟨i,j⟩))
        (shuffle (fun i => ind fun j => A ⟨i,j⟩)
          (fun i x => ind fun j => B ⟨i,j⟩ (x j)))) =
    comp (shuffle A B)
      (depMap (P := ind A) (R := ind fun i => ind fun j => A ⟨i,j⟩) (Q := fun x => ind fun z => B z (x z))
        (S := fun x => ind fun i => ind fun j => B ⟨i,j⟩ (x i j))
        (regroup A) (fun x => regroup fun z => B z (x z))) := rfl

end ContextualComposition.OppositeTypeFamilies
