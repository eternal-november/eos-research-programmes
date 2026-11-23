module

public import ContextualComposition.StrictCornerRecognition

/-! The intrinsic corner category for the filled, opcartesian part of
Štěpán's factorization double categories. Its arrows retain corners modulo
zigzags of actual right-identity squares. -/

@[expose] public section
namespace ContextualComposition.OrthogonalCornerCategory
open CategoryTheory StrictCornerRecognition
universe u v w s
variable {O : Type u} [Category.{v} O] [Category.{w} (HObj O)]
variable (S : Faces.{u,v,w,s} O)
variable {a b c d i j k : O}

/-- Vertical opcartesian lifting of a square after factoring its right side. -/
structure Extension {m : Horiz a b} {e : a ⟶ i} {v : b ⟶ c} {n : Horiz i c}
    (l : S.Sq m e v n) {r : c ⟶ d} {w : a ⟶ j} {g : Horiz j d} (h : S.Sq m w (v ≫ r) g) where
  middle : i ⟶ j
  factor : e ≫ middle = w
  face : S.Sq n middle r g
  pastes : HEq (S.vp l face) h

def Opcartesian {m : Horiz a b} {e : a ⟶ i} {v : b ⟶ c} {n : Horiz i c} (l : S.Sq m e v n) :=
  ∀ {d j : O} {r : c ⟶ d} {w : a ⟶ j} {g : Horiz j d} (h : S.Sq m w (v ≫ r) g),
    Unique (Extension S l h)

structure Filled where
  fill : ∀ {a b c : O} (m : Horiz a b) (v : b ⟶ c), Filler S m v
  opcartesian : ∀ {a b c i : O} {m : Horiz a b} {e : a ⟶ i} {v : b ⟶ c} {n : Horiz i c}
    (l : S.Sq m e v n), Opcartesian S l

structure Step (p q : Corner a b) where
  mid : p.mid ⟶ q.mid
  left_eq : p.e ≫ mid = q.e
  face : S.Sq p.m mid (𝟙 b) q.m

abbrev Ar (a b : O) := Quot (fun p q : Corner a b => Nonempty (Step S p q))
def mk (p : Corner a b) : Ar S a b := Quot.mk _ p

variable (K : Filled S)

def fillerStep {m : Horiz a b} {v : b ⟶ c} (f g : Filler S m v) : Step S f.corner g.corner := by
  let h : S.Sq m g.corner.e (v ≫ 𝟙 c) g.corner.m := (Category.comp_id v).symm ▸ g.face
  let t := (K.opcartesian f.face h).default
  exact ⟨t.middle,t.factor,t.face⟩

def postHorizontal (x : Ar S i a) (m : Horiz a b) : Ar S i b := by
  refine Quot.lift (fun p => mk S (postH p m)) ?_ x
  rintro p q ⟨t⟩
  exact Quot.sound ⟨⟨t.mid,t.left_eq,S.hp t.face (S.idV m)⟩⟩

def appendV (p : Corner i a) (v : a ⟶ b) : Corner i b :=
  let q := (K.fill p.m v).corner
  ⟨q.mid,p.e ≫ q.e,q.m⟩

theorem appendV_using (p : Corner i a) {v : a ⟶ b} (f : Filler S p.m v) :
    mk S (appendV S K p v) = mk S ⟨f.corner.mid,p.e ≫ f.corner.e,f.corner.m⟩ := by
  let t := fillerStep S K (K.fill p.m v) f
  exact Quot.sound ⟨⟨t.mid,(Category.assoc ..).trans (congrArg (p.e ≫ ·) t.left_eq),t.face⟩⟩

def postVertical (x : Ar S i a) (v : a ⟶ b) : Ar S i b := by
  refine Quot.lift (fun p => mk S (appendV S K p v)) ?_ x
  rintro p q ⟨t⟩
  let f := K.fill q.m v
  let composite : S.Sq p.m (t.mid ≫ f.corner.e) v f.corner.m := by simpa using S.vp t.face f.face
  refine (appendV_using S K p ⟨⟨f.corner.mid,t.mid ≫ f.corner.e,f.corner.m⟩,composite⟩).trans ?_
  change mk S ⟨_, p.e ≫ t.mid ≫ _,_⟩ = mk S ⟨_, q.e ≫ _,_⟩
  rw [← Category.assoc,t.left_eq]

theorem postVertical_mk (p : Corner i a) {v : a ⟶ b} {e : p.mid ⟶ j} {n : Horiz j b}
    (h : S.Sq p.m e v n) : postVertical S K (mk S p) v = mk S ⟨j,p.e ≫ e,n⟩ :=
  appendV_using S K p ⟨⟨j,e,n⟩,h⟩

theorem postH_id (p : Ar S i a) : postHorizontal S p (𝟙 _) = p := by
  induction p using Quot.ind with
  | _ p => change mk S ⟨p.mid,p.e,p.m ≫ 𝟙 _⟩ = _; simp [mk]

theorem postV_id (p : Ar S i a) : postVertical S K p (𝟙 _) = p := by
  induction p using Quot.ind with
  | _ p =>
    change postVertical S K (mk S p) _ = _
    rw [postVertical_mk S K p (S.idV p.m)]
    simp [mk]

theorem postH_paste (p : Ar S i a) (m : Horiz a b) (n : Horiz b c) :
    postHorizontal S (postHorizontal S p m) n = postHorizontal S p (m ≫ n) := by
  induction p using Quot.ind with
  | _ p => exact congrArg (mk S) (postH_comp p m n)

theorem postV_paste (p : Ar S i a) (u : a ⟶ b) (v : b ⟶ c) :
    postVertical S K (postVertical S K p u) v = postVertical S K p (u ≫ v) := by
  induction p using Quot.ind with
  | _ p =>
    let f := K.fill p.m u
    let g := K.fill f.corner.m v
    change postVertical S K (postVertical S K (mk S p) u) v = postVertical S K (mk S p) (u ≫ v)
    rw [postVertical_mk S K p f.face,postVertical_mk S K ⟨f.corner.mid,p.e ≫ f.corner.e,f.corner.m⟩ g.face,
      postVertical_mk S K p (S.vp f.face g.face)]
    simp [Category.assoc]

theorem post_square (p : Ar S i a) {m : Horiz a b} {e : a ⟶ j} {v : b ⟶ c} {n : Horiz j c}
    (h : S.Sq m e v n) :
    postVertical S K (postHorizontal S p m) v = postHorizontal S (postVertical S K p e) n := by
  induction p using Quot.ind with
  | _ p =>
    let f := K.fill p.m e
    change postVertical S K (mk S (postH p m)) v = postHorizontal S (postVertical S K (mk S p) e) n
    rw [postVertical_mk S K p f.face,postVertical_mk S K (postH p m) (S.hp f.face h)]
    rfl

def compose (x : Ar S a b) (y : Ar S b c) : Ar S a c := by
  refine Quot.lift (fun q => postHorizontal S (postVertical S K x q.e) q.m) ?_ y
  rintro q r ⟨t⟩
  rw [← t.left_eq, ← postV_paste]
  exact (postV_id S K _).symm.trans (post_square S K _ t.face)

theorem comp_mk (x : Ar S a b) (q : Corner b c) :
    compose S K x (mk S q) = postHorizontal S (postVertical S K x q.e) q.m := rfl

theorem comp_assoc (x : Ar S a b) (y : Ar S b c) (z : Ar S c d) :
    compose S K (compose S K x y) z = compose S K x (compose S K y z) := by
  induction y using Quot.ind with
  | _ q =>
    induction z using Quot.ind with
    | _ r =>
      let f := K.fill q.m r.e
      change compose S K (compose S K x (mk S q)) (mk S r) = compose S K x (compose S K (mk S q) (mk S r))
      rw [comp_mk,comp_mk,comp_mk,postVertical_mk S K q f.face,post_square S K _ f.face,postV_paste,postH_paste]
      rfl

theorem id_comp (x : Ar S a b) : compose S K (mk S (vert (𝟙 a))) x = x := by
  induction x using Quot.ind with
  | _ p =>
    change compose S K _ (mk S p) = _
    rw [comp_mk,postVertical_mk S K _ (S.idH p.e)]
    change mk S ⟨_,𝟙 _ ≫ p.e,𝟙 _ ≫ p.m⟩ = _
    simp [mk]

theorem comp_id (x : Ar S a b) : compose S K x (mk S (vert (𝟙 b))) = x := by
  change postHorizontal S (postVertical S K x (𝟙 b)) (𝟙 _) = x
  rw [postV_id,postH_id]

structure Cnr (K : Filled S) where
  obj : O

instance : Category (Cnr S K) where
  Hom x y := Ar S x.obj y.obj
  id a := mk S (vert (𝟙 a.obj))
  comp := compose S K
  id_comp := id_comp S K
  comp_id := comp_id S K
  assoc := comp_assoc S K

def Step.identity (p : Corner a b) : Step S p p :=
  ⟨𝟙 _,Category.comp_id _,S.idV _⟩

def Step.trans {p q r : Corner a b} (t : Step S p q) (f : Step S q r) : Step S p r :=
  ⟨t.mid ≫ f.mid, by rw [← Category.assoc,t.left_eq,f.left_eq], by simpa using S.vp t.face f.face⟩

/-- Factoring the identity square through a square over the right identity
reverses its midpoint and gives the left inverse equation. -/
def reverseFace {m : Horiz i b} {θ : i ⟶ j} {n : Horiz j b} (t : S.Sq m θ (𝟙 b) n) :
    Step S (⟨j,θ,n⟩ : Corner i b) ⟨i,𝟙 _,m⟩ :=
  fillerStep S K ⟨_,t⟩ ⟨_,S.idV m⟩

def Step.symm {p q : Corner a b} (t : Step S p q) : Step S q p := by
  let r := reverseFace S K t.face
  refine ⟨r.mid, ?_, r.face⟩
  change q.e ≫ r.mid = p.e
  rw [← t.left_eq,Category.assoc,show t.mid ≫ r.mid = 𝟙 _ from r.left_eq,Category.comp_id]

def Step.midIso {p q : Corner a b} (t : Step S p q) : p.mid ≅ q.mid := by
  let s := reverseFace S K t.face
  let r := reverseFace S K s.face
  have e : t.mid ≫ s.mid = 𝟙 _ := s.left_eq
  have f : s.mid ≫ r.mid = 𝟙 _ := r.left_eq
  have inverse_law {x y : O} (a : x ⟶ y) (b : y ⟶ x) (c : x ⟶ y)
      (ab : a ≫ b = 𝟙 x) (bc : b ≫ c = 𝟙 y) : b ≫ a = 𝟙 y := by
    have ac : a = c := by rw [← Category.id_comp c, ← ab, Category.assoc,bc,Category.comp_id]
    rw [ac,bc]
  exact ⟨t.mid,s.mid,e,inverse_law _ _ _ e f⟩

def stepSetoid : Setoid (Corner a b) where
  r p q := Nonempty (Step S p q)
  iseqv := ⟨fun p => ⟨Step.identity S p⟩,fun ⟨h⟩ => ⟨h.symm S K⟩,fun ⟨h⟩ ⟨g⟩ => ⟨h.trans S g⟩⟩

include K in
theorem eq_iff_step (p q : Corner a b) : mk S p = mk S q ↔ Nonempty (Step S p q) :=
  ⟨fun h => Quotient.exact (s := stepSetoid S K) h,fun h => Quot.sound (r := fun c d => Nonempty (Step S c d)) h⟩

theorem comp_from_legs (e : a ⟶ j) (m : Horiz j b) :
    compose S K (mk S (vert e)) (mk S (horiz m)) = mk S ⟨j,e,m⟩ := by
  change postHorizontal S (postVertical S K (mk S (vert e)) (𝟙 j)) m = _
  rw [postV_id]
  change mk S ⟨j,e,𝟙 _ ≫ m⟩ = _
  rw [Category.id_comp]

theorem comp_to_legs {m : Horiz a b} {e : a ⟶ j} {v : b ⟶ c} {n : Horiz j c} (h : S.Sq m e v n) :
    compose S K (mk S (horiz m)) (mk S (vert v)) = mk S ⟨j,e,n⟩ := by
  change postHorizontal S (postVertical S K (mk S (horiz m)) v) (𝟙 _) = _
  rw [postH_id,postVertical_mk S K (horiz m) h]
  simp [horiz]

theorem square_iff {m : Horiz a b} {e : a ⟶ j} {v : b ⟶ c} {n : Horiz j c} :
    Nonempty (S.Sq m e v n) ↔
    compose S K (mk S (horiz m)) (mk S (vert v)) = compose S K (mk S (vert e)) (mk S (horiz n)) := by
  rw [comp_from_legs]
  constructor
  · rintro ⟨t⟩; exact comp_to_legs S K t
  · intro eq
    let f := K.fill m v
    have h := (comp_to_legs S K f.face).symm.trans eq
    obtain ⟨s⟩ := (eq_iff_step S K f.corner ⟨j,e,n⟩).mp h
    have face := S.vp f.face s.face
    have hl : f.corner.e ≫ s.mid = e := s.left_eq
    simpa [hl] using (show Nonempty (S.Sq m (f.corner.e ≫ s.mid) (v ≫ 𝟙 c) n) from ⟨face⟩)

end ContextualComposition.OrthogonalCornerCategory
