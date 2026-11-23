module

public import ContextualComposition.FactorizationDoubleEnvelope

/-! Intrinsic codomain-discrete recognition. Vertical and horizontal
categories have the same objects. A unique filler for each top-right corner
determines composition of bottom-left corners and recovers the squares. -/

@[expose] public section
namespace ContextualComposition.StrictCornerRecognition
open CategoryTheory

universe u v w s

/-- A separate copy of the objects for the horizontal category structure. -/
structure HObj (O : Type u) where
  obj : O

variable {O : Type u} [Category.{v} O] [Category.{w} (HObj O)]

abbrev Horiz (a b : O) := (⟨a⟩ : HObj O) ⟶ (⟨b⟩ : HObj O)

structure Corner (a b : O) where
  mid : O
  e : a ⟶ mid
  m : Horiz mid b

/-- Only the two identity and pasting operations are needed as input.
Unique filling forces uniqueness of every parallel pair of squares. -/
structure Faces (O : Type u) [Category.{v} O] [Category.{w} (HObj O)] where
  Sq : ∀ {a b c d : O}, Horiz a b → (a ⟶ c) → (b ⟶ d) → Horiz c d → Type s
  idV : ∀ {a b} (m : Horiz a b), Sq m (𝟙 a) (𝟙 b) m
  idH : ∀ {a b} (e : a ⟶ b), Sq (𝟙 _) e e (𝟙 _)
  hp : ∀ {a b c d e f : O} {m : Horiz a b} {n : Horiz b c}
    {u : a ⟶ d} {v : b ⟶ e} {w : c ⟶ f} {m' : Horiz d e} {n' : Horiz e f},
    Sq m u v m' → Sq n v w n' → Sq (m ≫ n) u w (m' ≫ n')
  vp : ∀ {a b c d e f : O} {m : Horiz a b} {n : Horiz c d} {h : Horiz e f}
    {u : a ⟶ c} {v : b ⟶ d} {u' : c ⟶ e} {v' : d ⟶ f},
    Sq m u v n → Sq n u' v' h → Sq m (u ≫ u') (v ≫ v') h

variable (S : Faces O) {a b c d i j k : O}

structure Filler (m : Horiz a b) (v : b ⟶ c) where
  corner : Corner a c
  face : S.Sq m corner.e v corner.m

abbrev CodomainDiscrete := ∀ {a b c : O} (m : Horiz a b) (v : b ⟶ c), Unique (Filler S m v)

variable (U : CodomainDiscrete S)

def postH (p : Corner i a) (m : Horiz a b) : Corner i b := ⟨p.mid,p.e,p.m ≫ m⟩

def postV (p : Corner i a) (v : a ⟶ b) : Corner i b :=
  let q := (U p.m v).default.corner
  ⟨q.mid,p.e ≫ q.e,q.m⟩

theorem fill_eq {m : Horiz a b} {v : b ⟶ c} {j : O} {e : a ⟶ j} {n : Horiz j c}
    (h : S.Sq m e v n) :
    (U m v).default.corner = ⟨j,e,n⟩ :=
  congrArg Filler.corner ((U m v).uniq ⟨⟨j,e,n⟩,h⟩).symm

theorem postV_mk (x : i ⟶ a) {m : Horiz a b} {v : b ⟶ c} {e : a ⟶ j} {n : Horiz j c}
    (h : S.Sq m e v n) :
    postV S U ⟨a,x,m⟩ v = ⟨j,x ≫ e,n⟩ := by
  change (fun (q : Corner a c) => Corner.mk q.mid (x ≫ q.e) q.m) (U m v).default.corner = _
  rw [fill_eq S U h]

theorem post_square (p : Corner i a) {m : Horiz a b} {v : b ⟶ c} {e : a ⟶ j} {n : Horiz j c}
    (h : S.Sq m e v n) : postV S U (postH p m) v = postH (postV S U p e) n := by
  obtain ⟨x,y,z⟩ := p
  let f := (U z e).default
  exact postV_mk S U y (S.hp f.face h)

theorem postV_comp (p : Corner i a) (u : a ⟶ b) (v : b ⟶ c) :
    postV S U (postV S U p u) v = postV S U p (u ≫ v) := by
  obtain ⟨x,y,z⟩ := p
  let f := (U z u).default
  let g := (U f.corner.m v).default
  rw [postV_mk S U y (S.vp f.face g.face)]
  change Corner.mk _ ((y ≫ f.corner.e) ≫ g.corner.e) g.corner.m = _
  rw [Category.assoc]

theorem postH_comp (p : Corner i a) (m : Horiz a b) (n : Horiz b c) :
    postH (postH p m) n = postH p (m ≫ n) := by simp [postH, Category.assoc]

def compose (p : Corner a b) (q : Corner b c) : Corner a c := postH (postV S U p q.e) q.m

theorem compose_assoc (p : Corner a b) (q : Corner b c) (r : Corner c d) :
    compose S U (compose S U p q) r = compose S U p (compose S U q r) := by
  let f := (U q.m r.e).default
  change postH (postV S U (postH (postV S U p q.e) q.m) r.e) r.m = _
  rw [post_square S U _ f.face, postV_comp, postH_comp]
  rfl

def vert (u : a ⟶ b) : Corner a b := ⟨b,u,𝟙 _⟩
def horiz (m : Horiz a b) : Corner a b := ⟨a,𝟙 _,m⟩

theorem compose_from_legs (e : a ⟶ j) (m : Horiz j b) : compose S U (vert e) (horiz m) = ⟨j,e,m⟩ := by
  change postH (postV S U ⟨j,e,𝟙 _⟩ (𝟙 j)) m = _
  rw [postV_mk S U e (S.idH (𝟙 j))]
  simp [postH]

theorem compose_to_legs {m : Horiz a b} {v : b ⟶ c} {e : a ⟶ j} {n : Horiz j c} (h : S.Sq m e v n) :
    compose S U (horiz m) (vert v) = ⟨j,e,n⟩ := by
  change postH (postV S U ⟨a,𝟙 _,m⟩ v) (𝟙 _) = _
  rw [postV_mk S U (𝟙 a) h]
  simp [postH]

theorem compose_id (p : Corner a b) : compose S U p (vert (𝟙 b)) = p := by
  obtain ⟨j,e,m⟩ := p
  change postH (postV S U ⟨j,e,m⟩ (𝟙 b)) (𝟙 _) = _
  rw [postV_mk S U e (S.idV m)]
  simp [postH]

theorem id_compose (p : Corner a b) : compose S U (vert (𝟙 a)) p = p := by
  obtain ⟨j,e,m⟩ := p
  change postH (postV S U ⟨a,𝟙 _,𝟙 _⟩ e) m = _
  rw [postV_mk S U (𝟙 a) (S.idH e)]
  simp [postH]

structure Cnr (U : CodomainDiscrete S) where
  obj : O

instance : Category (Cnr S U) where
  Hom a b := Corner a.obj b.obj
  id a := vert (𝟙 a.obj)
  comp := compose S U
  id_comp := id_compose S U
  comp_id := compose_id S U
  assoc := compose_assoc S U

theorem vert_comp (e : a ⟶ b) (v : b ⟶ c) : compose S U (vert e) (vert v) = vert (e ≫ v) := by
  change postH (postV S U ⟨b,e,𝟙 _⟩ v) (𝟙 _) = _
  rw [postV_mk S U e (S.idH v)]
  simp [postH,vert]

theorem horiz_comp (m : Horiz a b) (n : Horiz b c) : compose S U (horiz m) (horiz n) = horiz (m ≫ n) := by
  change postH (postV S U ⟨a,𝟙 _,m⟩ (𝟙 b)) n = _
  rw [postV_mk S U (𝟙 a) (S.idV m)]
  simp [postH,horiz]

/-- Decode an actual commuting boundary back into a square of the original
structure, by transporting the chosen filler on equality of whole corners. -/
def recoverFace {m : Horiz a b} {v : b ⟶ c} {e : a ⟶ j} {n : Horiz j c}
    (h : compose S U (horiz m) (vert v) = compose S U (vert e) (horiz n)) : S.Sq m e v n := by
  let f := (U m v).default
  have eq : f.corner = ⟨j,e,n⟩ := by
    exact ((compose_to_legs S U f.face).symm.trans h).trans (compose_from_legs S U e n)
  exact Eq.mp (congrArg (fun q : Corner a c => S.Sq m q.e v q.m) eq) f.face

include U in
theorem square_subsingleton {m : Horiz a b} {v : b ⟶ c} {e : a ⟶ j} {n : Horiz j c} :
    Subsingleton (S.Sq m e v n) := by
  constructor
  intro h k
  have h₁ := (U m v).uniq ⟨⟨j,e,n⟩,h⟩
  have h₂ := (U m v).uniq ⟨⟨j,e,n⟩,k⟩
  exact eq_of_heq (Filler.mk.inj (h₁.trans h₂.symm)).2

def squareEquiv {m : Horiz a b} {v : b ⟶ c} {e : a ⟶ j} {n : Horiz j c} :
    S.Sq m e v n ≃ (compose S U (horiz m) (vert v) = compose S U (vert e) (horiz n)) where
  toFun h := (compose_to_legs S U h).trans (compose_from_legs S U e n).symm
  invFun := recoverFace S U
  left_inv _ := (square_subsingleton S U).allEq _ _
  right_inv _ := rfl

def verticalClass : MorphismProperty (Cnr S U) := fun x y p => ∃ e : x.obj ⟶ y.obj, vert e = p
def horizontalClass : MorphismProperty (Cnr S U) := fun x y p => ∃ m : Horiz x.obj y.obj, horiz m = p

instance : (verticalClass S U).IsMultiplicative where
  id_mem x := ⟨𝟙 x.obj,rfl⟩
  comp_mem f g := by
    rintro ⟨e,rfl⟩ ⟨e',rfl⟩
    exact ⟨e ≫ e',(vert_comp S U e e').symm⟩

instance : (horizontalClass S U).IsMultiplicative where
  id_mem x := ⟨𝟙 _,rfl⟩
  comp_mem f g := by
    rintro ⟨m,rfl⟩ ⟨m',rfl⟩
    exact ⟨m ≫ m',(horiz_comp S U m m').symm⟩

def factor {x y : Cnr S U} (p : x ⟶ y) :
    MorphismProperty.MapFactorizationData (verticalClass S U) (horizontalClass S U) p where
  Z := ⟨p.mid⟩
  i := vert p.e
  p := horiz p.m
  fac := compose_from_legs S U p.e p.m
  hi := ⟨p.e,rfl⟩
  hp := ⟨p.m,rfl⟩

/-- Strict factorization is a conclusion of intrinsic unique top-right
filling. The midpoint as well as both legs are recovered. -/
@[instance_reducible] def strictFactorization {x y : Cnr S U} (p : x ⟶ y) :
    Unique (MorphismProperty.MapFactorizationData (verticalClass S U) (horizontalClass S U) p) where
  default := factor S U p
  uniq d := by
    obtain ⟨⟨z⟩,i,m,fac,⟨e,rfl⟩,⟨n,rfl⟩⟩ := d
    change compose S U (vert e) (horiz n) = p at fac
    rw [compose_from_legs] at fac
    cases fac
    rfl

theorem vert_injective {X Y : O} : Function.Injective (vert : (X ⟶ Y) → Corner X Y) := by
  intro f g e
  exact eq_of_heq (Corner.mk.inj e).2.1

theorem horiz_injective {X Y : O} : Function.Injective (horiz : Horiz X Y → Corner X Y) := by
  intro f g e
  exact eq_of_heq (Corner.mk.inj e).2.2

/-- Both marked subcategories recover the original arrow sets without any
loss from passing to their images in the reconstructed category. -/
noncomputable def verticalEquiv (x y : Cnr S U) :
    (x.obj ⟶ y.obj) ≃ {p : x ⟶ y // verticalClass S U p} :=
  Equiv.ofBijective (fun e => ⟨vert e,e,rfl⟩)
    ⟨fun _ _ h => vert_injective (congrArg Subtype.val h), fun ⟨_,e,rfl⟩ => ⟨e,rfl⟩⟩

noncomputable def horizontalEquiv (x y : Cnr S U) :
    Horiz x.obj y.obj ≃ {p : x ⟶ y // horizontalClass S U p} :=
  Equiv.ofBijective (fun m => ⟨horiz m,m,rfl⟩)
    ⟨fun _ _ h => horiz_injective (congrArg Subtype.val h), fun ⟨_,m,rfl⟩ => ⟨m,rfl⟩⟩

end ContextualComposition.StrictCornerRecognition
