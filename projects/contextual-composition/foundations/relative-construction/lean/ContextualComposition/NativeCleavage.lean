module
public import ContextualComposition.SpanPayload
/-! Chosen restrictions for positive span products. The primitive construction is
native right append: pull the last grade along the destination of the recursively
chosen prefix arrow. Factorization proves functoriality on fibre arrows. Only
after this construction do we compare with the independent iterate. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeCleavage
open CategoryTheory Opposite
universe b w k j l i u v
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K] {L : Type l} [Category.{i} L]

/-- Universal factorization with the actual mapped endpoints as coordinates. -/
def Cartesian (p : K ⥤ B) {x y : K} (f : x ⟶ y) : Prop :=
  ∀ (z : K) (g : z ⟶ y) (a : p.obj z ⟶ p.obj x), p.map g = a ≫ p.map f →
    ∃! h : z ⟶ x, p.map h = a ∧ h ≫ f = g

theorem composite {p : K ⥤ L} {q : L ⥤ B} {x y : K} {f : x ⟶ y}
    (hp : Cartesian p f) (hq : Cartesian q (p.map f)) : Cartesian (p ⋙ q) f := by
  intro z g a e
  obtain ⟨k,⟨hk,hg⟩,uk⟩ := hq _ (p.map g) a e
  obtain ⟨h,⟨hh,he⟩,uh⟩ := hp z g k hg.symm
  exact ⟨h,⟨by change q.map (p.map h) = a; rw [hh,hk],he⟩,fun t ht =>
    uh t ⟨uk (p.map t) ⟨ht.1,by rw [← p.map_comp,ht.2]⟩,ht.2⟩⟩

theorem identityBase {x y : B} (f : x ⟶ y) : Cartesian (𝟭 B) f := by
  intro z g a e
  exact ⟨a,⟨rfl,e.symm⟩,fun _ h => h.1⟩

theorem strong {p : K ⥤ B} {x y : K} {f : x ⟶ y} (h : Cartesian p f) :
    p.IsStronglyCartesian (p.map f) f where
  universal_property' {z} a g hg := by
    have ew := IsHomLift.eq_of_isHomLift p (a ≫ p.map f) g
    obtain ⟨k,⟨hk,he⟩,uk⟩ := h z g a ew.symm
    exact ⟨k,⟨hk ▸ (IsHomLift.map p k),he⟩,fun t ht => by
      let : p.IsHomLift a t := ht.1
      exact uk t ⟨(IsHomLift.eq_of_isHomLift p a t).symm,ht.2⟩⟩

variable (Y : Bᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ B)
def pullObj (y : Total Y e) {k : K} (a : k ⟶ grade _ _ y) : Total Y e :=
  pair _ _ k ((Y.map (e.map a).op).toFunctor.obj (payload _ _ y))
def pullLift (y : Total Y e) {k : K} (a : k ⟶ grade _ _ y) : pullObj Y e y a ⟶ y := arrow a (𝟙 _)

private theorem total_ext {x y : Total Y e} {f g : x ⟶ y} (a : gradeMap f = gradeMap g)
    (b : HEq (payloadMap f) (payloadMap g)) : f = g := (homEquiv _ _).injective (Sigma.ext a b)

private theorem strip {C : Type*} [Category* C] {a b c : C} (f : a ⟶ b) (h : b = c) :
    HEq (f ≫ eqToHom h) f := by subst c; simp

set_option backward.isDefEq.respectTransparency false in
theorem payload_post (y : Total Y e) {k : K} (a : k ⟶ grade _ _ y) {z : Total Y e} (g : z ⟶ pullObj Y e y a) :
    HEq (payloadMap (g ≫ pullLift Y e y a)) (payloadMap g) := by
  rw [payload_comp]
  change HEq (_ ≫ (Y.map _).toFunctor.map (𝟙 _) ≫ _) _
  rw [Functor.map_id,Category.id_comp]
  exact strip _ _

/-- A pull with identity final component is cartesian even for noninvertible base arrows. -/
theorem cartesianLift (y : Total Y e) {k : K} (a : k ⟶ grade _ _ y) :
    Cartesian gradeProjection (pullLift Y e y a) := by
  intro z g b hb
  change gradeMap g = b ≫ a at hb
  let t : z ⟶ pullObj Y e y a := arrow b (payloadMap g ≫ eqToHom
    (show (Y.map (e.map (gradeMap g)).op).toFunctor.obj (payload _ _ y) =
      (Y.map (e.map b).op).toFunctor.obj ((Y.map (e.map a).op).toFunctor.obj (payload _ _ y)) by
        rw [hb]; exact (comp_target b a _).symm))
  have ht : HEq (payloadMap t) (payloadMap g) := strip _ _
  refine ⟨t,⟨rfl,total_ext Y e hb.symm ((payload_post Y e y a t).trans ht)⟩,?_⟩
  intro l hl
  apply total_ext Y e (f := l) (g := t) hl.1
  exact ((payload_post Y e y a l).symm.trans (by rw [hl.2])).trans ht.symm

/-- A specified object and lift, not merely existence of a cartesian arrow. -/
structure Choice (p : K ⥤ B) (A : B) (y : K) (a : A ⟶ p.obj y) where
  obj : K
  source : p.obj obj = A
  lift : obj ⟶ y
  over : p.map lift = eqToHom source ≫ a
  cart : Cartesian p lift

abbrev Cleavage (p : K ⥤ B) := ∀ (A : B) (y : K) (a : A ⟶ p.obj y), Choice p A y a

def baseChoice : Cleavage (𝟭 B) := fun A _ a => ⟨A,rfl,a,(Category.id_comp a).symm,identityBase a⟩

/-- Append one presheaf; the same step also attaches the terminal payload. -/
def extendChoice (p : K ⥤ B) (C : Cleavage p) :
    Cleavage (gradeProjection (Y := Y) (e := e) ⋙ p) := fun A y a =>
  let L := C A (grade _ _ y) a
  ⟨pullObj Y e y L.lift,L.source,pullLift Y e y L.lift,L.over,
    composite (cartesianLift Y e y L.lift) L.cart⟩

open SpanApex
variable {P : Endpoints.{b,w,k,j} B} (S : P.Split)
def powerChoice : (n : Nat) → Cleavage (positivePowers P S n).source
  | 0 => extendChoice P.grades (𝟭 B) (𝟭 B) baseChoice
  | n+1 => extendChoice P.grades (positivePowers P S n).dest (positivePowers P S n).source (powerChoice n)

def payloadChoice (n : Nat) : Cleavage (gradeProjection (Y := Y) (e := (positivePowers P S n).dest) ⋙ (positivePowers P S n).source) :=
  extendChoice Y _ _ (powerChoice S n)

theorem chosenStrong {p : K ⥤ B} {A : B} {y : K} {a : A ⟶ p.obj y} (c : Choice p A y a) :
    p.IsStronglyCartesian a c.lift := by
  obtain ⟨z,h,k,e,cart⟩ := c
  cases h
  simp only [eqToHom_refl,Category.id_comp] at e
  subst a
  exact strong cart

namespace Reindex
variable {p : K ⥤ B} (C : Cleavage p) {A D : B} (a : A ⟶ D)
def selected (y : p.Fiber D) := C A y.val (a ≫ eqToHom y.property.symm)
def object (y : p.Fiber D) : p.Fiber A := ⟨(selected C a y).obj,(selected C a y).source⟩
def lift (y : p.Fiber D) : (object C a y).val ⟶ y.val := (selected C a y).lift
theorem lift_over (y : p.Fiber D) : p.map (lift C a y) =
    eqToHom (object C a y).property ≫ a ≫ eqToHom y.property.symm := (selected C a y).over

theorem vertical_map {X Z : p.Fiber A} (f : X ⟶ Z) :
    p.map f.val = eqToHom X.property ≫ eqToHom Z.property.symm := by
  let : p.IsHomLift (𝟙 A) f.val := f.property
  simpa only [Category.id_comp] using IsHomLift.fac' p (𝟙 A) f.val

def verticalMk {X Z : p.Fiber A} (f : X.val ⟶ Z.val)
    (h : p.map f = eqToHom X.property ≫ eqToHom Z.property.symm) : X ⟶ Z :=
  ⟨f,IsHomLift.of_fac' p _ _ X.property Z.property (by simpa only [Category.id_comp] using h)⟩

set_option backward.isDefEq.respectTransparency false in
theorem factor {x : p.Fiber A} (z : p.Fiber D) (f : x.val ⟶ z.val)
    (h : p.map f = eqToHom x.property ≫ a ≫ eqToHom z.property.symm) :
    ∃! t : x ⟶ object C a z, t.val ≫ lift C a z = f := by
  obtain ⟨k,⟨hk,he⟩,uk⟩ := (selected C a z).cart x.val f
    (eqToHom x.property ≫ eqToHom (object C a z).property.symm) (by
      change p.map f = _ ≫ p.map (lift C a z)
      rw [lift_over,h]; simp)
  exact ⟨verticalMk k hk,he,fun t ht => Subtype.ext (uk t.val ⟨vertical_map t,ht⟩)⟩

theorem cancel {x : p.Fiber A} {z : p.Fiber D} (f g : x ⟶ object C a z)
    (h : f.val ≫ lift C a z = g.val ≫ lift C a z) : f = g := by
  have w : p.map (g.val ≫ lift C a z) = eqToHom x.property ≫ a ≫ eqToHom z.property.symm := by
    rw [p.map_comp,vertical_map g,lift_over]; simp
  obtain ⟨_,_,uniq⟩ := factor C a z _ w
  exact (uniq f h).trans (uniq g rfl).symm

theorem map_over {y z : p.Fiber D} (f : y ⟶ z) : p.map (lift C a y ≫ f.val) =
    eqToHom (object C a y).property ≫ a ≫ eqToHom z.property.symm := by
  rw [p.map_comp,lift_over,vertical_map f]; simp

noncomputable def map {y z : p.Fiber D} (f : y ⟶ z) : object C a y ⟶ object C a z :=
  (factor C a z _ (map_over C a f)).choose
theorem map_fac {y z : p.Fiber D} (f : y ⟶ z) :
    (map C a f).val ≫ lift C a z = lift C a y ≫ f.val := (factor C a z _ (map_over C a f)).choose_spec.1

noncomputable def functor : p.Fiber D ⥤ p.Fiber A where
  obj := object C a
  map := map C a
  map_id y := by apply cancel C a; rw [map_fac]; change _ ≫ 𝟙 _ = 𝟙 _ ≫ _; simp
  map_comp {x y z} f g := by
    apply cancel C a
    rw [map_fac]
    change lift C a x ≫ f.val ≫ g.val = ((map C a f).val ≫ (map C a g).val) ≫ lift C a z
    rw [Category.assoc,map_fac,← Category.assoc (map C a f).val,map_fac,Category.assoc]
end Reindex

theorem pasteCart {p : K ⥤ B} {x y z : K} {f : x ⟶ y} {g : y ⟶ z}
    (hf : Cartesian p f) (hg : Cartesian p g) : Cartesian p (f ≫ g) := by
  intro w k a h
  rw [p.map_comp,← Category.assoc] at h
  obtain ⟨j,⟨hj,ej⟩,uj⟩ := hg w k _ h
  obtain ⟨t,⟨ht,et⟩,ut⟩ := hf w j a hj
  refine ⟨t,⟨ht,by rw [← Category.assoc,et,ej]⟩,?_⟩
  intro l hl
  apply ut l
  exact ⟨hl.1,uj _ ⟨by rw [p.map_comp,hl.1],by rw [Category.assoc,hl.2]⟩⟩

structure Route (p : K ⥤ B) {A D : B} (a : A ⟶ D) where
  act : p.Fiber D ⥤ p.Fiber A
  lift (y : p.Fiber D) : (act.obj y).val ⟶ y.val
  over (y : p.Fiber D) : p.map (lift y) = eqToHom (act.obj y).property ≫ a ≫ eqToHom y.property.symm
  cart (y : p.Fiber D) : Cartesian p (lift y)
  natural {x y : p.Fiber D} (f : x ⟶ y) : (act.map f).val ≫ lift y = lift x ≫ f.val

/- Different choices or bracketings over the same base map are compared by the unique vertical maps preserving the lifts. -/
namespace Route
variable {p : K ⥤ B} {A D E : B} {a : A ⟶ D}
noncomputable def ofChoice (C : Cleavage p) (a : A ⟶ D) : Route p a :=
  ⟨Reindex.functor C a,Reindex.lift C a,Reindex.lift_over C a,fun y => (Reindex.selected C a y).cart,Reindex.map_fac C a⟩

theorem cartId (p : K ⥤ B) (y : K) : Cartesian p (𝟙 y) := by
  intro z g a h
  rw [p.map_id,Category.comp_id] at h
  exact ⟨g,⟨h,Category.comp_id _⟩,fun l hl => (Category.comp_id l).symm.trans hl.2⟩

set_option backward.isDefEq.respectTransparency false in
def id (A : B) : Route p (𝟙 A) where
  act := 𝟭 _
  lift y := 𝟙 y.val
  over y := by simp
  cart y := cartId p y.val
  natural f := by simp

def comp {b : D ⟶ E} (R : Route p a) (Q : Route p b) : Route p (a ≫ b) where
  act := Q.act ⋙ R.act
  lift y := R.lift (Q.act.obj y) ≫ Q.lift y
  over y := by rw [p.map_comp,R.over,Q.over]; simp
  cart y := pasteCart (R.cart _) (Q.cart y)
  natural {x y} f := by
    change (R.act.map (Q.act.map f)).val ≫ R.lift _ ≫ Q.lift _ = (R.lift _ ≫ Q.lift _) ≫ f.val
    rw [← Category.assoc,R.natural,Category.assoc,Q.natural,Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem unique (R : Route p a) {x : p.Fiber A} (y : p.Fiber D) (f : x.val ⟶ y.val)
    (h : p.map f = eqToHom x.property ≫ a ≫ eqToHom y.property.symm) :
    ∃! t : x ⟶ R.act.obj y, t.val ≫ R.lift y = f := by
  obtain ⟨k,⟨hk,he⟩,uk⟩ := R.cart y x.val f (eqToHom x.property ≫ eqToHom (R.act.obj y).property.symm)
    (by rw [R.over,h]; simp)
  exact ⟨Reindex.verticalMk k hk,he,fun t ht => Subtype.ext (uk t.val ⟨Reindex.vertical_map t,ht⟩)⟩

theorem cancel (R : Route p a) {x : p.Fiber A} {y : p.Fiber D} {f g : x ⟶ R.act.obj y}
    (h : f.val ≫ R.lift y = g.val ≫ R.lift y) : f = g := by
  obtain ⟨_,_,uniq⟩ := R.unique y (g.val ≫ R.lift y)
    (by rw [p.map_comp,Reindex.vertical_map g,R.over]; simp)
  exact (uniq f h).trans (uniq g rfl).symm

noncomputable def compareApp (R Q : Route p a) (x : p.Fiber D) : R.act.obj x ⟶ Q.act.obj x :=
  (Q.unique x (R.lift x) (R.over x)).choose
theorem compare_fac (R Q : Route p a) (x : p.Fiber D) :
    (compareApp R Q x).val ≫ Q.lift x = R.lift x := (Q.unique x (R.lift x) (R.over x)).choose_spec.1

noncomputable def compare (R Q : Route p a) : R.act ⟶ Q.act where
  app := compareApp R Q
  naturality {x y} f := by
    apply Q.cancel
    change ((R.act.map f).val ≫ (compareApp R Q y).val) ≫ _ = ((compareApp R Q x).val ≫ (Q.act.map f).val) ≫ _
    rw [Category.assoc,Category.assoc,compare_fac,R.natural,Q.natural,← Category.assoc,compare_fac]

theorem compare_id (R : Route p a) : compare R R = 𝟙 _ := by
  ext x : 2
  apply R.cancel
  change (compareApp R R x).val ≫ R.lift x = 𝟙 _ ≫ R.lift x
  rw [compare_fac,Category.id_comp]

theorem compare_comp (R Q T : Route p a) : compare R Q ≫ compare Q T = compare R T := by
  ext x : 2
  apply T.cancel
  change ((compareApp R Q x).val ≫ (compareApp Q T x).val) ≫ T.lift x = (compareApp R T x).val ≫ T.lift x
  rw [Category.assoc,compare_fac,compare_fac,compare_fac]

noncomputable def iso (R Q : Route p a) : R.act ≅ Q.act :=
  ⟨compare R Q,compare Q R,(compare_comp ..).trans (compare_id _),(compare_comp ..).trans (compare_id _)⟩
open CategoryTheory.Functor
/-- Changing only the displayed base arrow leaves the actual functor and lifts unchanged. -/
def rebase {b : A ⟶ D} (h : a = b) (R : Route p a) : Route p b where
  act := R.act
  lift := R.lift
  over y := h ▸ R.over y
  cart := R.cart
  natural := R.natural

noncomputable def unitIso (C : Cleavage p) (A : B) : Reindex.functor C (𝟙 A) ≅ 𝟭 _ :=
  iso (ofChoice C (𝟙 A)) (id A)
noncomputable def compIso (C : Cleavage p) (a : A ⟶ D) (b : D ⟶ E) :
    Reindex.functor C (a ≫ b) ≅ Reindex.functor C b ⋙ Reindex.functor C a :=
  iso (ofChoice C (a ≫ b)) (comp (ofChoice C a) (ofChoice C b))

theorem compare_horizontal {b : D ⟶ E} (R R' : Route p a) (Q Q' : Route p b) :
    whiskerRight (compare Q Q') R.act ≫ whiskerLeft Q'.act (compare R R') =
      compare (comp R Q) (comp R' Q') := by
  ext x : 2
  apply (comp R' Q').cancel
  change ((R.act.map (compareApp Q Q' x)).val ≫ (compareApp R R' (Q'.act.obj x)).val) ≫
      R'.lift _ ≫ Q'.lift x = (compareApp (comp R Q) (comp R' Q') x).val ≫ (comp R' Q').lift x
  rw [Category.assoc,← Category.assoc (compareApp R R' _).val,compare_fac,← Category.assoc,
    R.natural,Category.assoc,compare_fac,compare_fac]
  rfl

theorem compare_unique (R Q : Route p a) (t : R.act ⟶ Q.act)
    (fac : ∀ x, (t.app x).val ≫ Q.lift x = R.lift x) : t = compare R Q := by
  ext x : 2
  apply Q.cancel
  exact (fac x).trans (compare_fac R Q x).symm

theorem associator_fac {H : B} {b : D ⟶ E} {c : E ⟶ H} (R : Route p a) (Q : Route p b) (T : Route p c) :
    compare (rebase (Category.assoc a b c) (comp (comp R Q) T)) (comp R (comp Q T)) =
      (CategoryTheory.Functor.associator T.act Q.act R.act).inv := by
  symm
  refine compare_unique (rebase (Category.assoc a b c) (comp (comp R Q) T)) (comp R (comp Q T)) _ ?_
  intro x
  change 𝟙 _ ≫ R.lift _ ≫ (Q.lift _ ≫ T.lift x) = (R.lift _ ≫ Q.lift _) ≫ T.lift x
  rw [Category.id_comp,Category.assoc]

theorem left_unit_fac (R : Route p a) :
    compare (rebase (Category.id_comp a) (comp (id A) R)) R = (CategoryTheory.Functor.rightUnitor R.act).hom := by
  symm; refine compare_unique (rebase (Category.id_comp a) (comp (id A) R)) R _ ?_; intro x; rfl

theorem right_unit_fac (R : Route p a) :
    compare (rebase (Category.comp_id a) (comp R (id D))) R = (CategoryTheory.Functor.leftUnitor R.act).hom := by
  symm; refine compare_unique (rebase (Category.comp_id a) (comp R (id D))) R _ ?_; intro x
  change 𝟙 _ ≫ R.lift x = R.lift x ≫ 𝟙 _
  simp

end Route
/- Pack and unpack verticality with strictly inverse functors, not an appeal to invariance of strict fibres. -/
namespace FibreTotal
variable (p : K ⥤ B) (A : B)
abbrev projection := gradeProjection (Y := Y) (e := e) ⋙ p
abbrev endpoint := Functor.Fiber.fiberInclusion (p := p) (S := A) ⋙ e

def into : Total Y (endpoint e p A) ⥤ (projection Y e p).Fiber A where
  obj x := ⟨pair Y e (grade _ _ x).val (payload _ _ x),(grade _ _ x).property⟩
  map f := ⟨(SpanPayload.Power.fibreInclude A Y p e).map f,
    (SpanPayload.lift_iff gradeProjection p rfl (𝟙 A) ((SpanPayload.Power.fibreInclude A Y p e).map f)).mpr (gradeMap f).property⟩
  map_id x := by
    apply Subtype.ext
    exact (SpanPayload.Power.fibreInclude A Y p e).map_id x
  map_comp f g := by
    apply Subtype.ext
    exact (SpanPayload.Power.fibreInclude A Y p e).map_comp f g

def baseObj (x : (projection Y e p).Fiber A) : p.Fiber A := ⟨grade _ _ x.val,x.property⟩

def outObj (x : (projection Y e p).Fiber A) : Total Y (endpoint e p A) :=
  pair _ _ (baseObj Y e p A x) (payload _ _ x.val)

def outMap {x y : (projection Y e p).Fiber A} (f : x ⟶ y) : outObj Y e p A x ⟶ outObj Y e p A y :=
  arrow (show baseObj Y e p A x ⟶ baseObj Y e p A y from
    ⟨gradeMap f.val,(SpanPayload.lift_iff gradeProjection p rfl (𝟙 A) f.val).mp f.property⟩) (payloadMap f.val)

theorem out_into {x y : Total Y (endpoint e p A)} (f : x ⟶ y) : outMap Y e p A ((into Y e p A).map f) = f := rfl
theorem into_out {x y : (projection Y e p).Fiber A} (f : x ⟶ y) : (into Y e p A).map (outMap Y e p A f) = f := rfl

instance intoFaithful : (into Y e p A).Faithful where
  map_injective {_ _} _f _g h := congrArg (outMap Y e p A) h

def out : (projection Y e p).Fiber A ⥤ Total Y (endpoint e p A) where
  obj := outObj Y e p A
  map := outMap Y e p A
  map_id x := (into Y e p A).map_injective ((into Y e p A).map_id (outObj Y e p A x)).symm
  map_comp f g := (into Y e p A).map_injective ((into Y e p A).map_comp (outMap Y e p A f) (outMap Y e p A g)).symm

theorem into_out_functors : into Y e p A ⋙ out Y e p A = 𝟭 _ := rfl
theorem out_into_functors : out Y e p A ⋙ into Y e p A = 𝟭 _ := rfl
instance intoEquivalence : (into Y e p A).IsEquivalence :=
  (show Total Y (endpoint e p A) ≌ (projection Y e p).Fiber A from
    { functor := into Y e p A, inverse := out Y e p A, unitIso := Iso.refl _, counitIso := Iso.refl _
      functor_unitIso_comp x := by change (into Y e p A).map (𝟙 x) ≫ 𝟙 _ = _; rw [Functor.map_id,Category.comp_id] }).isEquivalence_functor

end FibreTotal

open SpanPayload.Power
noncomputable def nativeReindex (n : Nat) {A D : B} (a : A ⟶ D) :
    Total Y (nativeEndpoint S n D) ⥤ Total Y (nativeEndpoint S n A) :=
  FibreTotal.into Y _ _ D ⋙ Reindex.functor (payloadChoice Y S n) a ⋙ FibreTotal.out Y _ _ A

noncomputable def nativeId (n : Nat) (A : B) : nativeReindex Y S n (𝟙 A) ≅ 𝟭 _ :=
  CategoryTheory.Functor.isoWhiskerLeft (FibreTotal.into Y _ _ A)
    (CategoryTheory.Functor.isoWhiskerRight (Route.unitIso (payloadChoice Y S n) A) (FibreTotal.out Y _ _ A))

noncomputable def nativeComp (n : Nat) {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    nativeReindex Y S n (a ≫ b) ≅ nativeReindex Y S n b ⋙ nativeReindex Y S n a :=
  CategoryTheory.Functor.isoWhiskerLeft (FibreTotal.into Y _ _ E)
    (CategoryTheory.Functor.isoWhiskerRight (Route.compIso (payloadChoice Y S n) a b) (FibreTotal.out Y _ _ A))

/- A comparison cone records the arrow as well as its underlying fibre functor. -/
namespace Change
variable {p : K ⥤ B} {q : L ⥤ B} {A D : B} (a : A ⟶ D) {X : Type*} [Category* X] (Z : X ⥤ q.Fiber D)
structure Cone where
  act : X ⥤ q.Fiber A
  lift (x : X) : (act.obj x).val ⟶ (Z.obj x).val
  over (x : X) : q.map (lift x) = eqToHom (act.obj x).property ≫ a ≫ eqToHom (Z.obj x).property.symm
  cart (x : X) : Cartesian q (lift x)
  natural {x y : X} (f : x ⟶ y) : (act.map f).val ≫ lift y = lift x ≫ (Z.map f).val

variable {a Z}
set_option backward.isDefEq.respectTransparency false in
theorem factor (R : Cone a Z) (y : X) {x : q.Fiber A} (f : x.val ⟶ (Z.obj y).val)
    (h : q.map f = eqToHom x.property ≫ a ≫ eqToHom (Z.obj y).property.symm) :
    ∃! t : x ⟶ R.act.obj y, t.val ≫ R.lift y = f := by
  obtain ⟨k,⟨hk,he⟩,uk⟩ := R.cart y x.val f (eqToHom x.property ≫ eqToHom (R.act.obj y).property.symm)
    (by rw [R.over,h]; simp)
  exact ⟨Reindex.verticalMk k hk,he,fun t ht => Subtype.ext (uk t.val ⟨Reindex.vertical_map t,ht⟩)⟩

theorem cancel (R : Cone a Z) {y : X} {x : q.Fiber A} {f g : x ⟶ R.act.obj y}
    (h : f.val ≫ R.lift y = g.val ≫ R.lift y) : f = g := by
  obtain ⟨_,_,uk⟩ := factor R y (g.val ≫ R.lift y) (by rw [q.map_comp,Reindex.vertical_map g,R.over]; simp)
  exact (uk f h).trans (uk g rfl).symm

noncomputable def app (R Q : Cone a Z) (x : X) : R.act.obj x ⟶ Q.act.obj x :=
  (factor Q x (R.lift x) (R.over x)).choose
theorem fac (R Q : Cone a Z) (x : X) : (app R Q x).val ≫ Q.lift x = R.lift x :=
  (factor Q x (R.lift x) (R.over x)).choose_spec.1

noncomputable def iso (R Q : Cone a Z) : R.act ≅ Q.act := NatIso.ofComponents (fun x =>
  { hom := app R Q x, inv := app Q R x
    hom_inv_id := by apply cancel R; change ((app R Q x).val ≫ (app Q R x).val) ≫ _ = 𝟙 _ ≫ _; rw [Category.assoc,fac,fac,Category.id_comp]
    inv_hom_id := by apply cancel Q; change ((app Q R x).val ≫ (app R Q x).val) ≫ _ = 𝟙 _ ≫ _; rw [Category.assoc,fac,fac,Category.id_comp] })
  (fun {x y} f => by
    apply cancel Q
    change ((R.act.map f).val ≫ (app R Q y).val) ≫ _ = ((app R Q x).val ≫ (Q.act.map f).val) ≫ _
    rw [Category.assoc,Category.assoc,fac,R.natural,Q.natural,← Category.assoc,fac])

theorem iso_unique (R Q : Cone a Z) (t : R.act ⟶ Q.act)
    (ht : ∀ x, (t.app x).val ≫ Q.lift x = R.lift x) : t = (iso R Q).hom := by
  ext x : 2
  apply cancel Q
  exact (ht x).trans (fac R Q x).symm

theorem iso_trans (R Q T : Cone a Z) : (iso R Q).hom ≫ (iso Q T).hom = (iso R T).hom := by
  apply iso_unique R T
  intro x
  change ((app R Q x).val ≫ (app Q T x).val) ≫ T.lift x = _
  rw [Category.assoc,fac,fac]

def before (Z : X ⥤ q.Fiber D) (R : Route q a) : Cone a Z :=
  ⟨Z ⋙ R.act,fun x => R.lift (Z.obj x),fun x => R.over (Z.obj x),fun x => R.cart (Z.obj x),fun f => R.natural (Z.map f)⟩

theorem ofStrong {p : K ⥤ B} {x y : K} (f : x ⟶ y) (h : p.IsStronglyCartesian (p.map f) f) : Cartesian p f := by
  intro z g a e
  let : p.IsHomLift (a ≫ p.map f) g := e ▸ (IsHomLift.map p g)
  obtain ⟨k,⟨hk,he⟩,uk⟩ := h.universal_property' a g
  let : p.IsHomLift a k := hk
  exact ⟨k,⟨(IsHomLift.eq_of_isHomLift p a k).symm,he⟩,fun t ht => uk t ⟨ht.1 ▸ (IsHomLift.map p t),ht.2⟩⟩

theorem presOfStrong (F : K ⥤ L) (H : F ⋙ q = p)
    (pres : ∀ {x y : K} {A D : B} (a : A ⟶ D) (f : x ⟶ y), p.IsStronglyCartesian a f → q.IsStronglyCartesian a (F.map f))
    {x y : K} (f : x ⟶ y) (h : Cartesian p f) : Cartesian q (F.map f) := by
  subst p
  exact ofStrong _ (pres _ f (strong h))

def after (F : K ⥤ L) (H : F ⋙ q = p) (R : Route p a)
    (pres : ∀ {x y : K} (f : x ⟶ y), Cartesian p f → Cartesian q (F.map f)) :
    Cone a (SpanPayload.fibreFunctor F q H D) := by
  subst p
  exact ⟨R.act ⋙ SpanPayload.fibreFunctor F q rfl A,fun x => F.map (R.lift x),fun x => R.over x,
    fun x => pres _ (R.cart x),fun f => by
      change F.map (R.act.map f).val ≫ F.map (R.lift _) = F.map (R.lift _) ≫ F.map f.val
      rw [← F.map_comp,← F.map_comp,R.natural]⟩

noncomputable def square (F : K ⥤ L) (H : F ⋙ q = p) (R : Route p a) (Q : Route q a)
    (pres : ∀ {x y : K} (f : x ⟶ y), Cartesian p f → Cartesian q (F.map f)) :
    R.act ⋙ SpanPayload.fibreFunctor F q H A ≅ SpanPayload.fibreFunctor F q H D ⋙ Q.act := by
  subst p
  exact iso (after F rfl R pres) (before _ Q)
end Change

/- Evaluate arbitrary (not just vertical) decorated arrows, then compare the two independently chosen restrictions. -/
namespace Evaluation
open TelescopeSquares
variable (Y : Bᵒᵖ ⥤ Cat.{j,k})
abbrev G (n : Nat) := Iterates.layer P S Y (n+1)
abbrev W (n : Nat) := Total Y (chainDest S n)

def obj {n : Nat} (x : W S Y n) : Total (G S Y n) (𝟭 B) :=
  pair _ _ (grade _ _ x).1 (realize Y S (grade _ _ x).2 (payload _ _ x))

def raw {n : Nat} {x y : W S Y n} (f : x ⟶ y) :
    DecoratedHom Y (gradeMap f).1 (grade _ _ x).2 (grade _ _ y).2 (payload _ _ x) (payload _ _ y) :=
  ⟨(gradeMap f).2,payloadMap f⟩

def hom {n : Nat} {x y : W S Y n} (f : x ⟶ y) : obj S Y x ⟶ obj S Y y :=
  arrow (gradeMap f).1 (squareEquiv Y S _ _ _ _ _ (raw S Y f))

private theorem payloadId {K : Type*} [Category* K] {e : K ⥤ B} {Y : Bᵒᵖ ⥤ Cat.{j,k}} (x : Total Y e) :
    HEq (payloadMap (𝟙 x)) (𝟙 (payload Y e x)) := by
  change HEq ((Grothendieck.Hom.fiber (𝟙 x.unop)).unop) _
  rw [Grothendieck.id_fiber]
  refine HEq.trans (heq_of_eq (eqToHom_unop (C := (Y.obj (op (e.obj (grade _ _ x))) : Type _)) _)) ?_
  exact eqToHom_heq_id_dom _ _ _

theorem raw_id {n : Nat} (x : W S Y n) : raw S Y (𝟙 x) = decoratedId S Y (grade _ _ x).2 (payload _ _ x) := by
  refine Sigma.ext (by rfl) ?_
  apply (payloadId x).trans
  symm
  exact eqToHom_heq_id_dom _ _ (by rw [terminal_id,op_id,Y.map_id]; rfl)

theorem raw_comp {n : Nat} {x y z : W S Y n} (f : x ⟶ y) (g : y ⟶ z) :
    raw S Y (f ≫ g) = decoratedComp S Y (raw S Y f) (raw S Y g) := by
  refine Sigma.ext (by rfl) ?_
  exact heq_of_eq (payload_comp f g)

set_option backward.isDefEq.respectTransparency false in
def functor (n : Nat) : W S Y n ⥤ Total (G S Y n) (𝟭 B) where
  obj := obj S Y
  map := hom S Y
  map_id x := by
    apply total_ext _ _ (by rfl)
    change HEq (squareEquiv Y S _ _ _ _ _ (raw S Y (𝟙 x))) _
    rw [raw_id]
    refine (heq_of_eq (square_id_native Y S (grade _ _ x).2 (payload _ _ x))).trans ?_
    exact (show HEq (TelescopeSquares.nativeId (G S Y n) (payload _ _ (obj S Y x))) (𝟙 _) from eqToHom_heq_id_dom _ _ _).trans (payloadId _).symm
  map_comp f g := by
    apply total_ext _ _ (by rfl)
    change HEq (squareEquiv Y S _ _ _ _ _ (raw S Y (f ≫ g))) _
    rw [raw_comp]
    refine (heq_of_eq (square_comp_native Y S (raw S Y f) (raw S Y g))).trans ?_
    exact heq_of_eq (payload_comp (hom S Y f) (hom S Y g)).symm

def homEquivalence {n : Nat} (x y : W S Y n) : (x ⟶ y) ≃ (obj S Y x ⟶ obj S Y y) :=
  (homEquiv x y).trans ((show _ ≃ (Σ a, DecoratedHom Y a (grade _ _ x).2 (grade _ _ y).2 (payload _ _ x) (payload _ _ y)) from
    ⟨fun f => ⟨f.1.1,f.1.2,f.2⟩,fun g => ⟨⟨g.1,g.2.1⟩,g.2.2⟩,fun _ => rfl,fun _ => rfl⟩).trans
    ((Equiv.sigmaCongrRight (fun a => squareEquiv Y S a _ _ _ _)).trans (homEquiv (obj S Y x) (obj S Y y)).symm))

instance full (n : Nat) : (functor S Y n).Full where
  map_surjective {x y} := (homEquivalence S Y x y).surjective
instance faithful (n : Nat) : (functor S Y n).Faithful where
  map_injective {x y} := (homEquivalence S Y x y).injective

theorem obj_surj (n : Nat) : Function.Surjective (functor S Y n).obj := by
  intro x
  obtain ⟨⟨t,y⟩,h⟩ := (realizedEquiv Y S (n+1) (grade _ _ x)).surjective (payload _ _ x)
  exact ⟨pair _ _ ⟨grade _ _ x,t⟩ y,congrArg (pair _ _ (grade _ _ x)) h⟩

def nativeFunctor (n : Nat) := SpanPayload.Power.global S n Y ⋙ functor S Y n

theorem native_over (n : Nat) : nativeFunctor S Y n ⋙ gradeProjection =
    gradeProjection ⋙ (positivePowers P S n).source := SpanPayload.Power.global_source S n Y

theorem native_cart {n : Nat} {A D : B} (a : A ⟶ D) {x y : Total Y (positivePowers P S n).dest} (f : x ⟶ y) :
    (gradeProjection ⋙ (positivePowers P S n).source).IsStronglyCartesian a f ↔
    gradeProjection.IsStronglyCartesian a ((nativeFunctor S Y n).map f) :=
  (SpanPayload.Power.global_cartesian S n Y a f).trans
    (SpanPayload.cartesian_iff (functor S Y n) gradeProjection rfl (obj_surj S Y n) a _)
theorem native_pres (n : Nat) {x y : Total Y (positivePowers P S n).dest} (f : x ⟶ y)
    (h : Cartesian (gradeProjection ⋙ (positivePowers P S n).source) f) :
    Cartesian gradeProjection ((nativeFunctor S Y n).map f) := by
  exact Change.presOfStrong _ (native_over S Y n) (fun a f => (native_cart S Y a f).mp) f h

def iterateChoice (n : Nat) : Cleavage (gradeProjection (Y := G S Y n) (e := 𝟭 B)) :=
  extendChoice (G S Y n) (𝟭 B) (𝟭 B) baseChoice

noncomputable def chosenSquare (n : Nat) {A D : B} (a : A ⟶ D) :
    Reindex.functor (payloadChoice Y S n) a ⋙ SpanPayload.fibreFunctor (nativeFunctor S Y n) gradeProjection (native_over S Y n) A ≅
      SpanPayload.fibreFunctor (nativeFunctor S Y n) gradeProjection (native_over S Y n) D ⋙ Reindex.functor (iterateChoice S Y n) a :=
  Change.square _ _ (Route.ofChoice _ a) (Route.ofChoice _ a) (native_pres S Y n)

instance nativeFull (n : Nat) : (nativeFunctor S Y n).Full := by unfold nativeFunctor; infer_instance
instance nativeFaithful (n : Nat) : (nativeFunctor S Y n).Faithful := by unfold nativeFunctor; infer_instance
theorem native_obj_surj (n : Nat) : Function.Surjective (nativeFunctor S Y n).obj :=
  (obj_surj S Y n).comp (SpanPayload.total_obj_surjective _ _ _ (powerPoints S n).decode.surjective)

def onFibre (n : Nat) (A : B) :
    Total Y (nativeEndpoint S n A) ⥤ (gradeProjection (Y := G S Y n) (e := 𝟭 B)).Fiber A :=
  FibreTotal.into Y _ _ A ⋙ SpanPayload.fibreFunctor (nativeFunctor S Y n) _ (native_over S Y n) A

instance onFibreEquivalence (n : Nat) (A : B) : (onFibre S Y n A).IsEquivalence := by
  exact @CategoryTheory.Functor.isEquivalence_trans _ _ _ _ _ _ (FibreTotal.into Y (native S n).dest (native S n).source A) (SpanPayload.fibreFunctor (nativeFunctor S Y n) gradeProjection (native_over S Y n) A) (FibreTotal.intoEquivalence ..) (SpanPayload.fibre_isEquivalence _ _ _ _ (native_obj_surj S Y n))

noncomputable def fibreSquare (n : Nat) {A D : B} (a : A ⟶ D) :
    nativeReindex Y S n a ⋙ onFibre S Y n A ≅ onFibre S Y n D ⋙ Reindex.functor (iterateChoice S Y n) a :=
  CategoryTheory.Functor.isoWhiskerLeft (FibreTotal.into Y _ _ D) (chosenSquare S Y n a)

theorem iterate_computation (n : Nat) {A D : B} (a : A ⟶ D) (y : (G S Y n).obj (op D)) :
    (Reindex.object (iterateChoice S Y n) a (⟨pair _ (𝟭 B) D y,rfl⟩ : gradeProjection.Fiber D)).val =
      pair (G S Y n) (𝟭 B) A (((G S Y n).map a.op).toFunctor.obj y) := by
  change pair (G S Y n) (𝟭 B) A (((G S Y n).map (a ≫ 𝟙 D).op).toFunctor.obj y) = _
  rw [Category.comp_id]

end Evaluation
end ContextualComposition.GrothendieckStep.NativeCleavage
