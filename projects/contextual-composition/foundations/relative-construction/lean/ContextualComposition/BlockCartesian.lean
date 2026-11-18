module
public import ContextualComposition.NativeBlocks
@[expose] public section
namespace ContextualComposition.GrothendieckStep.BlockCartesian
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeCleavage
universe i j k l
variable {C D E B : Type*} [Category* C] [Category* D] [Category* E] [Category* B]
/-- All arrows with specified target, retaining the entire varying source. -/
abbrev Incoming (x : C) := Σ z : C, z ⟶ x
def push (F : C ⥤ D) {x : C} (z : Incoming x) : Incoming (F.obj x) :=
  ⟨F.obj z.1,F.map z.2⟩
def post {x y : C} (f : x ⟶ y) (z : Incoming x) : Incoming y := ⟨z.1,z.2 ≫ f⟩
theorem push_post (F : C ⥤ D) {x y : C} (f : x ⟶ y) (z : Incoming x) :
    push F (post f z) = post (F.map f) (push F z) := by
  exact Sigma.ext (by rfl) (heq_of_eq (F.map_comp _ _))
/-- Every arrow into the image of x has a unique lift into x, including its source. -/
def UniqueIncoming (F : C ⥤ D) : Prop := ∀ x, Function.Bijective (push F (x := x))
noncomputable def liftInto (F : C ⥤ D) (h : UniqueIncoming F) (x : C) : Incoming (F.obj x) ≃ Incoming x :=
  (Equiv.ofBijective _ (h x)).symm
theorem push_liftInto (F : C ⥤ D) (h : UniqueIncoming F) (x : C) (g : Incoming (F.obj x)) :
    push F (liftInto F h x g) = g := (Equiv.ofBijective _ (h x)).apply_symm_apply g
theorem liftInto_post (F : C ⥤ D) (h : UniqueIncoming F) {x y : C} (f : x ⟶ y) (g : Incoming (F.obj x)) :
    liftInto F h y (post (F.map f) g) = post f (liftInto F h x g) := by
  apply (h y).injective
  rw [push_liftInto,push_post,push_liftInto]
theorem idIncoming : UniqueIncoming (𝟭 C) := fun _ => Function.bijective_id
theorem compIncoming {F : C ⥤ D} {G : D ⥤ E} (h : UniqueIncoming F) (k : UniqueIncoming G) :
    UniqueIncoming (F ⋙ G) := fun x => (k _).comp (h x)
theorem isoIncoming (F : C ⥤ D) [F.IsIso] : UniqueIncoming F := by
  intro x
  constructor
  · rintro ⟨z,a⟩ ⟨u,b⟩ h
    obtain rfl := F.bijective_obj.injective (congrArg Sigma.fst h)
    obtain rfl := F.map_injective (Sigma.mk.inj_iff.mp h).2.eq
    rfl
  · rintro ⟨v,b⟩
    obtain ⟨z,rfl⟩ := F.bijective_obj.surjective v
    obtain ⟨a,rfl⟩ := F.map_surjective b
    exact ⟨⟨z,a⟩,rfl⟩

section Tags
variable {I : Type i} {K : I → Type j} [∀ i, Category.{k} (K i)]
theorem inclIncoming (i : I) : UniqueIncoming (Sigma.incl (C := K) i) := by
  intro x
  constructor
  · rintro ⟨z,a⟩ ⟨u,b⟩ h
    have he : (⟨i,z⟩ : Σ i, K i) = ⟨i,u⟩ := congrArg Sigma.fst h
    obtain rfl := (Sigma.mk.inj_iff.mp he).2.eq
    obtain rfl := (Sigma.incl i).map_injective (Sigma.mk.inj_iff.mp h).2.eq
    rfl
  · rintro ⟨⟨j,z⟩,a⟩; cases a with | mk a => exact ⟨⟨_,a⟩,rfl⟩
theorem descIncoming (F : ∀ i, K i ⥤ D) (h : ∀ i, UniqueIncoming (F i)) :
    UniqueIncoming (Sigma.desc F) := by
  rintro ⟨i,x⟩
  constructor
  · rintro ⟨⟨j,z⟩,a⟩ ⟨⟨k,u⟩,b⟩ e
    cases a with | mk a =>
      cases b with | mk b =>
        have hh := (h i x).injective (a₁ := ⟨_,a⟩) (a₂ := ⟨_,b⟩) e
        exact congrArg (push (Sigma.incl i)) hh
  · intro z
    obtain ⟨q,e⟩ := (h i x).surjective z
    exact ⟨push (Sigma.incl i) q,e⟩
end Tags

/-- The usual cartesian factorization, indexed by a pair of complete incoming arrows. -/
theorem cartesian_incoming (p : C ⥤ B) {x y : C} (f : x ⟶ y) :
    Cartesian p f ↔ ∀ (g : Incoming y) (a : Incoming (p.obj x)), push p g = post (p.map f) a →
      ∃! h : Incoming x, push p h = a ∧ post f h = g := by
  constructor
  · intro hf
    rintro ⟨z,g⟩ ⟨b,a⟩ e
    obtain rfl := congrArg Sigma.fst e
    obtain ⟨u,⟨hu,ug⟩,uniq⟩ := hf z g a (Sigma.mk.inj_iff.mp e).2.eq
    refine ⟨⟨z,u⟩,⟨by exact Sigma.ext rfl (heq_of_eq hu),by exact Sigma.ext rfl (heq_of_eq ug)⟩,?_⟩
    rintro ⟨w,v⟩ ⟨eq₁,eq₂⟩
    obtain rfl := congrArg Sigma.fst eq₂
    exact Sigma.ext rfl (heq_of_eq (uniq v ⟨(Sigma.mk.inj_iff.mp eq₁).2.eq,(Sigma.mk.inj_iff.mp eq₂).2.eq⟩))
  · intro hf z g a e
    obtain ⟨⟨w,v⟩,⟨h,k⟩,uniq⟩ := hf ⟨z,g⟩ ⟨p.obj z,a⟩ (Sigma.ext rfl (heq_of_eq e))
    obtain rfl := congrArg Sigma.fst k
    refine ⟨v,⟨(Sigma.mk.inj_iff.mp h).2.eq,(Sigma.mk.inj_iff.mp k).2.eq⟩,?_⟩
    intro u hu
    exact (Sigma.mk.inj_iff.mp (uniq ⟨_,u⟩ ⟨Sigma.ext rfl (heq_of_eq hu.1),Sigma.ext rfl (heq_of_eq hu.2)⟩)).2.eq

theorem cartesian_iff (F : C ⥤ D) (h : UniqueIncoming F) (q : D ⥤ B) {x y : C} (f : x ⟶ y) :
    Cartesian (F ⋙ q) f ↔ Cartesian q (F.map f) := by
  simp only [cartesian_incoming]
  constructor
  · intro hc g a e
    obtain ⟨g,rfl⟩ := (h y).surjective g
    obtain ⟨k,⟨ka,kg⟩,uniq⟩ := hc g a e
    refine ⟨push F k,⟨ka,(push_post F f k).symm.trans (congrArg (push F) kg)⟩,?_⟩
    intro u hu
    obtain ⟨v,rfl⟩ := (h x).surjective u
    exact congrArg (push F) (uniq v ⟨hu.1,(h y).injective ((push_post F f v).trans hu.2)⟩)
  · intro hc g a e
    obtain ⟨k,⟨ka,kg⟩,uniq⟩ := hc (push F g) a e
    obtain ⟨v,rfl⟩ := (h x).surjective k
    refine ⟨v,⟨ka,(h y).injective ((push_post F f v).trans kg)⟩,?_⟩
    intro u hu
    exact (h x).injective (uniq (push F u) ⟨hu.1,(push_post F f u).symm.trans (congrArg (push F) hu.2)⟩)


theorem faithful (F : C ⥤ D) (h : UniqueIncoming F) : F.Faithful where
  map_injective {x y} f g e := (Sigma.mk.inj_iff.mp ((h y).injective (a₁ := ⟨x,f⟩) (a₂ := ⟨x,g⟩)
    (Sigma.ext (by rfl) (heq_of_eq e)))).2.eq

theorem strong_characterization (p : C ⥤ B) {A D : B} (a : A ⟶ D) {x y : C} (f : x ⟶ y) :
    p.IsStronglyCartesian a f ↔ p.IsHomLift a f ∧ Cartesian p f := by
  constructor
  · intro h
    refine ⟨h.toIsHomLift,?_⟩
    let := h.toIsHomLift
    subst_hom_lift p a f
    exact Change.ofStrong f h
  · rintro ⟨hl,hc⟩
    let := hl
    subst_hom_lift p a f
    exact NativeCleavage.strong hc
theorem strong_iff (F : C ⥤ D) (hf : UniqueIncoming F) (q : D ⥤ B) {p : C ⥤ B} (H : F ⋙ q = p)
    {A E : B} (a : A ⟶ E) {x y : C} (f : x ⟶ y) :
    p.IsStronglyCartesian a f ↔ q.IsStronglyCartesian a (F.map f) := by
  subst p
  rw [strong_characterization,strong_characterization]
  exact and_congr (SpanPayload.lift_iff F q rfl a f) (cartesian_iff F hf q f)

section Change
variable {J : Type*} [Category* J] (F : C ⥤ D) (d : D ⥤ B) (p : J ⥤ B) {e : C ⥤ B} (h : F ⋙ d = e)
def onMatch : Strict.Match e p ⥤ Strict.Match d p :=
  Strict.lift _ _ (Strict.fst _ _ ⋙ F) (Strict.snd _ _) ((congrArg (Strict.fst e p ⋙ ·) h).trans (Strict.commute e p))

theorem matchIncoming (hF : UniqueIncoming F) : UniqueIncoming (onMatch F d p h) := by
  subst e; intro z
  constructor
  · rintro ⟨⟨x,u,hx⟩,⟨⟨a,b,w⟩⟩⟩ ⟨⟨y,v,hy⟩,⟨⟨c,k,w'⟩⟩⟩ eq
    have l : push F (⟨x,a⟩ : Incoming z.fst) = push F ⟨y,c⟩ :=
      congrArg (push (Strict.fst d p)) eq
    obtain ⟨hxy,hac⟩ := Sigma.mk.inj_iff.mp ((hF _).injective l)
    subst y; obtain rfl := hac.eq
    have r : (⟨u,b⟩ : Incoming z.snd) = ⟨v,k⟩ := congrArg (push (Strict.snd d p)) eq
    obtain ⟨huv,hbk⟩ := Sigma.mk.inj_iff.mp r
    subst v; obtain rfl := hbk.eq; rfl
  · rintro ⟨⟨x,u,hx⟩,⟨⟨a,b,w⟩⟩⟩
    obtain ⟨⟨y,c⟩,eq⟩ := (hF z.fst).surjective ⟨x,a⟩
    obtain ⟨hy,he⟩ := Sigma.mk.inj_iff.mp eq
    change F.obj y = x at hy; subst x
    obtain rfl := he.eq
    exact ⟨⟨⟨y,u,hx⟩,⟨⟨c,b,w⟩⟩⟩,rfl⟩
end Change


section Faces
variable (F : C ⥤ D) {p : C ⥤ B} (q : D ⥤ B) (H : F ⋙ q = p)
variable (h : ∀ {x y : C} (f : x ⟶ y), Cartesian p f → Cartesian q (F.map f))
variable (L : Cleavage p) (J : Cleavage q)
noncomputable def chosenFace {A E : B} (a : A ⟶ E) :
    NativeCube.Face (Route.ofChoice L a) (Route.ofChoice J a) F H :=
  ⟨Change.square _ _ _ _ h,NativeCube.changeFac _ _ _ _ h⟩
theorem chosenUnit (A : B) : FibreValue.Paste.UnitLaw (F := SpanPayload.fibreFunctor F q H A)
    (X := Reindex.functor L (𝟙 A)) (Y := Reindex.functor J (𝟙 A)) (chosenFace F q H h L J (𝟙 A)).sq
    (Route.unitIso L A).hom (Route.unitIso J A).hom :=
  fun x => NatTrans.congr_app (FibreValue.Laws.unitDiagram q F H h L J A) x
theorem chosenComp {A D' E : B} (a : A ⟶ D') (b : D' ⟶ E) :
    FibreValue.Paste.CompLaw (F := SpanPayload.fibreFunctor F q H A) (G := SpanPayload.fibreFunctor F q H D')
      (H := SpanPayload.fibreFunctor F q H E)
      (X := Reindex.functor L a) (Y := Reindex.functor L b) (W := Reindex.functor L (a ≫ b))
      (X' := Reindex.functor J a) (Y' := Reindex.functor J b) (W' := Reindex.functor J (a ≫ b))
      (chosenFace F q H h L J (a ≫ b)).sq (chosenFace F q H h L J a).sq (chosenFace F q H h L J b).sq
      (Route.compIso L a b).hom (Route.compIso J a b).hom :=
  fun x => NatTrans.congr_app (FibreValue.Laws.compDiagram q F H h L J a b) x
end Faces
section Product
variable {K J : Type*} [Category* K] [Category* J] (e : K ⥤ B) (p : J ⥤ B)
set_option backward.isDefEq.respectTransparency false in
/-- Pulling a cartesian second component back to the strict matching category
gives a cartesian arrow for the first projection. The matching square may
contain nonidentity maps and its equality transports are retained. -/
theorem fstCartesian {x y : Strict.Match e p} (f : x ⟶ y) (hc : Cartesian p f.hom.snd) :
    Cartesian (Strict.fst e p) f := by
  intro z g a eg
  change z.fst ⟶ x.fst at a
  change g.hom.fst = a ≫ f.hom.fst at eg
  let b := eqToHom z.glue.symm ≫ e.map a ≫ eqToHom x.glue
  have hz := g.hom.w
  have hx := f.hom.w
  change e.map g.hom.fst ≫ eqToHom y.glue = eqToHom z.glue ≫ p.map g.hom.snd at hz
  change e.map f.hom.fst ≫ eqToHom y.glue = eqToHom x.glue ≫ p.map f.hom.snd at hx
  have hb : p.map g.hom.snd = b ≫ p.map f.hom.snd := by
    dsimp [b]
    rw [Category.assoc,Category.assoc,← hx,← Category.assoc (e.map a),← e.map_comp,← eg,hz]
    simp
  obtain ⟨t,⟨over,fac⟩,uniq⟩ := hc _ _ _ hb
  have comm : e.map a ≫ eqToHom x.glue = eqToHom z.glue ≫ p.map t := by rw [over]; dsimp [b]; simp
  let u : z ⟶ x := ⟨⟨a,t,comm⟩⟩
  refine ⟨u,⟨rfl,InducedCategory.hom_ext (Limits.CategoricalPullback.hom_ext eg.symm fac)⟩,?_⟩
  intro l hl
  apply InducedCategory.hom_ext
  apply Limits.CategoricalPullback.hom_ext hl.1
  apply uniq
  constructor
  · have ww := l.hom.w
    change e.map l.hom.fst ≫ eqToHom x.glue = eqToHom z.glue ≫ p.map l.hom.snd at ww
    have hla : l.hom.fst = a := hl.1
    rw [hla] at ww
    dsimp [b]
    rw [ww]; simp
  · exact congrArg (fun k : z ⟶ y => k.hom.snd) hl.2

variable (s : K ⥤ B) (L : Cleavage s) (R : Cleavage p)
def prefixLift (A : B) (y : Strict.Match e p) (a : A ⟶ s.obj y.fst) := L A y.fst a
def suffixLift (A : B) (y : Strict.Match e p) (a : A ⟶ s.obj y.fst) :=
  R (e.obj (prefixLift e p s L A y a).obj) y.snd (e.map (prefixLift e p s L A y a).lift ≫ eqToHom y.glue)
def productChoice : Cleavage (Strict.fst e p ⋙ s) := fun A y a => by
  let U := prefixLift e p s L A y a
  let V := suffixLift e p s L R A y a
  let x : Strict.Match e p := ⟨U.obj,V.obj,V.source.symm⟩
  have w : e.map U.lift ≫ eqToHom y.glue = eqToHom V.source.symm ≫ p.map V.lift := by
    rw [V.over]; simp; rfl
  let m : x ⟶ y := ⟨⟨U.lift,V.lift,w⟩⟩
  exact ⟨x,U.source,m,U.over,NativeCleavage.composite (fstCartesian e p m V.cart) U.cart⟩
end Product

section Weighted
variable {K L : Type*} [Category* K] [Category* L] (Y : Bᵒᵖ ⥤ Cat.{l,j})
variable (d : K ⥤ B) (y : Total Y d)
abbrev PayloadIn (u : Incoming (grade Y d y)) := Σ z : Y.obj (op (d.obj u.1)),
  z ⟶ (Y.map (d.map u.2).op).toFunctor.obj (payload Y d y)
def decompose : Incoming y ≃ Σ u : Incoming (grade Y d y), PayloadIn Y d y u where
  toFun z := ⟨⟨grade Y d z.1,gradeMap z.2⟩,payload Y d z.1,payloadMap z.2⟩
  invFun := fun ⟨⟨k,a⟩,z,f⟩ => ⟨pair Y d k z,arrow a f⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem totalIncoming (F : L ⥤ K) {e : L ⥤ B} (h : F ⋙ d = e) (H : UniqueIncoming F) :
    UniqueIncoming (SpanPayload.totalMap Y F d h) := by
  subst e; intro y
  let G := SpanPayload.totalMap Y F d rfl
  let mv : (Σ a : Incoming (grade _ _ y), PayloadIn Y (F ⋙ d) y a) →
      Σ b : Incoming (grade _ _ (G.obj y)), PayloadIn Y d (G.obj y) b :=
    fun ⟨a,t⟩ => ⟨push F a,t⟩
  have hm : Function.Bijective mv := by
    constructor
    · rintro ⟨a,t⟩ ⟨b,s⟩ he
      obtain rfl := (H _).injective (congrArg Sigma.fst he)
      obtain rfl := (Sigma.mk.inj_iff.mp he).2.eq
      rfl
    · rintro ⟨a,t⟩
      obtain ⟨b,rfl⟩ := (H _).surjective a
      exact ⟨⟨b,t⟩,rfl⟩
  exact (decompose Y d (G.obj y)).symm.bijective.comp (hm.comp (decompose Y (F ⋙ d) y).bijective)
end Weighted

section Binary
universe b w
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,b,w} B} (S : P.Split)
theorem binaryIncoming : UniqueIncoming (binary S) := by
  let I : IsoCat (pairs S) (parts S) := ⟨splitPairs S,gatherPairs S,(split_gather S).symm,gather_split S⟩
  let : I.functor.IsIso := I.isIso_functor
  let J (i : Nat × Nat) : (blocks S i.1 i.2).strictIso.inverse.IsIso := (blocks S i.1 i.2).strictIso.symm.isIso_functor
  exact compIncoming (isoIncoming I.functor) (descIncoming _ fun i =>
    compIncoming (isoIncoming (blocks S i.1 i.2).strictIso.inverse) (inclIncoming (K := fun n => (power S n).apex) _))
end Binary

namespace All
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
open NativeBlocks.Nested
theorem extendIncoming {U : Span (B := B)} (F : Over U (whole S)) (h : UniqueIncoming F.functor) :
    UniqueIncoming (extend S F).functor :=
  compIncoming (matchIncoming F.functor (rightLeg S) (leftLeg S) F.dest h) (binaryIncoming S)
theorem collapseIncoming : (k : Nat) → UniqueIncoming (collapse S k).functor
  | 0 => inclIncoming (K := fun n => (power S n).apex) 0
  | 1 => idIncoming
  | k+2 => extendIncoming S _ (collapseIncoming (k+1))
theorem flattenIncoming : UniqueIncoming (flatten S) := descIncoming _ (collapseIncoming S)
abbrev source : strings S ⥤ B := Sigma.desc (fun k => (word S k).source)
abbrev dest : strings S ⥤ B := Sigma.desc (fun k => (word S k).dest)
theorem sourceCartesian {x y : strings S} (f : x ⟶ y) :
    Cartesian (source S) f ↔ Cartesian (leftLeg S) ((flatten S).map f) := by
  unfold source; rw [← flatten_source]; exact cartesian_iff _ (flattenIncoming S) _ f
theorem destCartesian {x y : strings S} (f : x ⟶ y) :
    Cartesian (dest S) f ↔ Cartesian (rightLeg S) ((flatten S).map f) := by
  unfold dest; rw [← flatten_dest]; exact cartesian_iff _ (flattenIncoming S) _ f
theorem strongCartesian {A D : B} (a : A ⟶ D) {x y : strings S} (f : x ⟶ y) :
    (source S).IsStronglyCartesian a f ↔ (leftLeg S).IsStronglyCartesian a ((flatten S).map f) :=
  strong_iff _ (flattenIncoming S) _ (flatten_source S) a f
instance flattenFaithful : (flatten S).Faithful := faithful _ (flattenIncoming S)
/-- Build the cleavage before flattening, by first lifting the prefix
and then the final block along the actual endpoint of that prefix lift. -/
def wordChoice (J : Cleavage (leftLeg S)) : (n : Nat) → Cleavage (word S n).source
  | 0 => baseChoice
  | 1 => J
  | n+2 => productChoice _ _ _ (wordChoice J (n+1)) J
def nativeChoice : Cleavage (leftLeg S) := SpanPull.choice _ (SpanPull.All.parts S)
def nestedChoice (J : Cleavage (leftLeg S)) : Cleavage (source S) :=
  SpanPull.choice _ (wordChoice S J)

noncomputable def sourceFace (L : Cleavage (source S)) (J : Cleavage (leftLeg S)) {A D : B} (a : A ⟶ D) :
    NativeCube.Face (Route.ofChoice L a) (Route.ofChoice J a) (flatten S) (flatten_source S) :=
  ⟨Change.square _ _ _ _ (fun f => (sourceCartesian S f).mp),
    NativeCube.changeFac _ _ _ _ (fun f => (sourceCartesian S f).mp)⟩

variable (Y : Bᵒᵖ ⥤ Cat.{l,j})
noncomputable abbrev weighted := SpanPayload.totalMap Y (flatten S) (rightLeg S) (flatten_dest S)
abbrev nestedProj := FibreTotal.projection Y (dest S) (source S)
abbrev nativeProj := FibreTotal.projection Y (rightLeg S) (leftLeg S)
theorem weightedOver : weighted S Y ⋙ nativeProj S Y = nestedProj S Y :=
  (congrArg (· ⋙ leftLeg S) (SpanPayload.total_projection Y (flatten S) (rightLeg S) (flatten_dest S))).trans
    (congrArg (gradeProjection ⋙ ·) (flatten_source S))
theorem weightedIncoming : UniqueIncoming (weighted S Y) :=
  totalIncoming Y _ _ (flatten_dest S) (flattenIncoming S)
theorem weightedCartesian {x y : Total Y (dest S)} (f : x ⟶ y) :
    Cartesian (nestedProj S Y) f ↔ Cartesian (nativeProj S Y) ((weighted S Y).map f) := by
  rw [← weightedOver]; exact cartesian_iff _ (weightedIncoming S Y) _ f

theorem weightedStrong {A D : B} (a : A ⟶ D) {x y : Total Y (dest S)} (f : x ⟶ y) :
    (nestedProj S Y).IsStronglyCartesian a f ↔ (nativeProj S Y).IsStronglyCartesian a ((weighted S Y).map f) :=
  strong_iff _ (weightedIncoming S Y) _ (weightedOver S Y) a f
variable (L : Cleavage (source S)) (J : Cleavage (leftLeg S))
abbrev nestedWeightedChoice := extendChoice Y (dest S) (source S) L
abbrev nativeWeightedChoice := extendChoice Y (rightLeg S) (leftLeg S) J
noncomputable abbrev onFibre (A : B) := SpanPayload.fibreFunctor (weighted S Y) (nativeProj S Y) (weightedOver S Y) A
noncomputable def weightedFace {A D : B} (a : A ⟶ D) :
    NativeCube.Face (Route.ofChoice (nestedWeightedChoice S Y L) a) (Route.ofChoice (nativeWeightedChoice S Y J) a)
      (weighted S Y) (weightedOver S Y) :=
  chosenFace (weighted S Y) _ (weightedOver S Y) (fun f => (weightedCartesian S Y f).mp) (nestedWeightedChoice S Y L) (nativeWeightedChoice S Y J) a
set_option maxHeartbeats 1200000 in
theorem unitLaw (A : B) :
    FibreValue.Paste.UnitLaw (F := onFibre S Y A) (X := Reindex.functor (nestedWeightedChoice S Y L) (𝟙 A))
      (Y := Reindex.functor (nativeWeightedChoice S Y J) (𝟙 A)) (weightedFace S Y L J (𝟙 A)).sq
      (Route.unitIso (nestedWeightedChoice S Y L) A).hom (Route.unitIso (nativeWeightedChoice S Y J) A).hom :=
  chosenUnit (weighted S Y) _ (weightedOver S Y) (fun f => (weightedCartesian S Y f).mp) (nestedWeightedChoice S Y L) (nativeWeightedChoice S Y J) A
set_option maxHeartbeats 1200000 in
theorem compLaw {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    FibreValue.Paste.CompLaw (F := onFibre S Y A) (G := onFibre S Y D) (H := onFibre S Y E)
      (X := Reindex.functor (nestedWeightedChoice S Y L) a) (Y := Reindex.functor (nestedWeightedChoice S Y L) b)
      (W := Reindex.functor (nestedWeightedChoice S Y L) (a ≫ b))
      (X' := Reindex.functor (nativeWeightedChoice S Y J) a) (Y' := Reindex.functor (nativeWeightedChoice S Y J) b)
      (W' := Reindex.functor (nativeWeightedChoice S Y J) (a ≫ b))
      (weightedFace S Y L J (a ≫ b)).sq (weightedFace S Y L J a).sq (weightedFace S Y L J b).sq
      (Route.compIso (nestedWeightedChoice S Y L) a b).hom (Route.compIso (nativeWeightedChoice S Y J) a b).hom :=
  chosenComp (weighted S Y) _ (weightedOver S Y) (fun f => (weightedCartesian S Y f).mp) (nestedWeightedChoice S Y L) (nativeWeightedChoice S Y J) a b

variable {Y} {Z : Bᵒᵖ ⥤ Cat.{l,j}} (T : Y ⟶ Z)
theorem payloadSquare : ChainPayload.fibreMap T (dest S) ⋙ weighted S Z = weighted S Y ⋙ ChainPayload.fibreMap T (rightLeg S) :=
  (SpanPayload.total_payload_natural (flatten S) (rightLeg S) (flatten_dest S) T).symm
theorem fibrePayload (A : B) :
    PayloadLift.action T (dest S) (source S) A ⋙ onFibre S Z A =
      onFibre S Y A ⋙ PayloadLift.action T (rightLeg S) (leftLeg S) A := by
  apply EvalPayload.cancelInclusion
  let I := Functor.Fiber.fiberInclusion (p := nestedProj S Y) (S := A)
  exact (EvalPayload.fibrePaste A _ _ (PayloadLift.over T _ _) (weightedOver S Z)).trans
    ((congrArg (I ⋙ ·) (payloadSquare S T)).trans (EvalPayload.fibrePaste A _ _ (weightedOver S Y) (PayloadLift.over T _ _)).symm)
/-- Both orders of evaluating the base-change and payload-change faces factor
the same arrow over the same chosen target lift. Neither face is replaced by identity. -/
theorem mixedLaw {A D : B} (a : A ⟶ D) :
    NativeCube.Face.Law (NativeCube.payload T (dest S) (source S) L a) (weightedFace S Z L J a)
      (weightedFace S Y L J a) (NativeCube.payload T (rightLeg S) (leftLeg S) J a)
      (fibrePayload S T A) (fibrePayload S T D) :=
  NativeCube.Face.law _ _ _ _ (payloadSquare S T) _ _
end All
end ContextualComposition.GrothendieckStep.BlockCartesian
