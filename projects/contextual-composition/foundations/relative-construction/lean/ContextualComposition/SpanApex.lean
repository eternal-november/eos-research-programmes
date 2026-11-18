module
public import ContextualComposition.ChainPayload
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep.SpanApex
open CategoryTheory CategoryTheory.Limits Opposite TelescopeSquares
universe b w u v k j
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K]
variable (P : Endpoints.{b,w,u,v} B)
abbrev Apex := Total P.grades (𝟭 B)
def left : Apex P ⥤ B := gradeProjection

private theorem payload_id (x : Apex P) : payloadMap (𝟙 x) = headId (P := P) (payload _ _ x) := by
  change (Grothendieck.Hom.fiber (𝟙 x.unop)).unop = _
  rw [Grothendieck.id_fiber]
  apply eqToHom_unop

def right (S : P.Split) : Apex P ⥤ B where
  obj x := (P.extend (grade _ _ x)).obj (payload _ _ x)
  map f := next (gradeMap f) (payloadMap f)
  map_id x := by rw [payload_id]; exact next_id S _
  map_comp f g := by rw [payload_comp]; exact next_comp S _ _

variable (e : K ⥤ B)
/-- The second projection retains the actual dependent grade arrow. -/
def second : Total P.grades e ⥤ Apex P :=
  (Grothendieck.pre (diagram P.grades (𝟭 B)) e.op).op

theorem matching :
    gradeProjection (Y := P.grades) (e := e) ⋙ e = second P e ⋙ left P := rfl

def intoPullback : Total P.grades e ⥤ CategoricalPullback e (left P) where
  obj x := ⟨grade _ _ x,(second P e).obj x,Iso.refl _⟩
  map f := ⟨gradeMap f,(second P e).map f,by change e.map (gradeMap f) ≫ 𝟙 _ = 𝟙 _ ≫ e.map (gradeMap f); simp⟩
  map_id x := CategoricalPullback.hom_ext rfl ((second P e).map_id x)
  map_comp f g := CategoricalPullback.hom_ext rfl ((second P e).map_comp f g)

theorem projection_fst : intoPullback P e ⋙ CategoricalPullback.π₁ _ _ = gradeProjection := rfl
theorem projection_snd : intoPullback P e ⋙ CategoricalPullback.π₂ _ _ = second P e := rfl

set_option backward.isDefEq.respectTransparency false in
theorem compatible {x y : Total P.grades e} (h : (intoPullback P e).obj x ⟶ (intoPullback P e).obj y) :
    e.map h.fst = gradeMap h.snd := by
  change e.map h.fst = (left P).map h.snd
  simpa only [intoPullback, Iso.refl_hom, Category.comp_id, Category.id_comp] using h.w

def fromMatched {x y : Total P.grades e} (h : (intoPullback P e).obj x ⟶ (intoPullback P e).obj y) : x ⟶ y :=
  arrow h.fst (payloadMap h.snd ≫ eqToHom (congrArg
    (fun a : e.obj (grade _ _ x) ⟶ e.obj (grade _ _ y) =>
      (P.grades.map a.op).toFunctor.obj (payload _ _ y)) (compatible P e h).symm))

set_option backward.isDefEq.respectTransparency false in
theorem recover {x y : Total P.grades e} (h : (intoPullback P e).obj x ⟶ (intoPullback P e).obj y) :
    (intoPullback P e).map (fromMatched P e h) = h := by
  refine CategoricalPullback.hom_ext (by rfl) ?_
  apply (homEquiv _ _).injective
  refine Sigma.ext (compatible P e h) ?_
  have aux {C : Type u} [Category.{v} C] {c d d' : C} (m : c ⟶ d) (j : d = d') :
      HEq (m ≫ eqToHom j) m := by subst d'; simp
  exact aux (payloadMap h.snd) _

instance full : (intoPullback P e).Full where
  map_surjective h := ⟨fromMatched P e h,recover P e h⟩

theorem retract {x y : Total P.grades e} (f : x ⟶ y) :
    fromMatched P e ((intoPullback P e).map f) = f := by
  apply (homEquiv _ _).injective
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  exact Category.comp_id _

instance faithful : (intoPullback P e).Faithful where
  map_injective {x y} f g h := by
    simpa only [retract] using congrArg (fromMatched P e (x := x) (y := y)) h
def normalize (z : CategoricalPullback e (left P)) : Total P.grades e :=
  pair _ _ z.fst ((P.grades.map z.iso.hom.op).toFunctor.obj (payload _ _ z.snd))

def normalizeIso (z : CategoricalPullback e (left P)) :
    (intoPullback P e).obj (normalize P e z) ≅ z :=
  CategoricalPullback.mkIso (Iso.refl z.fst)
    (Grothendieck.transportIso z.snd.unop z.iso.op).symm.op (by
      change e.map (𝟙 _) ≫ z.iso.hom = 𝟙 _ ≫ z.iso.hom
      rw [e.map_id])

instance essSurj : (intoPullback P e).EssSurj where
  mem_essImage z := ⟨normalize P e z,⟨normalizeIso P e z⟩⟩

instance isEquivalence : (intoPullback P e).IsEquivalence where

noncomputable def equivalence : Total P.grades e ≌ CategoricalPullback e (left P) :=
  (intoPullback P e).asEquivalence

/-- The binary composable-grade presentation and its strict endpoint equations. -/
abbrev Binary (S : P.Split) := Total P.grades (right P S)
abbrev EquipmentPair (S : P.Split) := CategoricalPullback (right P S) (left P)
noncomputable def binaryEquivalence (S : P.Split) : Binary P S ≌ EquipmentPair P S := equivalence P _

def binaryLeft (S : P.Split) : Binary P S ⥤ B := gradeProjection ⋙ left P
def binaryRight (S : P.Split) : Binary P S ⥤ B := second P (right P S) ⋙ right P S

theorem binaryLeft_agrees (S : P.Split) :
    intoPullback P (right P S) ⋙ CategoricalPullback.π₁ _ _ ⋙ left P = binaryLeft P S := rfl
theorem binaryRight_agrees (S : P.Split) :
    intoPullback P (right P S) ⋙ CategoricalPullback.π₂ _ _ ⋙ right P S = binaryRight P S := rfl

def chainPair (S : P.Split) {A : B} : Chain P 2 A → Binary P S
  | .cons p (.cons q (.nil _)) => pair P.grades _ (pair P.grades (𝟭 B) A p) q

def pairChain (S : P.Split) (x : Binary P S) : Σ A, Chain P 2 A :=
  ⟨grade _ _ (grade _ _ x),.cons (payload _ _ (grade _ _ x)) (.cons (payload _ _ x) (.nil _))⟩

def chainObjects (S : P.Split) : (Σ A, Chain P 2 A) ≃ Binary P S where
  toFun z := chainPair P S z.2
  invFun := pairChain P S
  left_inv := by
    rintro ⟨A,t⟩; cases t with
    | cons p t => cases t with
      | cons q t => cases t; rfl
  right_inv _ := rfl

theorem chainEndpoint (S : P.Split) {A : B} (t : Chain P 2 A) :
    (binaryRight P S).obj (chainPair P S t) = endpoint t := by
  cases t with
  | cons p t => cases t with
    | cons q t => cases t; rfl

/-- A square over a specified u is exactly a map of the binary apex over u. -/
def chainHoms (S : P.Split) {A D : B} (a : A ⟶ D) (t : Chain P 2 A) (z : Chain P 2 D) :
    Square a t z ≃ {f : chainPair P S t ⟶ chainPair P S z //
      HEq ((binaryLeft P S).map f) a} := by
  cases t with | cons p t =>
    cases t with | cons q t =>
      cases t
      cases z with | cons r z =>
        cases z with | cons s z =>
          cases z
          let X := chainPair P S (.cons p (.cons q (.nil _)))
          let Z := chainPair P S (.cons r (.cons s (.nil _)))
          exact {
            toFun := fun f => ⟨arrow (x := X) (y := Z) (arrow a f.1) f.2.1,HEq.rfl⟩
            invFun := fun ⟨g,h⟩ => by
              have hg : gradeMap (gradeMap g) = a := eq_of_heq h
              subst a
              exact ⟨payloadMap (gradeMap g),payloadMap g,PUnit.unit⟩
            left_inv := fun _ => rfl
            right_inv := fun ⟨g,h⟩ => by
              have hg : gradeMap (gradeMap g) = a := eq_of_heq h
              subst a; rfl }

theorem chainEndpoint_map (S : P.Split) {A D : B} (a : A ⟶ D) (t : Chain P 2 A) (z : Chain P 2 D)
    (f : Square a t z) :
    HEq ((binaryRight P S).map ((chainHoms P S a t z) f).1) (terminalMap f) := by
  cases t with | cons p t =>
    cases t with | cons q t =>
      cases t
      cases z with | cons r z =>
        cases z with | cons s z =>
          cases z; rfl

/-- Universal property allowing arbitrary matching natural isomorphisms and
compatible pairs of natural transformations, not equality of object counts. -/
noncomputable def coneEquivalence (X : Type*) [Category* X] :
    (X ⥤ Total P.grades e) ≌ CategoricalPullback.CatCommSqOver e (left P) X :=
  ((equivalence P e).congrRight).trans (CategoricalPullback.functorEquiv e (left P) X)

/-- A span with a concrete middle category and both actual functor legs. -/
structure TwoLegs (B : Type b) [Category.{w} B] where
  apex : Cat.{max w v,max b u}
  source : apex ⥤ B
  dest : apex ⥤ B

def primitive (S : P.Split) : TwoLegs.{b,w,u,v} B :=
  ⟨Cat.of (Apex P),left P,right P S⟩

def append (S : P.Split) (V : TwoLegs.{b,w,u,v} B) : TwoLegs.{b,w,u,v} B :=
  ⟨Cat.of (Total P.grades V.dest),gradeProjection ⋙ V.source,second P V.dest ⋙ right P S⟩

/-- Index zero means one primitive span; the empty string is not a primitive span. -/
def positivePowers (S : P.Split) : Nat → TwoLegs.{b,w,u,v} B
  | 0 => primitive P S
  | n+1 => append P S (positivePowers S n)

noncomputable def successorCone (S : P.Split) (n : Nat) (X : Type*) [Category* X] :
    (X ⥤ (positivePowers P S (n+1)).apex) ≌
      CategoricalPullback.CatCommSqOver (positivePowers P S n).dest (left P) X :=
  coneEquivalence P _ X


namespace Strict
variable {J : Type*} [Category* J] (d : J ⥤ B)
structure Match where
  fst : K
  snd : J
  glue : e.obj fst = d.obj snd

def ambient (x : Match e d) : CategoricalPullback e d :=
  ⟨x.fst,x.snd,eqToIso x.glue⟩

instance matchCategory : Category (Match e d) := InducedCategory.instCategory (F := ambient e d)
def inclusion : Match e d ⥤ CategoricalPullback e d := inducedFunctor (ambient e d)
def fst : Match e d ⥤ K := inclusion e d ⋙ CategoricalPullback.π₁ _ _
def snd : Match e d ⥤ J := inclusion e d ⋙ CategoricalPullback.π₂ _ _

set_option backward.isDefEq.respectTransparency false in
theorem commute : fst e d ⋙ e = snd e d ⋙ d := by
  fapply Functor.ext
  · intro x; exact x.glue
  · intro x y f
    have h := f.hom.w
    exact ((comp_eqToHom_iff y.glue _ _).mp h).trans (Category.assoc ..)

variable {X : Type*} [Category* X] (F : X ⥤ K) (G : X ⥤ J) (h : F ⋙ e = G ⋙ d)
def lift : X ⥤ Match e d where
  obj x := ⟨F.obj x,G.obj x,Functor.congr_obj h x⟩
  map {x y} f := ⟨⟨F.map f,G.map f,(comp_eqToHom_iff (Functor.congr_obj h y) _ _).mpr (by exact (Functor.congr_hom h f).trans (Category.assoc ..).symm)⟩⟩
  map_id x := InducedCategory.hom_ext (CategoricalPullback.hom_ext (F.map_id x) (G.map_id x))
  map_comp f g := InducedCategory.hom_ext (CategoricalPullback.hom_ext (F.map_comp f g) (G.map_comp f g))

theorem lift_fst : lift e d F G h ⋙ fst e d = F := rfl
theorem lift_snd : lift e d F G h ⋙ snd e d = G := rfl

private theorem match_ext {x y : Match e d} (l : x.fst = y.fst) (r : x.snd = y.snd) : x = y := by
  cases x; cases y; congr

set_option backward.isDefEq.respectTransparency false in
theorem uniq (V W : X ⥤ Match e d) (l : V ⋙ fst e d = W ⋙ fst e d) (r : V ⋙ snd e d = W ⋙ snd e d) :
    V = W := by
  fapply Functor.ext
  · intro x; exact match_ext e d (Functor.congr_obj l x) (Functor.congr_obj r x)
  · intro x y f
    apply InducedCategory.hom_ext
    apply CategoricalPullback.hom_ext
    · change (fst e d).map (V.map f) = (fst e d).map (eqToHom _ ≫ W.map f ≫ eqToHom _)
      simp only [Functor.map_comp,eqToHom_map]
      exact Functor.congr_hom l f
    · change (snd e d).map (V.map f) = (snd e d).map (eqToHom _ ≫ W.map f ≫ eqToHom _)
      simp only [Functor.map_comp,eqToHom_map]
      exact Functor.congr_hom r f

include h in
theorem universal : ∃! L : X ⥤ Match e d, L ⋙ fst e d = F ∧ L ⋙ snd e d = G :=
  ⟨lift e d F G h,⟨lift_fst e d F G h,lift_snd e d F G h⟩,fun V hv => uniq e d V _ (hv.1.trans (lift_fst e d F G h).symm) (hv.2.trans (lift_snd e d F G h).symm)⟩
end Strict

def strictFactor : Total P.grades e ⥤ Strict.Match e (left P) :=
  Strict.lift e (left P) gradeProjection (second P e) (matching P e)

theorem strict_inclusion : strictFactor P e ⋙ Strict.inclusion e (left P) = intoPullback P e := rfl
theorem strict_left : strictFactor P e ⋙ Strict.fst e (left P) = gradeProjection := rfl
theorem strict_right : strictFactor P e ⋙ Strict.snd e (left P) = second P e := rfl

instance strictFull : (strictFactor P e).Full where
  map_surjective h := ⟨fromMatched P e h.hom,InducedCategory.hom_ext (recover P e h.hom)⟩

instance strictFaithful : (strictFactor P e).Faithful where
  map_injective {_x _y} _f _g h := (intoPullback P e).map_injective (congrArg (fun m => (Strict.inclusion e (left P)).map m) h)

instance strictEssSurj : (strictFactor P e).EssSurj where
  mem_essImage z := ⟨normalize P e (Strict.ambient e (left P) z),⟨InducedCategory.isoMk (normalizeIso P e _)⟩⟩

instance strictIsEquivalence : (strictFactor P e).IsEquivalence where

noncomputable def strictEquivalence : Total P.grades e ≌ Strict.Match e (left P) :=
  (strictFactor P e).asEquivalence

end ContextualComposition.GrothendieckStep.SpanApex
