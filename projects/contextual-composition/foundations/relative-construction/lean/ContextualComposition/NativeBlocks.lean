module
public import ContextualComposition.SpanPull
public import Mathlib.CategoryTheory.IsoCat
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeBlocks
open CategoryTheory CategoryTheory.Limits Opposite SpanApex
universe b w
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,b,w} B} (S : P.Split)
abbrev power (n : Nat) := CoproductSpan.All.span S n
theorem succ_power (n : Nat) : power S (n+1) = SpanApex.append P S (power S n) := by
  cases n <;> rfl

section Last
variable {K : Type*} [Category* K] (e : K ⥤ B)
def unmatch (z : Strict.Match e (left P)) : Total P.grades e := by
  rcases z with ⟨k,⟨⟨⟨a⟩,⟨p⟩⟩⟩,h⟩
  change e.obj k = a at h
  subst a
  exact pair _ _ k p
theorem unmatch_cut (x : Total P.grades e) :
    unmatch e ((strictFactor P e).obj x) = x := by cases x; rfl
theorem cut_unmatch (z : Strict.Match e (left P)) :
    (strictFactor P e).obj (unmatch e z) = z := by
  rcases z with ⟨k,⟨⟨⟨a⟩,⟨p⟩⟩⟩,h⟩
  change e.obj k = a at h
  subst a; rfl
instance lastIso : (strictFactor P e).IsIso where
  bijective_obj := Function.bijective_iff_has_inverse.mpr
    ⟨unmatch e,unmatch_cut e,cut_unmatch e⟩

variable {X : Type*} [Category* X]
noncomputable def attachLast (F : X ⥤ K) (G : X ⥤ Apex P) (h : F ⋙ e = G ⋙ left P) :
    X ⥤ Total P.grades e :=
  Strict.lift e _ F G h ⋙ (strictFactor P e).strictInv
theorem attach_cut (F : X ⥤ K) (G : X ⥤ Apex P) (h : F ⋙ e = G ⋙ left P) :
    attachLast e F G h ⋙ strictFactor P e = Strict.lift e _ F G h := by
  change Strict.lift e _ F G h ⋙ ((strictFactor P e).asIsomorphism.inverse ⋙ (strictFactor P e).asIsomorphism.functor) = _
  rw [IsoCat.counit_eq,Functor.comp_id]
theorem attach_prefix (F : X ⥤ K) (G : X ⥤ Apex P) (h : F ⋙ e = G ⋙ left P) :
    attachLast e F G h ⋙ gradeProjection = F :=
  congrArg (· ⋙ Strict.fst e _) (attach_cut e F G h)
theorem attach_last (F : X ⥤ K) (G : X ⥤ Apex P) (h : F ⋙ e = G ⋙ left P) :
    attachLast e F G h ⋙ second P e = G :=
  congrArg (· ⋙ Strict.snd e _) (attach_cut e F G h)
theorem last_ext {F G : X ⥤ Total P.grades e} (h : F ⋙ gradeProjection = G ⋙ gradeProjection)
    (k : F ⋙ second P e = G ⋙ second P e) : F = G :=
  (strictFactor P e).asIsomorphism.comp_functor_injective
    (Strict.uniq e _ _ _ h k)
end Last

abbrev Span := TwoLegs.{b,w,b,w} B
/-- Cut of a native sequence into a prefix and suffix. The lift is universal
for strictly matching diagrams on arbitrary parameter categories of the apex size. -/
structure Cut (M N D : Span (B := B)) where
  first : D.apex ⥤ M.apex
  rest : D.apex ⥤ N.apex
  glue : first ⋙ M.dest = rest ⋙ N.source
  source : first ⋙ M.source = D.source
  dest : rest ⋙ N.dest = D.dest
  assemble {X : Type b} [Category.{w} X] (F : X ⥤ M.apex) (G : X ⥤ N.apex)
    (h : F ⋙ M.dest = G ⋙ N.source) : X ⥤ D.apex
  first_assemble {X : Type b} [Category.{w} X] (F : X ⥤ M.apex) (G : X ⥤ N.apex)
    (h : F ⋙ M.dest = G ⋙ N.source) : assemble F G h ⋙ first = F
  rest_assemble {X : Type b} [Category.{w} X] (F : X ⥤ M.apex) (G : X ⥤ N.apex)
    (h : F ⋙ M.dest = G ⋙ N.source) : assemble F G h ⋙ rest = G
  ext {X : Type b} [Category.{w} X] {U V : X ⥤ D.apex}
    (l : U ⋙ first = V ⋙ first) (r : U ⋙ rest = V ⋙ rest) : U = V

variable (M : Span (B := B))
def emptyCut : Cut M (power S 0) M where
  first := 𝟭 _
  rest := M.dest
  glue := rfl
  source := rfl
  dest := rfl
  assemble F _ _ := F
  first_assemble _ _ _ := rfl
  rest_assemble _ _ h := h
  ext l _ := l

namespace Cut
variable {M N D : Span (B := B)} (c : Cut M N D)
abbrev pre (W : Span (B := B)) : (SpanApex.append P S W).apex ⥤ W.apex := gradeProjection
abbrev finalGrade (W : Span (B := B)) : (SpanApex.append P S W).apex ⥤ Apex P := second P W.dest
noncomputable def nextRest : (SpanApex.append P S D).apex ⥤ (SpanApex.append P S N).apex :=
  attachLast N.dest (pre S D ⋙ c.rest) (finalGrade S D) (congrArg (pre S D ⋙ ·) c.dest)
theorem nextRest_pre : nextRest S c ⋙ pre S N = pre S D ⋙ c.rest :=
  attach_prefix _ _ _ _
theorem nextRest_grade : nextRest S c ⋙ finalGrade S N = finalGrade S D :=
  attach_last _ _ _ _
variable {X : Type b} [Category.{w} X]
variable (F : X ⥤ M.apex) (G : X ⥤ (SpanApex.append P S N).apex)
variable (h : F ⋙ M.dest = G ⋙ (SpanApex.append P S N).source)
noncomputable def nextAssemble : X ⥤ (SpanApex.append P S D).apex :=
  attachLast D.dest (c.assemble F (G ⋙ pre S N) h) (G ⋙ finalGrade S N) (by
    calc
      _ = (c.assemble F (G ⋙ pre S N) h ⋙ c.rest) ⋙ N.dest := congrArg (c.assemble F (G ⋙ pre S N) h ⋙ ·) c.dest.symm
      _ = _ := congrArg (· ⋙ N.dest) (c.rest_assemble F (G ⋙ pre S N) h))
theorem nextAssemble_pre : nextAssemble S c F G h ⋙ pre S D = c.assemble F (G ⋙ pre S N) h :=
  attach_prefix _ _ _ _
theorem nextAssemble_grade : nextAssemble S c F G h ⋙ finalGrade S D = G ⋙ finalGrade S N :=
  attach_last _ _ _ _

noncomputable def snoc : Cut M (SpanApex.append P S N) (SpanApex.append P S D) where
  first := pre S D ⋙ c.first
  rest := nextRest S c
  glue := (congrArg (pre S D ⋙ ·) c.glue).trans (congrArg (· ⋙ N.source) (nextRest_pre S c).symm)
  source := congrArg (pre S D ⋙ ·) c.source
  dest := congrArg (· ⋙ right P S) (nextRest_grade S c)
  assemble := nextAssemble S c
  first_assemble F G h := (congrArg (· ⋙ c.first) (nextAssemble_pre S c F G h)).trans (c.first_assemble ..)
  rest_assemble F G h := last_ext N.dest (by
    calc
      _ = (nextAssemble S c F G h ⋙ pre S D) ⋙ c.rest := congrArg (nextAssemble S c F G h ⋙ ·) (nextRest_pre S c)
      _ = _ := (congrArg (· ⋙ c.rest) (nextAssemble_pre S c F G h)).trans (c.rest_assemble ..))
    ((congrArg (nextAssemble S c F G h ⋙ ·) (nextRest_grade S c)).trans (nextAssemble_grade S c F G h))
  ext {X _ U V} l r := last_ext D.dest (c.ext l (by
    calc
      _ = (U ⋙ nextRest S c) ⋙ pre S N := congrArg (U ⋙ ·) (nextRest_pre S c).symm
      _ = _ := (congrArg (· ⋙ pre S N) r).trans (congrArg (V ⋙ ·) (nextRest_pre S c))))
    (by
      calc
        _ = (U ⋙ nextRest S c) ⋙ finalGrade S N := congrArg (U ⋙ ·) (nextRest_grade S c).symm
        _ = _ := (congrArg (· ⋙ finalGrade S N) r).trans (congrArg (V ⋙ ·) (nextRest_grade S c)))
end Cut

/-- The cut is on the prior native apices, not on replacement lists. -/
noncomputable def blocks (m : Nat) : (n : Nat) → Cut (power S m) (power S n) (power S (m+n))
  | 0 => emptyCut S _
  | n+1 => by
    rw [show m+(n+1) = (m+n)+1 from rfl,succ_power S (m+n),succ_power S n]
    exact (blocks m n).snoc S
namespace Cut
variable {M N D : Span (B := B)} (c : Cut M N D)
abbrev matching := Strict.Match M.dest N.source
def cutFunctor : D.apex ⥤ matching (M := M) (N := N) := Strict.lift _ _ c.first c.rest c.glue
noncomputable def joinFunctor : matching (M := M) (N := N) ⥤ D.apex :=
  c.assemble (Strict.fst _ _) (Strict.snd _ _) (Strict.commute _ _)
theorem join_first : c.joinFunctor ⋙ c.first = Strict.fst _ _ := c.first_assemble .. 
theorem join_rest : c.joinFunctor ⋙ c.rest = Strict.snd _ _ := c.rest_assemble ..
noncomputable def strictIso : IsoCat D.apex (matching (M := M) (N := N)) where
  functor := c.cutFunctor
  inverse := c.joinFunctor
  unit_eq := c.ext (congrArg (c.cutFunctor ⋙ ·) c.join_first.symm) (congrArg (c.cutFunctor ⋙ ·) c.join_rest.symm)
  counit_eq := Strict.uniq _ _ _ _ c.join_first c.join_rest
theorem join_source : c.joinFunctor ⋙ D.source = Strict.fst M.dest N.source ⋙ M.source :=
  (congrArg (c.joinFunctor ⋙ ·) c.source.symm).trans (congrArg (· ⋙ M.source) c.join_first)
theorem join_dest : c.joinFunctor ⋙ D.dest = Strict.snd M.dest N.source ⋙ N.dest :=
  (congrArg (c.joinFunctor ⋙ ·) c.dest.symm).trans (congrArg (· ⋙ N.dest) c.join_rest)
end Cut

section IsoGlue
variable {K J : Type*} [Category* K] [Category* J] (e : K ⥤ B) (p : J ⥤ B)
variable (C : NativeCleavage.Cleavage p)
include C in
/-- A matching isomorphism can be absorbed by a cartesian lift of the second block.
This is not an assertion that the matching isomorphism must be an identity. -/
theorem inclusionEquivalence : (Strict.inclusion e p).IsEquivalence := by
  let : (Strict.inclusion e p).Full := (fullyFaithfulInducedFunctor _).full
  let : (Strict.inclusion e p).Faithful := (fullyFaithfulInducedFunctor _).faithful
  refine { essSurj := ⟨fun z => ?_⟩ }
  let d := C (e.obj z.fst) z.snd z.iso.hom
  let := NativeCleavage.chosenStrong d
  let : IsIso d.lift := Functor.IsStronglyCartesian.isIso_of_base_isIso p z.iso.hom d.lift
  let i : d.obj ≅ z.snd := asIso d.lift
  refine ⟨⟨z.fst,d.obj,d.source.symm⟩,⟨CategoricalPullback.mkIso (Iso.refl z.fst) i ?_⟩⟩
  change e.map (𝟙 _) ≫ z.iso.hom = eqToHom d.source.symm ≫ p.map d.lift
  rw [d.over,e.map_id,Category.id_comp,← Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]
end IsoGlue

/-- Fixed-length equipment composite, allowing arbitrary boundary isomorphisms. -/
noncomputable def equipment (m n : Nat) :
    (power S (m+n)).apex ≌ CategoricalPullback (power S m).dest (power S n).source := by
  let C : NativeCleavage.Cleavage (power S n).source := by
    cases n with
    | zero => exact NativeCleavage.baseChoice
    | succ j => exact NativeCleavage.powerChoice S j
  let := inclusionEquivalence (power S m).dest (power S n).source C
  exact (blocks S m n).strictIso.toEquivalence.trans (Strict.inclusion _ _).asEquivalence
section Tags
abbrev tel := Σ n, (power S n).apex
abbrev leftLeg : tel S ⥤ B := Sigma.desc (fun n => (power S n).source)
abbrev rightLeg : tel S ⥤ B := Sigma.desc (fun n => (power S n).dest)
abbrev pairs := Strict.Match (rightLeg S) (leftLeg S)
abbrev part (i : Nat × Nat) := Strict.Match (power S i.1).dest (power S i.2).source
abbrev parts := Σ i, part S i
def splitObj (x : pairs S) : parts S :=
  ⟨(x.fst.1,x.snd.1),x.fst.2,x.snd.2,x.glue⟩
def splitMap {x y : pairs S} (f : x ⟶ y) : splitObj S x ⟶ splitObj S y := by
  rcases x with ⟨⟨m,x₁⟩,⟨n,y₁⟩,hx⟩; rcases y with ⟨⟨m',x'⟩,⟨n',y'⟩,hy⟩
  rcases f with ⟨⟨a,b,h⟩⟩
  cases a with | mk a =>
    cases b with | mk b =>
      exact Sigma.SigmaHom.mk ⟨⟨a,b,h⟩⟩
def splitPairs : pairs S ⥤ parts S where
  obj := splitObj S
  map := splitMap S
  map_id := by rintro ⟨⟨m,x⟩,⟨n,y⟩,h⟩; rfl
  map_comp := by
    rintro ⟨⟨m,x⟩,⟨n,y⟩,h⟩ ⟨⟨m',x'⟩,⟨n',y'⟩,h'⟩ ⟨⟨m'',x''⟩,⟨n'',y''⟩,h''⟩ ⟨⟨a,b,_⟩⟩ ⟨⟨c,d,_⟩⟩
    cases a; cases b; cases c; cases d; rfl
abbrev incl (n : Nat) : (power S n).apex ⥤ tel S := Sigma.incl (C := fun j => (power S j).apex) n
def tagPair (i : Nat × Nat) : part S i ⥤ pairs S :=
  Strict.lift _ _ (Strict.fst _ _ ⋙ incl S i.1) (Strict.snd _ _ ⋙ incl S i.2) (Strict.commute (power S i.1).dest (power S i.2).source)
def gatherPairs : parts S ⥤ pairs S := Sigma.desc (tagPair S)
theorem tag_split (i : Nat × Nat) : tagPair S i ⋙ splitPairs S = Sigma.incl i := rfl
theorem split_gather : splitPairs S ⋙ gatherPairs S = 𝟭 _ := by
  apply Strict.uniq _ _
  all_goals
    fapply Functor.ext
    · rintro ⟨⟨m,x⟩,⟨n,y⟩,h⟩; rfl
    · rintro ⟨⟨m,x⟩,⟨n,y⟩,h⟩ ⟨⟨m',x'⟩,⟨n',y'⟩,h'⟩ ⟨⟨a,b,k⟩⟩
      cases a; cases b; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; rw [Category.id_comp]; exact (Category.comp_id _).symm
theorem gather_split : gatherPairs S ⋙ splitPairs S = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨⟨m,n⟩,x⟩; rfl
  · rintro ⟨⟨m,n⟩,x⟩ ⟨_,y⟩ ⟨f⟩; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; rw [Category.id_comp]; exact (Category.comp_id _).symm
noncomputable def binary : pairs S ⥤ tel S := splitPairs S ⋙
  Sigma.desc fun i => (blocks S i.1 i.2).joinFunctor ⋙ incl S (i.1+i.2)
theorem binary_at (m n : Nat) :
    tagPair S (m,n) ⋙ binary S = (blocks S m n).joinFunctor ⋙ incl S (m+n) := rfl
theorem binary_source : binary S ⋙ leftLeg S = Strict.fst _ _ ⋙ leftLeg S := by
  have H : gatherPairs S ⋙ (binary S ⋙ leftLeg S) = gatherPairs S ⋙ (Strict.fst _ _ ⋙ leftLeg S) := by
    fapply Functor.ext
    · rintro ⟨⟨m,n⟩,x⟩; exact Functor.congr_obj (blocks S m n).join_source x
    · rintro ⟨⟨m,n⟩,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (blocks S m n).join_source f
  exact (show IsoCat (parts S) (pairs S) from ⟨gatherPairs S,splitPairs S,(gather_split S).symm,split_gather S⟩).functor_comp_injective H
theorem binary_dest : binary S ⋙ rightLeg S = Strict.snd _ _ ⋙ rightLeg S := by
  apply (show IsoCat (parts S) (pairs S) from ⟨gatherPairs S,splitPairs S,(gather_split S).symm,split_gather S⟩).functor_comp_injective
  fapply Functor.ext
  · rintro ⟨⟨m,n⟩,x⟩; exact Functor.congr_obj (blocks S m n).join_dest x
  · rintro ⟨⟨m,n⟩,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (blocks S m n).join_dest f
theorem rejoin (m n : Nat) :
    (blocks S m n).cutFunctor ⋙ tagPair S (m,n) ⋙ binary S = incl S (m+n) := by
  exact congrArg (· ⋙ incl S (m+n)) (blocks S m n).strictIso.unit_eq.symm
end Tags


namespace Nested
universe u v
-- A common size closed under the category-of-tags construction.
variable {C : Type u} [Category.{max u v} C] {Q : Endpoints.{u,max u v,u,max u v} C} (R : Q.Split)
abbrev whole : Span (B := C) := ⟨Cat.of (tel R),leftLeg R,rightLeg R⟩
def product (U V : Span (B := C)) : Span (B := C) :=
  ⟨Cat.of (Strict.Match U.dest V.source),Strict.fst _ _ ⋙ U.source,Strict.snd _ _ ⋙ V.dest⟩
/-- A word of blocks; each block is an object of the actual tagged native span.
The first block is left untouched, not normalized by an auxiliary identity case. -/
def word : Nat → Span (B := C)
  | 0 => power R 0
  | 1 => whole R
  | n+2 => product (word (n+1)) (whole R)
noncomputable def wordEquipment (n : Nat) : (word R (n+2)).apex ≌
    CategoricalPullback (word R (n+1)).dest (leftLeg R) := by
  let F := Strict.inclusion (word R (n+1)).dest (leftLeg R)
  let : F.IsEquivalence := inclusionEquivalence _ _ (SpanPull.choice _ (SpanPull.All.parts R))
  exact F.asEquivalence
structure Over (U V : Span (B := C)) where
  functor : U.apex ⥤ V.apex
  source : functor ⋙ V.source = U.source
  dest : functor ⋙ V.dest = U.dest

noncomputable def extend {U : Span (B := C)} (F : Over U (whole R)) :
    Over (product U (whole R)) (whole R) := by
  let L := Strict.fst U.dest (leftLeg R)
  let G := Strict.snd U.dest (leftLeg R)
  have h : (L ⋙ F.functor) ⋙ rightLeg R = G ⋙ leftLeg R :=
    (congrArg (L ⋙ ·) F.dest).trans (Strict.commute _ _)
  let H := Strict.lift _ _ (L ⋙ F.functor) G h
  exact ⟨H ⋙ binary R,(congrArg (H ⋙ ·) (binary_source R)).trans (congrArg (L ⋙ ·) F.source),
    congrArg (H ⋙ ·) (binary_dest R)⟩
noncomputable def collapse : (k : Nat) → Over (word R k) (whole R)
  | 0 => ⟨incl R 0,rfl,rfl⟩
  | 1 => ⟨𝟭 _,rfl,rfl⟩
  | k+2 => extend R (collapse (k+1))
abbrev strings := Σ k, (word R k).apex
abbrev outer (k : Nat) : (word R k).apex ⥤ strings R := Sigma.incl (C := fun n => (word R n).apex) k
noncomputable def flatten : strings R ⥤ tel R := Sigma.desc fun k => (collapse R k).functor
theorem flatten_at (k : Nat) : outer R k ⋙ flatten R = (collapse R k).functor := rfl
theorem flatten_empty : outer R 0 ⋙ flatten R = incl R 0 := rfl
theorem flatten_single : outer R 1 ⋙ flatten R = 𝟭 (tel R) := rfl
theorem flatten_source : flatten R ⋙ leftLeg R = Sigma.desc (fun k => (word R k).source) := by
  fapply Functor.ext
  · rintro ⟨k,x⟩; exact Functor.congr_obj (collapse R k).source x
  · rintro ⟨k,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (collapse R k).source f
theorem flatten_dest : flatten R ⋙ rightLeg R = Sigma.desc (fun k => (word R k).dest) := by
  fapply Functor.ext
  · rintro ⟨k,x⟩; exact Functor.congr_obj (collapse R k).dest x
  · rintro ⟨k,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (collapse R k).dest f
def count : (k : Nat) → (word R k).apex → Nat
  | 0,_ => 0
  | 1,x => x.1
  | k+2,x => count (k+1) x.fst + x.snd.1
theorem flatten_length : (k : Nat) → (x : (word R k).apex) →
    ((flatten R).obj ((outer R k).obj x)).1 = count R k x
  | 0,_ => rfl
  | 1,_ => rfl
  | k+2,x => congrArg (· + x.snd.1) (flatten_length (k+1) x.fst)
theorem flatten_two : outer R 2 ⋙ flatten R = binary R := by
  let H := Strict.lift (rightLeg R) (leftLeg R) (Strict.fst _ _ ⋙ 𝟭 _) (Strict.snd _ _) (Strict.commute _ _)
  exact congrArg (· ⋙ binary R) (Strict.uniq _ _ H (𝟭 _) rfl rfl)

/-- Replace each primitive grade by its actual length-one block, retaining all
native squares. The two endpoints agree strictly at each length. -/
noncomputable def singletonBlocks : (n : Nat) → Over (power R n) (word R n)
  | 0 => ⟨𝟭 _,rfl,rfl⟩
  | 1 => ⟨incl R 1,rfl,rfl⟩
  | k+2 => by
    let c := blocks R (k+1) 1
    let a := singletonBlocks (k+1)
    let H := Strict.lift (word R (k+1)).dest (leftLeg R) (c.first ⋙ a.functor) (c.rest ⋙ incl R 1)
      ((congrArg (c.first ⋙ ·) a.dest).trans c.glue)
    exact ⟨H,(congrArg (c.first ⋙ ·) a.source).trans c.source,c.dest⟩
set_option maxHeartbeats 1600000 in
theorem collapse_singletons : (n : Nat) →
    (singletonBlocks R n).functor ⋙ (collapse R n).functor = incl R n
  | 0 => rfl
  | 1 => rfl
  | k+2 => by
    let c := blocks R (k+1) 1
    let a := singletonBlocks R (k+1)
    let f := collapse R (k+1)
    let K := Strict.lift (word R (k+1)).dest (leftLeg R) (c.first ⋙ a.functor) (c.rest ⋙ incl R 1)
      ((congrArg (c.first ⋙ ·) a.dest).trans c.glue)
    let L := Strict.fst (word R (k+1)).dest (leftLeg R)
    let G := Strict.snd (word R (k+1)).dest (leftLeg R)
    let H := Strict.lift (rightLeg R) (leftLeg R) (L ⋙ f.functor) G
      ((congrArg (L ⋙ ·) f.dest).trans (Strict.commute _ _))
    have h : K ⋙ H = c.cutFunctor ⋙ tagPair R (k+1,1) :=
      Strict.uniq _ _ _ _ (congrArg (c.first ⋙ ·) (collapse_singletons (k+1))) rfl
    exact (congrArg (· ⋙ binary R) h).trans (rejoin R (k+1) 1)
noncomputable def singletons : tel R ⥤ strings R :=
  Sigma.desc fun n => (singletonBlocks R n).functor ⋙ outer R n
theorem singletons_flatten : singletons R ⋙ flatten R = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (collapse_singletons R n) x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (collapse_singletons R n) f
end Nested
end ContextualComposition.GrothendieckStep.NativeBlocks
