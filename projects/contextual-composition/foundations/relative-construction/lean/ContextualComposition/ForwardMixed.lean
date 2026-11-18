module
public import ContextualComposition.TaggedMixed
/-! The mixed comparison on the forward presentation of the single coproduct
span. The whole-span base and payload actions are defined by its own cleavage. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ForwardMixed
open CategoryTheory CategoryTheory.Functor Opposite CoproductSpan NativeCleavage TelescopeSquares
open TaggedMixed SpanPull
universe i b w k j u v
variable {I : Type i} {B : Type b} [Category.{w} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (C : ∀ t, Cleavage (p t)) {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
noncomputable abbrev whole {A D : B} (a : A ⟶ D) := Presented.square T (Sigma.desc d) (Sigma.desc p) (choice p C) a
noncomputable abbrev part {A D : B} (a : A ⟶ D) (t : I) := Presented.square T (d t) (p t) (C t) a
/-- Both strict-fibre comparison arrows factor the same image of the selected
lift through the chosen lift in the weighted whole span. -/
theorem strictCell {A D : B} (a : A ⟶ D) (t : I) (x : (partProj p d Y t).Fiber D) :
    (strictTag p d Z A t).map ((PayloadLift.square T (d t) (p t) (C t) a).hom.app x) =
      (PayloadLift.square T (Sigma.desc d) (Sigma.desc p) (choice p C) a).hom.app ((strictTag p d Y D t).obj x) := by
  let z := (PayloadLift.action T (d t) (p t) D).obj x
  apply Reindex.cancel (weightedChoice p d C Z) a (z := (strictTag p d Z D t).obj z)
  refine Eq.trans ?_ (PayloadLift.square_fac T _ _ (choice p C) a ((strictTag p d Y D t).obj x)).symm
  let H := totalTag d Z t
  let f := ((PayloadLift.square T (d t) (p t) (C t) a).hom.app x).val
  let g := Reindex.lift (partChoice p d C Z t) a z
  change H.map f ≫ H.map g = _
  exact (H.map_comp f g).symm.trans (congrArg H.map (PayloadLift.square_fac T (d t) (p t) (C t) a x))
theorem strip {L : Type*} [Category* L] (e q : L ⥤ B) (J : Cleavage q) {A D : B} (a : A ⟶ D)
    (x : Total Y (FibreTotal.endpoint e q D)) :
    Aligned ((Presented.square T e q J a).hom.app x)
      ((FibreTotal.out Z e q A).map ((PayloadLift.square T e q J a).hom.app ((FibreTotal.into Y e q D).obj x))) :=
  FinalCube.Align.stripPresent _ _ _ _ _ _ _ _ (PayloadLift.square T e q J a)
    (NativeCube.outSquare T e q A) (EvalPayload.intoSquare T e q D).symm x
-- Converting the strict inverse fibre presentations unfolds both total functors.
set_option maxHeartbeats 1000000 in
theorem presentedCell {A D : B} (a : A ⟶ D) (t : I) (x : Total Y (leg p d D t)) :
    Aligned ((presentedTag p d Z A t).map ((part p d C T a t).hom.app x))
      ((whole p d C T a).hom.app ((presentedTag p d Y D t).obj x)) := by
  let y := (FibreTotal.into Y (d t) (p t) D).obj x
  let O := FibreTotal.out Z (Sigma.desc d) (Sigma.desc p) A
  exact ((strip T (d t) (p t) (C t) a x).map (presentedTag p d Z A t)).trans
    ((NativeCube.ofEq (congrArg O.map (strictCell p d C T a t y))).trans
      (strip T (Sigma.desc d) (Sigma.desc p) (choice p C) a ((presentedTag p d Y D t).obj x)).symm)
theorem compareCell {A D : B} (a : A ⟶ D) (t : I) (x : Total Y (leg p d D t)) :
    Aligned ((compare p d A Z).map ((Sigma.incl t).map ((part p d C T a t).hom.app x)))
      ((whole p d C T a).hom.app ((compare p d D Y).obj ⟨t,x⟩)) :=
  (NativeCube.functorAlign (compareTag p d Z A t) ((part p d C T a t).hom.app x)).trans
    ((presentedCell p d C T a t x).trans
      (FinalCube.Align.atEq (whole p d C T a).hom (Functor.congr_obj (compareTag p d Y D t).symm x)))
/-- A comparison component is specifically an equality transport, not merely an isomorphism. -/
def IsTransport {H : Type*} [Category* H] {x y : H} (f : x ⟶ y) : Prop :=
  ∃ h : x = y, f = eqToHom h
namespace IsTransport
variable {H J : Type*} [Category* H] [Category* J]
theorem app {F G : H ⥤ J} (e : F = G) (x : H) : IsTransport ((eqToHom e).app x) :=
  ⟨_,eqToHom_app e x⟩
theorem map (F : H ⥤ J) {x y : H} {f : x ⟶ y} (h : IsTransport f) : IsTransport (F.map f) := by
  obtain ⟨rfl,rfl⟩ := h
  exact ⟨rfl,F.map_id _⟩
theorem comp {x y z : H} {f : x ⟶ y} {g : y ⟶ z} (h : IsTransport f) (j : IsTransport g) :
    IsTransport (f ≫ g) := by
  obtain ⟨rfl,rfl⟩ := h; obtain ⟨rfl,rfl⟩ := j; exact ⟨rfl,Category.id_comp _⟩
/-- Aligned mixed arrows can be compared across four particular endpoint
arrows only when each of those arrows is an equality transport. -/
theorem hexagon {a b c d e u : H} {f : a ⟶ b} {g : c ⟶ d}
    {t : b ⟶ e} {r : e ⟶ d} {l : a ⟶ u} {s : u ⟶ c} (h : Aligned f g)
    (ht : IsTransport t) (hr : IsTransport r) (hl : IsTransport l) (hs : IsTransport s) :
    (f ≫ t) ≫ r = l ≫ s ≫ g := by
  obtain ⟨rfl,rfl⟩ := ht; obtain ⟨rfl,rfl⟩ := hr
  obtain ⟨rfl,rfl⟩ := hl; obtain ⟨rfl,rfl⟩ := hs
  simpa using h.eq
end IsTransport
theorem forwardTransport (X : Bᵒᵖ ⥤ Cat.{v,u}) {A D : B} (a : A ⟶ D)
    (x : Σ t, Total X (leg p d D t)) : IsTransport ((forward p d C X a).inv.app x) := by
  rcases x with ⟨t,x⟩; exact ⟨_,PullLaws.forwardApp p d C X a t x⟩
/-- Equality, in the functor category, of the two pastes of an arrow-faced cube. -/
def Commuting {U V : FinalCube.Mix.Grid} (M : Cube.Map U V) : Prop :=
  (whiskerRight U.cell M.f' ≫ whiskerLeft U.q M.t) ≫ whiskerRight M.r V.b' =
    whiskerLeft U.b M.l ≫ whiskerRight M.s V.p ≫ whiskerLeft M.g V.cell
theorem commuting {U V : FinalCube.Mix.Grid} (M : Cube.Map U V) (h : Cube.Law M) : Commuting M :=
  (Cube.diagram_iff M).mp h
namespace All
open CoproductSpan.All SumChange
variable {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) {Y Z : Bᵒᵖ ⥤ Cat.{w,b}} (T : Y ⟶ Z)
noncomputable abbrev wholeGrid {A D : B} (a : A ⟶ D) :=
  Presented.grid T (Sigma.desc (dst R)) (Sigma.desc (src R)) (choice (src R) (SpanPull.All.parts R)) a
noncomputable def cube {A D : B} (a : A ⟶ D) :
    Cube.Map (TaggedMixed.All.taggedGrid R T a) (wholeGrid R T a) where
  f := compare (src R) (dst R) A Y
  g := compare (src R) (dst R) D Y
  f' := compare (src R) (dst R) A Z
  g' := compare (src R) (dst R) D Z
  s := (SpanPull.All.comparison R Y a).inv
  t := (SpanPull.All.comparison R Z a).inv
  l := (eqToIso (compare_payload (src R) (dst R) A Y T)).inv
  r := (eqToIso (compare_payload (src R) (dst R) D Y T)).inv
theorem comparisonTransport (X : Bᵒᵖ ⥤ Cat.{w,b}) {A D : B} (a : A ⟶ D)
    (x : Σ n, Total X (leg (src R) (dst R) D n)) : IsTransport ((SpanPull.All.comparison R X a).inv.app x) :=
  IsTransport.comp (IsTransport.app (congrArg (fun F => ZeroPower.Sum.map F ⋙ compare (src R) (dst R) A X)
    (SpanPull.All.pull_eq_leaf R X a)).symm x) (forwardTransport (src R) (dst R) (SpanPull.All.parts R) X a x)
set_option maxHeartbeats 1000000 in
theorem leafAligned {A D : B} (a : A ⟶ D) (n : Nat) (x : Total Y (leg (src R) (dst R) D n)) :
    Aligned ((TaggedMixed.All.leafSquare R T a n).hom.app x)
      ((part (src R) (dst R) (SpanPull.All.parts R) T a n).hom.app x) := by
  cases n with
  | zero => exact Aligned.refl _
  | succ n => exact Aligned.refl _
set_option maxHeartbeats 1000000 in
theorem alignedCell {A D : B} (a : A ⟶ D) (n : Nat) (x : Total Y (leg (src R) (dst R) D n)) :
    Aligned ((compare (src R) (dst R) A Z).map ((TaggedMixed.All.taggedSource R T a).hom.app ⟨n,x⟩))
      ((whole (src R) (dst R) (SpanPull.All.parts R) T a).hom.app ((compare (src R) (dst R) D Y).obj ⟨n,x⟩)) :=
  ((leafAligned R T a n x).map (Sigma.incl n ⋙ compare (src R) (dst R) A Z)).trans
    (compareCell (src R) (dst R) (SpanPull.All.parts R) T a n x)
set_option maxHeartbeats 1000000 in
theorem law {A D : B} (a : A ⟶ D) : Cube.Law (cube R T a) := by
  rintro ⟨n,x⟩
  exact IsTransport.hexagon (alignedCell R T a n x)
    (comparisonTransport R Z a _)
    (IsTransport.map (SpanPull.All.pull R Z a) (IsTransport.app (compare_payload (src R) (dst R) D Y T).symm ⟨n,x⟩))
    (IsTransport.app (compare_payload (src R) (dst R) A Y T).symm ((ZeroPower.Sum.map (leafPull R Y a)).obj ⟨n,x⟩))
    (IsTransport.map (ChainPayload.fibreMap T _) (comparisonTransport R Y a _))
/-- The two full natural-transformation pastes. The fields of M are exactly
the four comparisons specified in cube, including the length-family correction. -/
theorem diagram {A D : B} (a : A ⟶ D) : Commuting (cube R T a) :=
  commuting (cube R T a) (law R T a)
end All
end ContextualComposition.GrothendieckStep.ForwardMixed
