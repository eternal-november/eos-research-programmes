module
public import ContextualComposition.BlockUnits
/-! The two distinct unit diagrams overlap precisely on length zero. Here the
units on that overlap agree as natural transformations, including on arbitrary
arrows of the zero-length weighted fibre. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.EmptyUnitOverlap
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockUnits
set_option backward.isDefEq.respectTransparency false
universe b w u v
section Packed
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split) (Y : Psh.{b,w,u,v} B) (A : B)
theorem endpoints {x : BlockUnits.value S Y A} :
    (insert S Y A .left).obj x = (insert S Y A .right).obj x ↔ x.1 = 0 := by
  constructor
  · intro h; exact wrongSide S Y A (eqToHom h)
  · intro h
    apply obj_ext S Y A
    · rw [insertShape,insertShape,h]; rfl
    · exact (Functor.congr_obj (erase S Y A .left) x).trans (Functor.congr_obj (erase S Y A .right) x).symm
theorem functor_ext {X C D : Type*} [Category* X] [Category* C] [Category* D] (M : C ⥤ D) [M.Faithful]
    {F G : X ⥤ C} (p : ∀ x, F.obj x = G.obj x) (k : F ⋙ M = G ⋙ M) : F = G := by
  fapply Functor.ext
  · exact p
  · intro x y f; apply M.map_injective
    simp only [Functor.map_comp,eqToHom_map]
    exact Functor.congr_hom k f
theorem endpointDiagrams {X : Type*} [Category* X] (F : X ⥤ BlockUnits.value S Y A) :
    F ⋙ insert S Y A .left = F ⋙ insert S Y A .right ↔ ∀ x, (F.obj x).1 = 0 := by
  constructor
  · intro h x; exact (endpoints S Y A).mp (Functor.congr_obj h x)
  · intro h
    let _ := BlockCartesian.faithful _ (joinIncoming S Y A)
    exact functor_ext (mu S Y A) (fun x => (endpoints S Y A).mpr (h x))
      (congrArg (F ⋙ ·) ((erase S Y A .left).trans (erase S Y A .right).symm))
end Packed
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : Psh.{u,max u v,u,v} B) (A : B)
abbrev empty := Lift.weighted (inclPower S 0) Y A
theorem degenerate : empty S Y A ⋙ J S Y A .left = empty S Y A ⋙ J S Y A .right := by
  let I := inclPower S 0
  exact (Lift.weighted_comp I Y A (degeneracy S .left)).trans
    ((Lift.weighted_eq _ Y A (G := Lift.comp I (degeneracy S .right))
       (Strict.uniq _ _ _ _ rfl rfl)).trans (Lift.weighted_comp I Y A (degeneracy S .right)).symm)
set_option maxHeartbeats 1200000 in
theorem atZero : empty S Y A ⋙ target S Y A .left = empty S Y A ⋙ target S Y A .right :=
  (endpointDiagrams S Y A (empty S Y A ⋙ evaluation S Y A)).mpr
    (fun x => (evaluationLength S Y A _).trans (key Y A (inclPower S 0) (fun w => w.1) x))
def aligned {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {x y : C}
    (e : x = y) {a b : D} (d : a = b) (l : F.obj x ⟶ a) (r : F.obj y ⟶ b) : Prop :=
  eqToHom (congrArg F.obj e) ≫ r = l ≫ eqToHom d
theorem slide {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (M : D ⥤ E) [M.Faithful]
    (G : C ⥤ E) (c : F ⋙ M ⟶ G) {x y : C} (e : x = y) {a b : D} (d : a = b)
    (l : F.obj x ⟶ a) (r : F.obj y ⟶ b) (p : G.obj x = M.obj a) (q : G.obj y = M.obj b)
    (k : M.map l = c.app x ≫ eqToHom p) (j : M.map r = c.app y ≫ eqToHom q) :
    eqToHom (congrArg F.obj e) ≫ r = l ≫ eqToHom d := by
  subst y; subst b
  simpa using (M.map_injective (k.trans j.symm)).symm
theorem nativePoint (x : Lift.value Y A (power S 0)) :
    (J S Y A .left).obj ((empty S Y A).obj x) = (J S Y A .right).obj ((empty S Y A).obj x) :=
  Functor.congr_obj (degenerate S Y A) x
theorem packedPoint (x : Lift.value Y A (power S 0)) :
    (target S Y A .left).obj ((empty S Y A).obj x) = (target S Y A .right).obj ((empty S Y A).obj x) :=
  Functor.congr_obj (atZero S Y A) x
noncomputable def unitAt (s : Side) (z : single S Y A) :
    (CutCompositor.stages S Y A).obj ((J S Y A s).obj z) ⟶ (target S Y A s).obj z :=
  (stagedUnit S Y A s).hom.app z
theorem sends (s : Side) (z : single S Y A) :
    (mu S Y A).map (unitAt S Y A s z) =
      (BlockCompositor.multiplicationSquare S Y A).hom.app ((J S Y A s).obj z) ≫
      eqToHom (Functor.congr_obj ((nativeContract S Y A s).trans (targetErase S Y A s).symm) z) :=
  (NatTrans.congr_app (stagedTriangle S Y A s) z).trans
    (congrArg ((BlockCompositor.multiplicationSquare S Y A).hom.app ((J S Y A s).obj z) ≫ ·)
      (eqToHom_app ((nativeContract S Y A s).trans (targetErase S Y A s).symm) z))
section CommonFace
variable {X C D E : Type*} [Category* X] [Category* C] [Category* D] [Category* E]
variable (J : Side → X ⥤ C) (F : C ⥤ D) (T : Side → X ⥤ D)
variable (U : (s : Side) → (z : X) → F.obj ((J s).obj z) ⟶ (T s).obj z)
def agreesAt (z : X) (e : (J .left).obj z = (J .right).obj z) (d : (T .left).obj z = (T .right).obj z) : Prop :=
  aligned F e d (U .left z) (U .right z)
theorem glue (M : D ⥤ E) [M.Faithful] (G : C ⥤ E) (c : F ⋙ M ⟶ G)
    (p : (s : Side) → (z : X) → G.obj ((J s).obj z) = M.obj ((T s).obj z))
    (q : ∀ s z, M.map (U s z) = c.app ((J s).obj z) ≫ eqToHom (p s z))
    (z : X) (e : (J .left).obj z = (J .right).obj z) (d : (T .left).obj z = (T .right).obj z) :
    agreesAt J F T U z e d :=
  slide F M G c e d _ _ _ _ (q .left z) (q .right z)
end CommonFace
/-- Componentwise equality of the restricted natural transformations. The two
transports are induced by equal functors on the entire empty-weighted category. -/
theorem overlap (x : Lift.value Y A (power S 0)) :
    agreesAt (J S Y A) (CutCompositor.stages S Y A) (target S Y A) (unitAt S Y A)
      ((empty S Y A).obj x) (nativePoint S Y A x) (packedPoint S Y A x) := by
  let M := mu S Y A
  let _ : M.Faithful := BlockCartesian.faithful _ (joinIncoming S Y A)
  exact glue (J S Y A) (CutCompositor.stages S Y A) (target S Y A) (unitAt S Y A)
    M (CutCompositor.native S Y A) (BlockCompositor.multiplicationSquare S Y A).hom
    (fun s z => Functor.congr_obj ((nativeContract S Y A s).trans (targetErase S Y A s).symm) z)
    (sends S Y A) _ _ _
end ContextualComposition.GrothendieckStep.EmptyUnitOverlap
