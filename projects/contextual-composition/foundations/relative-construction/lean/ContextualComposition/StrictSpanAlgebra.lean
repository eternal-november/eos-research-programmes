module
public import ContextualComposition.NativeAssoc
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictSpanAlgebra
open CategoryTheory NativeBlocks SpanApex
open NativeBlocks.Nested (Over product)
open NativeCleavage
universe b w x v
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{max b w} B]

abbrev I : Span (B := B) := ⟨Cat.of B,𝟭 B,𝟭 B⟩
abbrev Pair (U V : Span (B := B)) := product U V

def id (U : Span (B := B)) : Over U U := ⟨𝟭 _,rfl,rfl⟩
def comp {U V W : Span (B := B)} (F : Over U V) (G : Over V W) : Over U W :=
  ⟨F.functor ⋙ G.functor,(congrArg (F.functor ⋙ ·) G.source).trans F.source,
    (congrArg (F.functor ⋙ ·) G.dest).trans F.dest⟩
theorem overExt {U V : Span (B := B)} {F G : Over U V} (h : F.functor = G.functor) : F = G := by
  cases F; cases G; cases h; rfl

variable {X : Type x} [Category.{v} X] {U V W T : Span (B := B)}

def combine (F : X ⥤ U.apex) (G : X ⥤ V.apex) (e : F ⋙ U.dest = G ⋙ V.source) :
    X ⥤ (Pair U V).apex := Strict.lift _ _ F G e

theorem before {Y : Type*} [Category* Y] (J : Y ⥤ X) (F : X ⥤ U.apex) (G : X ⥤ V.apex)
    (e : F ⋙ U.dest = G ⋙ V.source) :
    J ⋙ combine F G e = combine (J ⋙ F) (J ⋙ G) (congrArg (J ⋙ ·) e) :=
  Strict.uniq _ _ _ _ rfl rfl

theorem combineEq {F F' : X ⥤ U.apex} {G G' : X ⥤ V.apex}
    {e : F ⋙ U.dest = G ⋙ V.source} {e' : F' ⋙ U.dest = G' ⋙ V.source}
    (h : F = F') (k : G = G') : combine F G e = combine F' G' e' := by subst F'; subst G'; rfl

def both (F : Over U W) (G : Over V T) : Over (Pair U V) (Pair W T) where
  functor := combine (Strict.fst _ _ ⋙ F.functor) (Strict.snd _ _ ⋙ G.functor)
    ((congrArg (Strict.fst _ _ ⋙ ·) F.dest).trans
      ((Strict.commute _ _).trans (congrArg (Strict.snd _ _ ⋙ ·) G.source.symm)))
  source := congrArg (Strict.fst _ _ ⋙ ·) F.source
  dest := congrArg (Strict.snd _ _ ⋙ ·) G.dest

theorem combine_both (F : Over U W) (G : Over V T) (p : X ⥤ U.apex) (q : X ⥤ V.apex)
    (e : p ⋙ U.dest = q ⋙ V.source) :
    combine p q e ⋙ (both F G).functor =
      combine (p ⋙ F.functor) (q ⋙ G.functor)
        ((congrArg (p ⋙ ·) F.dest).trans (e.trans (congrArg (q ⋙ ·) G.source.symm))) :=
  Strict.uniq _ _ _ _ rfl rfl

/-- The ordinary category of diagrams reads the native unit and binary
operation with equality over both feet, not an invertible colaxator. -/
structure Ops (U : Span (B := B)) where
  unit : Over I U
  tensor : Over (Pair U U) U

variable (M : Ops U)
abbrev one (F : X ⥤ B) : X ⥤ U.apex := F ⋙ M.unit.functor
abbrev join (F G : X ⥤ U.apex) (e : F ⋙ U.dest = G ⋙ U.source) :=
  combine F G e ⋙ M.tensor.functor
theorem one_src (F : X ⥤ B) : one M F ⋙ U.source = F :=
  (congrArg (F ⋙ ·) M.unit.source).trans (Functor.comp_id _)
theorem one_dst (F : X ⥤ B) : one M F ⋙ U.dest = F :=
  (congrArg (F ⋙ ·) M.unit.dest).trans (Functor.comp_id _)
theorem join_src (F G : X ⥤ U.apex) (e : F ⋙ U.dest = G ⋙ U.source) :
    join M F G e ⋙ U.source = F ⋙ U.source := congrArg (combine F G e ⋙ ·) M.tensor.source
theorem join_dst (F G : X ⥤ U.apex) (e : F ⋙ U.dest = G ⋙ U.source) :
    join M F G e ⋙ U.dest = G ⋙ U.dest := congrArg (combine F G e ⋙ ·) M.tensor.dest
theorem joinEq {F F' G G' : X ⥤ U.apex} {e : F ⋙ U.dest = G ⋙ U.source}
    {e' : F' ⋙ U.dest = G' ⋙ U.source} (h : F = F') (k : G = G') : join M F G e = join M F' G' e' :=
  congrArg (· ⋙ M.tensor.functor) (combineEq h k)
theorem join_before {Y : Type*} [Category* Y] (J : Y ⥤ X) (F G : X ⥤ U.apex)
    (e : F ⋙ U.dest = G ⋙ U.source) :
    J ⋙ join M F G e = join M (J ⋙ F) (J ⋙ G) (congrArg (J ⋙ ·) e) :=
  congrArg (· ⋙ M.tensor.functor) (before J F G e)

/-- This form of the three strict equations is obtained by testing the
usual three universal diagrams. In particular it is about all native
arrows, not a relation of apex-object evaluation functions. -/
structure Laws : Prop where
  left : ∀ {X : Type b} [Category.{max b w} X] (F : X ⥤ U.apex),
    join M (one M (F ⋙ U.source)) F (one_dst M _) = F
  right : ∀ {X : Type b} [Category.{max b w} X] (F : X ⥤ U.apex),
    join M F (one M (F ⋙ U.dest)) (one_src M _).symm = F
  assoc : ∀ {X : Type b} [Category.{max b w} X] (F G H : X ⥤ U.apex)
    (e : F ⋙ U.dest = G ⋙ U.source) (d : G ⋙ U.dest = H ⋙ U.source),
    join M (join M F G e) H ((join_dst M F G e).trans d) =
      join M F (join M G H d) (e.trans (join_src M G H d).symm)

def CartesianMap (F : Over U V) : Prop :=
  ∀ {x y : U.apex} (f : x ⟶ y), Cartesian U.source f → Cartesian V.source (F.functor.map f)

def Normal (p : U.apex ⥤ B) (c : Cleavage p) : Prop :=
  ∀ y, (c (p.obj y) y (𝟙 (p.obj y))).obj = y ∧ HEq (c (p.obj y) y (𝟙 (p.obj y))).lift (𝟙 y)

structure Contextad (U : Span (B := B)) where
  operations : Ops U
  laws : Laws operations
  cleavage : Cleavage U.source
  normal : Normal U.source cleavage
  unitCart : CartesianMap operations.unit
  tensorCart : CartesianMap operations.tensor

end ContextualComposition.GrothendieckStep.StrictSpanAlgebra
