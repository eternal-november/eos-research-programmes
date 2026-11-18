module
public import ContextualComposition.MovingAssembly
public import ContextualComposition.GaugeLawExtra
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem castsPacked (J : C ⥤ D) (K : E ⥤ C) {a d : C} {b c : E} (p : a ⟶ K.obj b) (e : b = c) (f : K.obj c = d)
    {u v : D} (l : J.obj (K.obj b) = u) (r : J.obj (K.obj c) = v) (h : u = v) :
    ((J.map p ≫ eqToHom l) ≫ eqToHom h ≫ eqToHom r.symm ≫ J.map (eqToHom f)) =
      J.map (p ≫ K.map (eqToHom e) ≫ eqToHom f) := by
  rw [eqToHom_map K e]
  exact casts J p (congrArg K.obj e) f l r h
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
theorem frames (x : X S Y) : cFrame S Y x = (I S Y x).map (nFrame S Y x) := by
  unfold cFrame nFrame
  rw [leftLaw, rInv]
  unfold lFrame
  exact castsPacked (I S Y x) (pack S Y (A S Y x) (decode S Y x).1) (pfx S Y (A S Y x) (point S Y x))
    (Functor.congr_obj (BlockCompositor.fixedCompositor S Y (A S Y x) (decode S Y x).1.1 (decode S Y x).1.2) (decode S Y x).2)
    (Functor.congr_obj (oldChart S Y (A S Y x)) (decode S Y x))
    (firstObj S Y (A S Y x) (decode S Y x).1 (decode S Y x).2)
    (secondObj S Y (A S Y x) (decode S Y x).1 (decode S Y x).2)
    (Functor.congr_obj (refEq S Y) x)
theorem component (x : X S Y) :
    (cell S Y).hom.app x = (I S Y x).map ((BlockCompositor.compositor S Y (A S Y x)).hom.app (point S Y x)) :=
  (cellLaw S Y x).trans ((frames S Y x).trans (congrArg (I S Y x).map (priorLaw S Y x).symm))
theorem moving {x y : X S Y} (f : x ⟶ y) :
    (leftTotal S Y).map f ≫ (I S Y y).map ((BlockCompositor.compositor S Y (A S Y y)).hom.app (point S Y y)) =
      (I S Y x).map ((BlockCompositor.compositor S Y (A S Y x)).hom.app (point S Y x)) ≫ (rightTotal S Y).map f :=
  (congrArg ((leftTotal S Y).map f ≫ ·) (component S Y y).symm).trans
    (((cell S Y).hom.naturality f).trans (congrArg (· ≫ (rightTotal S Y).map f) (component S Y x)))
end ContextualComposition.GrothendieckStep.MovingCell
