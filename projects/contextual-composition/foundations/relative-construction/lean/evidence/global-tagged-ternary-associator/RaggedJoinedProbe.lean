import ContextualComposition.JoinedChartFrames
import ContextualComposition.TaggedTripleCover
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep SpanApex NativeBlocks
namespace Ragged220
set_option backward.isDefEq.respectTransparency false
-- Primitive labels are discrete but context-dependent payloads distinguish every decimal step of the cut.
def extF (a : Nat) : Discrete Nat ⥤ Nat := Discrete.functor (fun k : Nat => 10*a+k)
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of (Discrete Nat))
  extend := extF
  lift {a a'} f := { app := fun k => homOfLE (Nat.add_le_add_right (Nat.mul_le_mul_left 10 f.le) k.as) }
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj n := Cat.of (Fin n.unop → Nat)
  map f := (Pi.comap (fun _ => Nat) (Fin.castLE f.unop.le)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
open NativeBlocks SpanApex TripleBoundary TripleTrace TripleEvaluation WordTrace
def one (a k : Nat) : (power S 1).apex := pair P.grades (𝟭 Nat) a (Discrete.mk k)
def two (a i j : Nat) : (power S 2).apex := pair P.grades _ (one a i) (Discrete.mk j)
def x : input S Y 1 2 1 := pair Y _ ⟨⟨one 1 4,two 14 6 8,rfl⟩,one 1468 3,rfl⟩ (fun i : Fin 14683 => i.val+1)
def y : input S Y 2 1 1 := pair Y _ ⟨⟨two 1 4 6,one 146 8,rfl⟩,one 1468 3,rfl⟩ (fun i : Fin 14683 => i.val+1)
def z : input S Y 1 0 1 := pair Y _ ⟨⟨one 1 4,(14 : Nat),rfl⟩,one 14 6,rfl⟩ (fun i : Fin 146 => i.val+1)
def tags (u : TaggedTripleCover.target S Y) := 
  let g := grade _ _ u
  (g.fst.fst.1,g.fst.snd.1,g.snd.1)
example : tags ((TaggedTripleCover.incl S Y 1 2 1).obj x) = (1,2,1) := rfl
example : tags ((TaggedTripleCover.incl S Y 2 1 1).obj y) = (2,1,1) := rfl
example : tags ((TaggedTripleCover.incl S Y 1 0 1).obj z) = (1,0,1) := rfl
def x' : input S Y 1 2 1 := pair Y _ ⟨⟨one 1 4,two 14 6 8,rfl⟩,one 1468 3,rfl⟩ (fun i : Fin 14683 => i.val+2)
def raise : x ⟶ x' := arrow (𝟙 _) (fun _ => homOfLE (Nat.le_succ _))
theorem nonIso : ¬ IsIso raise := by
  intro h
  have v := payloadMap (inv raise) (⟨0,by decide⟩ : Fin 14683)
  have bad : 2 ≤ 1 := leOfHom v
  omega
example : ¬ IsIso ((TaggedTripleCover.incl S Y 1 2 1).map raise) := by
  intro h
  have v := payloadMap (inv ((TaggedTripleCover.incl S Y 1 2 1).map raise)) (⟨0,by decide⟩ : Fin 14683)
  have bad : 2 ≤ 1 := leOfHom v
  omega
open JoinedChartFrames TaggedFixedSquare
example := NatTrans.congr_app (targetTest S Y 1 2 1) x
example := NatTrans.congr_app (targetTest S Y 2 1 1) y
example := NatTrans.congr_app (targetTest S Y 1 0 1) z
example := (JoinedTarget.comparison S Y).hom.naturality ((TaggedTripleCover.incl S Y 1 2 1).map raise)
def innerBoundary (u : TaggedTripleCover.target S Y) : Nat :=
  (NativeBlocks.Nested.whole S).dest.obj (grade _ _ u).fst.fst
example : innerBoundary ((TaggedTripleCover.incl S Y 1 2 1).obj x) = 14 ∧
    innerBoundary ((TaggedTripleCover.incl S Y 2 1 1).obj y) = 146 := ⟨rfl,rfl⟩
example (t : TaggedTripleFaces.firstRight S Y ⟶ TaggedTripleFaces.lastRight S Y)
    (ht : ∀ n m k, TaggedSquareRecognition.edge S Y n m k t ≫ (JoinedChartFrames.joinLast S Y n m k).hom =
      (JoinedChartFrames.joinFirst S Y n m k).hom ≫ TaggedFixedSquare.ft S Y n m k) :
    t = (JoinedTarget.comparison S Y).hom := JoinedChartFrames.unique S Y ht
end Ragged220
