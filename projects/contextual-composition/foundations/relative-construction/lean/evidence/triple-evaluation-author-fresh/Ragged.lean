import ContextualComposition.TripleCuts
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedCuts
namespace Ragged214
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
def loop {C : Type*} [Category* C] (x : C) : Edge C := ⟨x,x,𝟙 x⟩
def labels (r : Trace (P := P) Y) := r.1.map (fun (g : Atom (P := P)) => (grade P.grades (𝟭 Nat) g.src,(show Discrete Nat from payload P.grades (𝟭 Nat) g.src).as))
noncomputable def obs (n m k : Nat) (a : input S Y n m k) := observe S Y n m k (Edge.map (joinLast S Y n m k) (loop a))
theorem readX : labels (obs 1 2 1 x) = [(1,4),(14,6),(146,8),(1468,3)] := (congrArg labels (groupedTrace S Y 1 2 1 (loop x))).trans rfl
theorem readY : labels (obs 2 1 1 y) = [(1,4),(14,6),(146,8),(1468,3)] := (congrArg labels (groupedTrace S Y 2 1 1 (loop y))).trans rfl
example : labels (obs 1 2 1 x) = labels (obs 2 1 1 y) := readX.trans readY.symm
-- The first genuine interior boundary changes even though the entire decoded primitive word is identical.
def boundary (n m k : Nat) (a : input S Y n m k) :=
  (first S Y n m k ⋙ (power S n).dest).obj a
example : boundary 1 2 1 x = 14 ∧ boundary 2 1 1 y = 146 := ⟨rfl,rfl⟩
example : labels (obs 1 0 1 z) = [(1,4),(14,6)] := (congrArg labels (groupedTrace S Y 1 0 1 (loop z))).trans rfl
def x' : input S Y 1 2 1 := pair Y _ ⟨⟨one 1 4,two 14 6 8,rfl⟩,one 1468 3,rfl⟩ (fun i : Fin 14683 => i.val+2)
def raise : x ⟶ x' := arrow (𝟙 _) (fun _ => homOfLE (Nat.le_succ _))
theorem nonIso : ¬ IsIso raise := by
  intro h
  have v := payloadMap (inv raise) (⟨0,by decide⟩ : Fin 14683)
  have bad : 2 ≤ 1 := leOfHom v
  omega
example : ¬ IsIso ((joinLast S Y 1 2 1).map raise) := by
  let F := joinLast S Y 1 2 1
  let _ : F.IsIso := TripleFibre.lastIso S Y 1 2 1
  let _ := F.asIsomorphism.toEquivalence.isEquivalence_functor
  intro h
  exact nonIso (isIso_of_reflects_iso raise F)
def digits (p : TripleCuts.Packet (P := P) Y) :=
  let tag := fun g : Atom (P := P) => (show Discrete Nat from payload P.grades (𝟭 Nat) g.src).as
  (p.1.map tag,p.2.1.map tag,p.2.2.1.map tag)
noncomputable def cuts (n m k : Nat) (a : input S Y n m k) :=
  digits (TripleCuts.decode S Y n m k (Edge.map (joinLast S Y n m k) (loop a)))
theorem cutX : cuts 1 2 1 x = ([4],[6,8],[3]) := (congrArg digits (TripleCuts.grouped S Y 1 2 1 (loop x))).trans rfl
theorem cutY : cuts 2 1 1 y = ([4,6],[8],[3]) := (congrArg digits (TripleCuts.grouped S Y 2 1 1 (loop y))).trans rfl
example : cuts 1 2 1 x ≠ cuts 2 1 1 y := by rw [cutX,cutY]; decide
end Ragged214
