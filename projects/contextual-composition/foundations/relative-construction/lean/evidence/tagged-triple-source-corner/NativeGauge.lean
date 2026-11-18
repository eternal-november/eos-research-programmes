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
end Ragged220
open CategoryTheory
namespace TargetGaugeProbe
inductive D where | point
instance : Category D where
  Hom _ _ := Bool
  id _ := false
  comp f g := Bool.xor f g
  id_comp := by intros x y f; cases f <;> rfl
  comp_id := by intros x y f; cases f <;> rfl
  assoc := by intros a b c d f g h; cases f <;> cases g <;> cases h <;> rfl
def twist : 𝟭 D ⟶ 𝟭 D where
  app _ := true
  naturality := by intros x y f; change Bool.xor f true = Bool.xor true f; cases f <;> rfl
def targetAlternative : 𝟭 D ≅ 𝟭 D where
  hom := twist
  inv := twist
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl
example : (𝟙 (𝟭 D)) ≫ targetAlternative.hom ≠ (𝟙 (𝟭 D)) ≫ (𝟙 (𝟭 D)) := by
  intro h
  have b : true = false := NatTrans.congr_app h D.point
  cases b
end TargetGaugeProbe
namespace GlobalGauge220
open CategoryTheory TargetGaugeProbe Ragged220 ContextualComposition.GrothendieckStep
-- Countermodel on the actual native ragged source (not the actual target).
abbrev K := (Functor.const (TaggedTripleCover.target S Y)).obj D.point
def τ : K ⟶ K where
  app _ := true
  naturality := by intros; rfl
example : τ ≠ 𝟙 K := by
  intro h
  exact Bool.noConfusion (NatTrans.congr_app h ((TaggedTripleCover.incl S Y 1 0 1).obj z))
example : τ ≫ τ = 𝟙 K := by ext; rfl
-- For arbitrarily chosen frames a changed first and fourth edge can jointly
-- pass *every* local test for an all-identity fixed square. This does not
-- change the global equation, but destroys uniqueness without fixing frames.
example : τ ≫ τ = 𝟙 K ≫ 𝟙 K ∧ τ ≫ 𝟙 K = τ ≫ 𝟙 K ∧ τ ≠ 𝟙 K := by
  refine ⟨?_,rfl,?_⟩
  · ext; rfl
  · intro h; exact Bool.noConfusion (NatTrans.congr_app h ((TaggedTripleCover.incl S Y 1 2 1).obj x))
open SpanApex NativeBlocks NativeBlocks.Nested NativePacked TripleBoundary
theorem idxEq {I : Type*} {C : I → Type*} [∀i,Category* (C i)] {x y : Σ i, C i} (f : x ⟶ y) : x.1 = y.1 := by
  cases f; rfl
theorem tagStable {x y : TaggedTripleCover.target S Y} (f : x ⟶ y) : tags x = tags y := by
  have h₁ := idxEq ((a (whole S) (whole S) (whole S)).map (gradeMap f))
  have h₂ := idxEq ((b (whole S) (whole S) (whole S)).map (gradeMap f))
  have h₃ := idxEq ((c (whole S) (whole S) (whole S)).map (gradeMap f))
  exact Prod.ext h₁ (Prod.ext h₂ h₃)
def localTwist : K ⟶ K where
  app x := decide (tags x = (1,2,1))
  naturality := by
    intro x y f
    change Bool.xor false (decide (tags y = (1,2,1))) = Bool.xor (decide (tags x = (1,2,1))) false
    rw [tagStable f]; cases decide (tags y = (1,2,1)) <;> rfl
example : whiskerLeft (TaggedTripleCover.incl S Y 2 1 1) localTwist = whiskerLeft (TaggedTripleCover.incl S Y 2 1 1) (𝟙 K) := by ext; rfl
example : localTwist ≠ 𝟙 K := by
  intro h
  exact Bool.noConfusion (NatTrans.congr_app h ((TaggedTripleCover.incl S Y 1 2 1).obj x))
end GlobalGauge220
