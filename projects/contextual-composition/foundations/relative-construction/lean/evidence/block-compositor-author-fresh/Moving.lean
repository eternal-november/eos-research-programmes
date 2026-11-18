import ContextualComposition.BlockCompositor
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativePacked NativeCleavage BlockEvaluation SpanApex
namespace Moving212
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
inductive B | pt
instance : Category B where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev b := B.pt
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of B)
  extend _ := 𝟭 _
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
inductive G | pt
instance : Category G where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp := by intros; apply List.nil_append
  comp_id := by intros; apply List.append_nil
  assoc := by intros; apply List.append_assoc
def Y : Bᵒᵖ ⥤ Cat.{0,0} where
  obj _ := Cat.of (Bool → G)
  map f := (Pi.comap (fun _ : Bool => G) (show Bool → Bool from f.unop)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def one : (power S 1).apex := pair P.grades (𝟭 B) b b
def two : (power S 2).apex := pair P.grades _ one b
def atom (s p : b ⟶ b) : one ⟶ one := arrow s p
def bi (m p q : b ⟶ b) : two ⟶ two := arrow (atom m p) q
def obj : (fixed S (1,2)).apex := ⟨one,two,rfl⟩
def move (s m p q : b ⟶ b) : obj ⟶ obj := ⟨⟨atom s m,bi m p q,rfl⟩⟩
def x := pair Y (fixed S (1,2)).dest obj (fun _ => G.pt)
def ar (s m p q : b ⟶ b) (k : Bool → List Nat) : x ⟶ x := arrow (move s m p q) k
def no : b ⟶ b := fun _ => false
def yes : b ⟶ b := fun _ => true
def flip : b ⟶ b := Bool.not
def f : x ⟶ x := ar yes no flip no (fun i => if i then [4,9] else [5])
def g : x ⟶ x := ar no yes no yes (fun i => if i then [8] else [2,6])

open WordTrace BlockCompositor
abbrev FX := Total Y (fixed S (1,2)).dest
def marks (p : Trace (P := P) Y) : List (Bool × Bool) :=
  p.1.map (fun z => ((show Bool → Bool from gradeMap z.hom) false,(show Bool → Bool from payloadMap z.hom) false))
def label (p : Trace (P := P) Y) : List Nat := payloadMap p.2.hom true
noncomputable abbrev staged (z : Edge FX) := flattenRead S Y 1 2 (Edge.map (totalStages S Y 1 2) z)
noncomputable abbrev joined := Lift.total (BlockCompositor.join S 1 2) Y ⋙ global S Y 3 ⋙ transport (PackedCuts.sameLength S Y (1,2)).symm
noncomputable abbrev whole (z : Edge FX) := flattenRead S Y 1 2 (Edge.map joined z)
theorem comparison (z : Edge FX) : whole z = staged z :=
  congrArg (fun H => flattenRead S Y 1 2 (Edge.map H z)) (onMatched S Y 1 2).symm
example : marks (whole ⟨x,x,f⟩) = [(true,false),(false,true),(true,false)] := by rw [comparison,staged,stagesTrace]; rfl
example : marks (whole ⟨x,x,g⟩) = [(false,true),(true,false),(false,true)] := by rw [comparison,staged,stagesTrace]; rfl
example : label (whole ⟨x,x,f ≫ g⟩) = [4,9,2,6] := by rw [comparison,staged,stagesTrace]; rfl
example : label (whole ⟨x,x,g ≫ f⟩) = [8,4,9] := by rw [comparison,staged,stagesTrace]; rfl
-- Same exterior and final base arrows and same payload labels. Only the moving internal grade changes.
def f' : x ⟶ x := ar yes yes flip no (fun i => if i then [4,9] else [5])
example : label (whole ⟨x,x,f'⟩) = label (whole ⟨x,x,f⟩) := by simp only [comparison,staged,stagesTrace]; rfl
example : marks (whole ⟨x,x,f'⟩) ≠ marks (whole ⟨x,x,f⟩) := by simp only [comparison,staged,stagesTrace]; decide
end Moving212
