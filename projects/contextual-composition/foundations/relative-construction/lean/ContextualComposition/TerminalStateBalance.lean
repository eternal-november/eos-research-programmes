module

public import ContextualComposition.DirectedStateDiagramMap
public import ContextualComposition.DirectedStateBoundaries

/-! With constant terminal process fibres the entire directed contraction is isomorphic to the state category. -/

@[expose] public section
namespace ContextualComposition.TerminalStateBalance

open CategoryTheory Opposite DirectedStateBalance DirectedStateBoundary
universe u v
variable (S : Type u) [Category.{v} S]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev pt : Discrete Unit := ⟨()⟩
abbrev vertex (s : S) := (insertion (terminalDiagram S) s).obj pt
abbrev step {s t : S} (h : s ⟶ t) : vertex S s ⟶ vertex S t := (slide (terminalDiagram S) h).app pt

theorem only_native (s : S) (f : pt ⟶ pt) : (insertion (terminalDiagram S) s).map f = 𝟙 _ := by
  have eq : f = 𝟙 pt := Subsingleton.elim _ _
  exact (congrArg (insertion (terminalDiagram S) s).map eq).trans ((insertion _ _).map_id _)

def represent : S ⥤ Balance (terminalDiagram S) where
  obj := vertex S
  map h := step S h
  map_id s := (restrict (𝟭 (Balance (terminalDiagram S)))).unit (i := s) pt
  map_comp {i j k} f g := by
    let F := terminalDiagram S
    have e := (restrict (𝟭 (Balance F))).comp f g pt
    change step S (f≫g) = (insertion F i).map _ ≫ step S f ≫ (insertion F j).map _ ≫ step S g ≫ (insertion F k).map _ at e
    rw [only_native S i,only_native S j,only_native S k] at e
    simp only [Category.id_comp,Category.comp_id] at e
    exact e

theorem state_represent : state (terminalDiagram S) ⋙ represent S = 𝟭 _ := by
  let F := terminalDiagram S
  apply DirectedStateDiagramMap.functor_ext (P:=state F ⋙ represent S) (Q:=𝟭 _)
  · intro i x; obtain ⟨⟨⟩⟩ := x; rfl
  · intro i x y f
    obtain ⟨⟨⟩⟩ := x; obtain ⟨⟨⟩⟩ := y
    exact heq_of_eq ((congrArg (represent S).map (native_label F f)).trans (((represent S).map_id i).trans (only_native S i f).symm))
  · intro i j h x
    obtain ⟨⟨⟩⟩ := x
    exact heq_of_eq (congrArg (represent S).map (slide_label F h pt))

theorem represent_state : represent S ⋙ state (terminalDiagram S) = 𝟭 _ := by
  apply Functor.hext (F := represent S ⋙ state (terminalDiagram S)) (G := 𝟭 S) (fun _ => rfl)
  exact fun _ _ h => heq_of_eq (slide_label (terminalDiagram S) h pt)

def terminal_iso : IsoCat (Balance (terminalDiagram S)) S where
  functor := state _
  inverse := represent S
  unit_eq := (state_represent S).symm
  counit_eq := represent_state S

end ContextualComposition.TerminalStateBalance
