module
public import ContextualComposition.MixedEffects

/-! The terminal-monad nonfaithfulness example recalled by the fixed mixed
constructor in the relative construction manuscript. -/

@[expose] public section
namespace ContextualComposition.TerminalMonadComparison
open CategoryTheory MixedRecovery

def terminal : Monad (Type u) where
  obj _ := PUnit
  map _ := 𝟙 _
  η := { app _ := TypeCat.ofHom (fun _ => PUnit.unit) }
  μ := { app _ := 𝟙 _ }

/-- The terminal monad admits the unique mixed law with every comonad on types. -/
def law (G : Comonad (Type u)) : Law G terminal where
  trans := { app _ := TypeCat.ofHom (fun _ => PUnit.unit) }
  unit _ := by ext; rfl
  counit _ := by ext; rfl
  mul _ := by ext; rfl
  comul _ := by ext; rfl

theorem all_bodies_equal (G : Comonad (Type u)) {A B : Type u} (f g : G.obj A ⟶ B) :
    fromComonad (T := terminal) f = fromComonad (G := G) g := by ext; rfl

/-- The original context bodies can differ on an actual argument. -/
theorem not_injective :
    ¬ Function.Injective (fromComonad (G := ReaderWriter.reader Unit) (T := terminal) (A := Unit) (B := Bool)) := by
  intro h
  let f : (ReaderWriter.reader Unit).obj Unit ⟶ Bool := TypeCat.ofHom (fun _ => false)
  let g : (ReaderWriter.reader Unit).obj Unit ⟶ Bool := TypeCat.ofHom (fun _ => true)
  have he : f = g := h (all_bodies_equal (ReaderWriter.reader Unit) f g)
  have eq : false = true := congrArg (fun k : Unit × Unit ⟶ Bool => k ((),())) he
  exact Bool.noConfusion eq

end ContextualComposition.TerminalMonadComparison
