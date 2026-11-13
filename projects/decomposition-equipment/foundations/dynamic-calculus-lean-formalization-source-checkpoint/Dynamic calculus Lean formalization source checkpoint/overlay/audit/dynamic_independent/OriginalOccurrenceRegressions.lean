import WitnessedDecompositions.PathOccurrences

/- Independent discriminators for the original occurrence API. -/
namespace DynamicIndependent.OriginalOccurrences
open WitnessedDecompositions

instance : Quiver Unit where
  Hom _ _ := Unit

def color : Component Unit := ⟨(), (), ()⟩
def once : Quiver.Path () () := (show (() : Unit) ⟶ (() : Unit) from ()).toPath
def twice : Quiver.Path () () := once.cons (show (() : Unit) ⟶ (() : Unit) from ())
def first : Path.Slot twice := .inl (.inr ())
def second : Path.Slot twice := .inr ()

theorem same_color : Path.componentAt twice first = Path.componentAt twice second := rfl

theorem different_occurrences : first ≠ second := by
  intro h
  cases h

def independentValues : Path.Slot twice → Bool
  | .inl (.inl e) => nomatch e
  | .inl (.inr ()) => false
  | .inr () => true

theorem ordered_distinct_values :
    Path.collect twice (fun i => [independentValues i]) = [false, true] := rfl

def oneEmptyOneIdentity (i : Path.Slot twice) :
    Quiver.Path (Path.componentAt twice i).source (Path.componentAt twice i).target :=
  match i with
  | .inl (.inl e) => nomatch e
  | .inl (.inr ()) => .nil
  | .inr () => Quiver.Path.nil.cons ()

theorem mixed_empty_profile :
    Path.expand twice oneEmptyOneIdentity = Quiver.Path.nil.cons () := rfl

def allEmpty (i : Path.Slot twice) :
    Quiver.Path (Path.componentAt twice i).source (Path.componentAt twice i).target :=
  match i with
  | .inl (.inl e) => nomatch e
  | .inl (.inr ()) => .nil
  | .inr () => .nil

theorem all_nullary_profile : Path.expand twice allEmpty = Quiver.Path.nil := rfl

end DynamicIndependent.OriginalOccurrences
