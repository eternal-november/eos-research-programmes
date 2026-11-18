module
public import ContextualComposition.TripleFibre
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TripleCuts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked BlockEvaluation WordTrace NativeTrace TripleEvaluation TripleTrace
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : Pr (B := B))
theorem readLength : (n : Nat) → (z : E (out S Y n)) → (read S Y n z).1.length = n
  | 0,_ => rfl
  | n+1,z => congrArg Nat.succ (readLength n (one S (out S Y n) z).2)
theorem wordLength : (n : Nat) → (z : Edge (power S n).apex) → (word S n z).length = n
  | 0,_ => rfl
  | n+1,z => by simp [word,wordLength n]
variable (n m k : Nat)
abbrev Packet := List (Atom (P := P)) × List (Atom (P := P)) × List (Atom (P := P)) × E Y
def decode (z : Edge (output S Y n m k)) : Packet (P := P) Y :=
  let a := read S (out S (out S Y k) m) n z
  let b := read S (out S Y k) m a.2
  let c := read S Y k b.2
  (a.1,b.1,c.1,c.2)
def native (z : Edge (input S Y n m k)) : Packet (P := P) Y :=
  (word S n (Edge.map (TripleTrace.first S Y n m k) z),word S m (Edge.map (TripleTrace.middle S Y n m k) z),
   word S k (Edge.map (TripleTrace.last S Y n m k) z),Edge.map (terminal S Y n m k) z)
def erase (w : Packet (P := P) Y) : Trace (P := P) Y := ((w.1 ++ w.2.1) ++ w.2.2.1,w.2.2.2)
theorem separate {x y : Packet (P := P) Y} (a : x.1.length = y.1.length) (b : x.2.1.length = y.2.1.length)
    (h : erase Y x = erase Y y) : x = y := by
  have j := congrArg Prod.fst h
  change (_ ++ _) ++ _ = (_ ++ _) ++ _ at j
  have l : (x.1 ++ x.2.1).length = (y.1 ++ y.2.1).length := by simp [a,b]
  have ab := List.append_inj_left j l
  have t := congrArg (fun p : Trace (P := P) Y => p.2) h
  exact Prod.ext (List.append_inj_left ab a) (Prod.ext (List.append_inj_right ab a) (Prod.ext (List.append_inj_right j l) t))
theorem grouped (z : Edge (input S Y n m k)) :
    decode S Y n m k (Edge.map (joinLast S Y n m k) z) = native S Y n m k z := by
  apply separate Y
  · exact (readLength S _ n _).trans (wordLength S n _).symm
  · exact (readLength S _ m _).trans (wordLength S m _).symm
  · exact groupedTrace S Y n m k z
/-- At a fixed ordered chart, the three separate lists and the terminal arrow
determine the nested arrow itself. No cancellation of packed multiplication. -/
theorem decodeInjective : Function.Injective (decode S Y n m k) := by
  intro z w h
  apply read_injective S _ n
  apply Prod.ext
  · exact congrArg (fun p : Packet (P := P) Y => p.1) h
  apply read_injective S _ m
  apply Prod.ext
  · exact congrArg (fun p : Packet (P := P) Y => p.2.1) h
  apply read_injective S _ k
  apply Prod.ext
  · exact congrArg (fun p : Packet (P := P) Y => p.2.2.1) h
  · exact congrArg (fun p : Packet (P := P) Y => p.2.2.2) h
end ContextualComposition.GrothendieckStep.TripleCuts
