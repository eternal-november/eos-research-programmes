import ContextualComposition.TripleTrace
open CategoryTheory Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativePacked BlockEvaluation WordTrace
namespace TripleMoving
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
structure Ctx where height : Nat
instance : Category Ctx where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
inductive Letter | dawn | dusk deriving DecidableEq
instance : Category Letter where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp _ := List.nil_append _
  comp_id _ := List.append_nil _
  assoc _ _ _ := List.append_assoc ..
def K : Ctxᵒᵖ ⥤ Cat.{0,0} where
  obj _ := Cat.of (Bool → Letter)
  map f := (Pi.comap (fun _ : Bool => Letter) (show Bool → Bool from f.unop)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def P : Endpoints.{0,0,0,0} Ctx where
  grades := K
  extend a := (Functor.const _).obj ⟨a.height+1⟩
  lift f := { app := fun _ => f }
theorem S : P.Split := ⟨fun _ => HEq.rfl, fun _ _ => HEq.rfl⟩
def col : Bool → Letter := fun j => if j then .dawn else .dusk
def shade (a : Nat) := if a % 2 = 0 then col else col ∘ Bool.not
def one (a : Nat) : (power S 1).apex := pair P.grades (𝟭 Ctx) ⟨a⟩ (shade a)
open TripleEvaluation TripleTrace TripleBoundary
abbrev T := L (power S 1) (power S 1) (power S 1)
def ob (a : Nat) : T.apex := ⟨⟨one a,one (a+1),rfl⟩,one (a+2),rfl⟩
def x (a : Nat) : input S K 1 1 1 := pair K _ (ob a) (shade (a+3))
def label (k : Nat) : Bool → List Nat := fun b => [k,if b then 1 else 0]
def single (a b : Nat) (f : Bool → Bool) (k : Nat) : one a ⟶ one b := arrow (show (Ctx.mk a ⟶ Ctx.mk b) from f) (label k)
def ar (a b : Nat) (f : Bool → Bool) (i j k t : Nat) : x a ⟶ x b :=
  arrow (⟨⟨⟨⟨single a b f i,single (a+1) (b+1) f j,rfl⟩⟩,single (a+2) (b+2) f k,rfl⟩⟩ : ob a ⟶ ob b) (label t)
def get (a : Edge (Total K (𝟭 Ctx))) : List Nat := (show Bool → List Nat from payloadMap (Y := K) (e := 𝟭 Ctx) a.hom) false
def labels (r : Trace (P := P) K) : List (List Nat) × List Nat := (r.1.map get,get r.2)
def ends (r : Trace (P := P) K) := (r.1.map (fun (a : Atom (P := P)) =>
    ((left P).obj a.src |>.height,(left P).obj a.dst |>.height)),((grade _ _ r.2.src).height,(grade _ _ r.2.dst).height))
def f := ar 4 7 Bool.not 10 20 30 40
def f' := ar 4 7 (fun _ => false) 10 20 30 40
def g := ar 7 11 (fun _ => true) 11 21 31 41
def z : Edge (input S K 1 1 1) := ⟨_,_,f ≫ g⟩
def z' : Edge (input S K 1 1 1) := ⟨_,_,f' ≫ g⟩
noncomputable abbrev read (e : Edge (input S K 1 1 1)) := observe S K 1 1 1 (Edge.map (joinLast S K 1 1 1) e)
example : labels (read z) = ([[10,0,11,1],[20,0,21,1],[30,0,31,1]],[40,0,41,1]) :=
  (congrArg labels (groupedTrace S K 1 1 1 z)).trans rfl
example : labels (read z') = ([[10,0,11,0],[20,0,21,0],[30,0,31,0]],[40,0,41,0]) :=
  (congrArg labels (groupedTrace S K 1 1 1 z')).trans rfl
example : ends (read z) = ([(4,11),(5,12),(6,13)],(7,14)) := (congrArg ends (groupedTrace S K 1 1 1 z)).trans rfl
-- Unequal grade and payload maps survive both groupings, even with the same composite exterior arrow.
example : Edge.map (joinFirst S K 1 1 1) z ≠ Edge.map (joinLast S K 1 1 1) z' := by
  rw [fixedAssociativity]
  intro h
  have eq := congrArg (fun w => labels (observe S K 1 1 1 w)) h
  have p := (congrArg labels (groupedTrace S K 1 1 1 z)).symm.trans (eq.trans (congrArg labels (groupedTrace S K 1 1 1 z')))
  exact (by decide : [40,0,41,1] ≠ [40,0,41,0]) (congrArg Prod.snd p)
end TripleMoving
