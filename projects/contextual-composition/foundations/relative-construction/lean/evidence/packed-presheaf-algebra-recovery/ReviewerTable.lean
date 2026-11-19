import Lean.Util.FoldConsts
import ContextualComposition.AccumulationAlgebra
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedFree AccumulationAlgebra
namespace ReviewerTable
set_option backward.isDefEq.respectTransparency false
abbrev B := Discrete Unit
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of B)
  extend _ := 𝟭 _
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
abbrev Z : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of (Discrete Bool))
def cst (t : Bool) {Y : Bᵒᵖ ⥤ Cat.{0,0}} : Y ⟶ Z where
  app _ := ((Functor.const _).obj (Discrete.mk t)).toCatHom
  naturality _ _ _ := rfl
def row (t : Bool) : (n : Nat) → pow S Z n ⟶ Z
  | 0 => 𝟙 _
  | _+1 => cst t
def k (t : Bool) := desc S (row t)
theorem unit (t : Bool) : inc S Z 0 ≫ k t = 𝟙 Z := inc_desc S _ 0
theorem consLaw (t : Bool) : HomLaw S (cons S Z) (cst t) (k t) := by
  apply step_pack_ext; intro n
  rw [← Category.assoc,inc_cons]
  exact (inc_desc S (row t) (n+1)).trans (by rfl)
theorem mul (t : Bool) : (free S).map (k t) ≫ k t = join S Z ≫ k t := by
  apply hom_ext S (cst t) (hom_comp S (map_hom S _) (consLaw t)) (hom_comp S (fold_hom S _ _) (consLaw t))
  erw [← Category.assoc,inc_map,Category.assoc,unit,Category.comp_id]
def K (t : Bool) : (monad S).Algebra := ⟨Z,k t,unit t,(mul t).symm⟩
-- The table construction and its two algebra proofs above use no AccumulationAlgebra declarations.
example (t : Bool) : (extend S).obj ((readOne S).obj (K t)) = K t := extend_restrict S _
theorem read_eq (t : Bool) : restrict S (K t) = cst t := inc_desc S _ 1
def baseObj : B := Discrete.mk ()
def atOne := pair Z (𝟭 B) baseObj (Discrete.mk false)
theorem disagree : restrict S (K false) ≠ restrict S (K true) := by
  intro h
  have hh := Functor.congr_obj (congrArg Cat.Hom.toFunctor (NatTrans.congr_app h (op baseObj))) atOne
  exact Bool.noConfusion (congrArg Discrete.as hh)
example : ¬ ∃ f : K false ⟶ K true, f.f = 𝟙 Z := by
  rintro ⟨f,h⟩
  apply disagree
  have hh := ((readOne S).map f).h
  change (step S).map f.f ≫ restrict S (K true) = restrict S (K false) ≫ f.f at hh
  erw [h,(step S).map_id Z,Category.id_comp,Category.comp_id] at hh
  exact hh.symm
-- Here the carrier map is not an isomorphism. It preserves the indicated, different reset tables.
def reset : Z ⟶ Z := cst true
theorem strict_reset : (free S).map reset ≫ k true = k false ≫ reset := by
  apply pack_ext; intro n
  erw [← Category.assoc,inc_map,Category.assoc,inc_desc,← Category.assoc,inc_desc]
  cases n <;> rfl
def resetHom : K false ⟶ K true := ⟨reset, strict_reset⟩
example : ((readOne S).map resetHom).f = reset := rfl
example : ((extend S).map ((readOne S).map resetHom)).f = reset := rfl
theorem differentCsts : (cst false : Z ⟶ Z) ≠ cst true := by
  intro h
  have q := Functor.congr_obj (congrArg Cat.Hom.toFunctor (NatTrans.congr_app h (op baseObj))) (Discrete.mk false)
  exact Bool.noConfusion (congrArg Discrete.as q)
example : ¬ IsIso reset := by
  intro h
  have same : (cst false : Z ⟶ Z) ≫ reset = cst true ≫ reset := rfl
  exact differentCsts ((cancel_mono reset).mp same)

-- The two EM laws do real work. With no unit, the all-false action is associative
-- but has the same singleton observation as the lawful K false.
def loseZero : (free S).obj Z ⟶ Z := cst false
example : (free S).map loseZero ≫ loseZero = join S Z ≫ loseZero := rfl
example : inc S Z 1 ≫ loseZero = restrict S (K false) := rfl
example : inc S Z 0 ≫ loseZero ≠ 𝟙 Z := by
  intro h
  have q := Functor.congr_obj (congrArg Cat.Hom.toFunctor (NatTrans.congr_app h (op baseObj))) (Discrete.mk true)
  exact Bool.noConfusion (congrArg Discrete.as q)
-- Satisfy the unit, break multiplication: arity 2 returns true although two singletons reset twice to false.
def fakeRow : (n : Nat) → pow S Z n ⟶ Z
  | 0 => 𝟙 _
  | 1 => cst false
  | _+2 => cst true
def fake := desc S fakeRow
example : inc S Z 0 ≫ fake = 𝟙 Z := inc_desc S _ 0
example : inc S Z 1 ≫ fake = restrict S (K false) := rfl
abbrev atTwo := pair ((step S).obj Z) (𝟭 B) baseObj atOne
example : (free S).map fake ≫ fake ≠ join S Z ≫ fake := by
  intro hm
  let nestedTag := ChainPayload.layerMap (inc S Z 1) S 1 ≫ inc S ((free S).obj Z) 1
  have hf := Functor.congr_obj (congrArg Cat.Hom.toFunctor (NatTrans.congr_app hm (op baseObj))) ((nestedTag.app (op baseObj)).toFunctor.obj atTwo)
  exact Bool.noConfusion (congrArg Discrete.as hf)
end ReviewerTable

open Lean Elab Command
private partial def tableDeps (env : Environment) (todo : List Name) (done : NameSet) : NameSet := Id.run do
  match todo with
  | [] => return done
  | n :: ns =>
    if done.contains n || !((`ReviewerTable).isPrefixOf n || (`ContextualComposition).isPrefixOf n) then return tableDeps env ns done
    let seen := done.insert n
    match env.find? n with
    | none => return tableDeps env ns seen
    | some c => return tableDeps env (c.getUsedConstantsAsSet.toList ++ ns) seen
run_cmd do
  let e ← getEnv
  -- Check both explicit algebra tables and the strict witness, not just their source spelling.
  let ds := tableDeps e [``ReviewerTable.K,``ReviewerTable.resetHom] {}
  for d in ds.toList do
    if (`ContextualComposition.GrothendieckStep.AccumulationAlgebra).isPrefixOf d then
      throwError "Independent EM table or map unexpectedly uses {d}."
