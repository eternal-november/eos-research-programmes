module
public import ContextualComposition.AugmentedOneSidedRecovery

/-! Local hom recoveries at genuinely terminal one-sided grade fibres,
and the distinct control in which only the coefficient rig is terminal. -/

@[expose] public section
namespace ContextualComposition.OneSidedTrivializations
open CategoryTheory NativeFinitePush
universe u v

def trivialContext {L : Type u} [Category.{v} L] {C : Type*} [Category* C] (A : C) (d : L ⥤ C) :
    Comma (Functor.fromPUnit.{0} A) d ≌ StructuredArrow A d := CategoryTheory.Equivalence.refl

def trivialContent {K : Type u} [Category.{v} K] {C : Type*} [Category* C] (e : K ⥤ C) (B : C) :
    Comma e (Functor.fromPUnit.{0} B) ≌ CostructuredArrow e B := CategoryTheory.Equivalence.refl

abbrev coeff : Coeff.{0,0} Unit where
  Hom _ _ := Unit
  id _ := ()
  seq _ _ := ()
  id_seq _ := rfl
  seq_id _ := rfl
  assoc _ _ _ := rfl

abbrev push : Push coeff where
  obj _ _ _ := ()
  map := fun {_ _} _ {_ _} _ _ => ()
  map_id _ _ := rfl
  map_seq := by intros; rfl
  single _ _ := ()
  split _ _ _ _ := ()
  single_nat _ := rfl
  split_nat := by intros; rfl
  left_unit _ _ := rfl
  right_unit _ _ := rfl
  pent _ _ _ _ := rfl

theorem native_ext {A B : Family Unit} {p q : Hom push A B} (h : p.addr = q.addr) : p = q := by
  cases p with | mk a c =>
    cases q with | mk b d =>
      change a = b at h
      subst b
      have e : c = d := Subsingleton.elim _ _
      cases e; rfl

/-- All finite carriers occur, even though every coefficient and its
every morphism are the unique object and map of the coefficient rig. -/
abbrev family (n : Nat) : Aug push () := ⟨⟨n,fun _ => ()⟩,⟨fun _ => (0 : Fin 1),fun _ => ()⟩⟩

def allFunctions (p q : Aug push ()) : AugHom push p q ≃ (Fin p.base.n → Fin q.base.n) where
  toFun f := f.native.addr
  invFun k := ⟨⟨k,fun _ => ()⟩,native_ext (funext fun _ => @Subsingleton.elim (Fin 1) _ _ _)⟩
  left_inv _ := AugHom.ext (native_ext rfl)
  right_inv _ := rfl

theorem not_terminal_context : ¬ Subsingleton (AugHom push (family 2) (family 2)) := by
  intro h
  let e := allFunctions (family 2) (family 2)
  have k := congrArg e (h.allEq (e.symm id) (e.symm (fun _ => 0)))
  rw [e.apply_symm_apply,e.apply_symm_apply] at k
  exact (by decide : (1 : Fin 2) ≠ 0) (congrFun k 1)

end ContextualComposition.OneSidedTrivializations
