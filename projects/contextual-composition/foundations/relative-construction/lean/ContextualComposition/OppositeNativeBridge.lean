module

public import ContextualComposition.NativeFibreAdapter
public import ContextualComposition.OppositeTypeFamilies

@[expose] public section

/-! From the finite addressed reverse-function instantiation to the
repository's total-token presentation. Global augmentation preservation is
obtained from the actual native equation, not postulated for this bridge. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
universe u
def mark {A : Family (Type u)} (ε : Hom push A (terminalShape PUnit)) : Sigma A.val :=
  let p := ε.cell (0:Fin 1) ⟨⟩
  ⟨p.1.val,p.2⟩
def toTotal (A : Aug push.{u} PUnit) : ContextualComposition.OppositeTypeFamilies.Family.{u} where
  Pos := ULift.{u} (Fin A.base.n)
  Tok := Sigma A.base.val
  atPos v := ⟨v.1⟩
  mark := mark A.ε

def back {A B : Family (Type u)} (h : Hom push A B) (v : Sigma B.val) : Sigma A.val :=
  let p := h.cell v.1 v.2
  ⟨p.1.val,p.2⟩
def toTotalHom {A B : Aug push.{u} PUnit} (h : AugHom push A B) : ContextualComposition.OppositeTypeFamilies.Hom (toTotal A) (toTotal B) where
  f v := ⟨h.native.addr v.down⟩
  back := back h.native
  over v := congrArg ULift.up (h.native.cell v.1 v.2).1.property
  aug := congrArg mark h.preserves
theorem total_ident (A : Aug push.{u} PUnit) :
    toTotalHom (AugHom.ident A) = ContextualComposition.OppositeTypeFamilies.id (toTotal A) := rfl
theorem total_comp {A B D : Aug push.{u} PUnit} (h : AugHom push A B) (k : AugHom push B D) :
    toTotalHom (h.comp k) = ContextualComposition.OppositeTypeFamilies.comp (toTotalHom h) (toTotalHom k) := rfl

theorem terminalHom_ext {A : Family (Type u)} {p q : Hom push A (terminalShape PUnit)}
    (hp : mark p = mark q) : p = q := by
  cases p with | mk f a =>
    cases q with | mk g b =>
      have he : f = g := funext fun i => @Subsingleton.elim (Fin 1) inferInstance (f i : Fin 1) (g i)
      subst g
      congr 1
      funext j v
      have hj : j = (0:Fin 1) := @Subsingleton.elim (Fin 1) inferInstance (j : Fin 1) _
      subst j
      cases v
      let proj (s : fibre f A.val (0:Fin 1)) : Sigma A.val := ⟨s.1.val,s.2⟩
      have faithful : ∀ s t, proj s = proj t → s = t := by
        rintro ⟨⟨i,hi⟩,s⟩ ⟨⟨j,hj⟩,t⟩ h
        cases h
        rfl
      exact faithful _ _ hp

def fromTotalHom {A B : Aug push.{u} PUnit}
    (h : ContextualComposition.OppositeTypeFamilies.Hom (toTotal A) (toTotal B)) : AugHom push A B where
  native := {
    addr := fun i => (h.f ⟨i⟩).down
    cell := fun j v =>
      let a := h.back ⟨j,v⟩
      ⟨⟨a.1,congrArg ULift.down (h.over ⟨j,v⟩)⟩,a.2⟩ }
  preserves := terminalHom_ext h.aug
theorem from_to {A B : Aug push.{u} PUnit} (h : AugHom push A B) : fromTotalHom (toTotalHom h) = h := rfl
theorem to_from {A B : Aug push.{u} PUnit}
    (h : ContextualComposition.OppositeTypeFamilies.Hom (toTotal A) (toTotal B)) :
    toTotalHom (fromTotalHom h) = h := rfl
end ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
