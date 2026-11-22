module
public import ContextualComposition.AddressedChartNaturality
public import ContextualComposition.ReverseNativeRoutes
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
universe u w
abbrev addStruct : AddStruct sum.{u} PEmpty where
  unitInv _ := Sum.elim PEmpty.elim id
  assoc _ _ _ := fun
    | .inl a => .inl (.inl a)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr c) => .inr c
  assocInv _ _ _ := fun
    | .inl (.inl a) => .inl a
    | .inl (.inr b) => .inr (.inl b)
    | .inr c => .inr (.inr c)
  swap _ _ := fun
    | .inl b => .inr b
    | .inr a => .inl a
def addInvertible : AddInvertible addStruct.{u} where
  unit _ := ⟨Sum.inr,rfl,by funext x; cases x with | inl x => exact x.elim | inr => rfl⟩
  assoc _ _ _ := ⟨addStruct.assocInv _ _ _,by funext x; rcases x with (a | b) | c <;> rfl,by funext x; rcases x with a | (b | c) <;> rfl⟩
  assocInv _ _ _ := ⟨addStruct.assoc _ _ _,by funext x; rcases x with a | (b | c) <;> rfl,by funext x; rcases x with (a | b) | c <;> rfl⟩
  swap _ _ := ⟨addStruct.swap _ _,by funext x; cases x <;> rfl,by funext x; cases x <;> rfl⟩
variable {X : Type w} (A : X → Type u)
theorem lookup_order {xs ys : List X} (p : AddressOrder X xs ys) (v : fold sum PEmpty A ys) :
    lookup xs (p.mapSum addStruct A v) = lookup ys v := by
  induction p with
  | ident => rfl
  | swap x y xs =>
    rcases v with a | (b | z) <;> rfl
  | keep x p ih =>
    cases v with
    | inl a => rfl
    | inr a => exact ih a
  | seq p q ih jh => exact (ih _).trans (jh v)
theorem order_coherence [DecidableEq X] {xs ys : List X} (nd : xs.Nodup)
    (p q : AddressOrder X xs ys) : p.mapSum addStruct A = q.mapSum addStruct A := by
  funext v
  have h := (lookup_order A p v).trans (lookup_order A q v).symm
  generalize p.mapSum addStruct A v = a at h ⊢
  generalize q.mapSum addStruct A v = b at h ⊢
  let decode (z : {z : Sigma A // z.1 ∈ xs}) := inject xs z.val.1 z.property z.val.2
  have hh : (⟨lookup xs a,lookup_mem xs a⟩ : {z : Sigma A // z.1 ∈ xs}) =
      ⟨lookup xs b,lookup_mem xs b⟩ := Subtype.ext h
  exact (inject_lookup xs nd a).symm.trans ((congrArg decode hh).trans (inject_lookup xs nd b))
end ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
