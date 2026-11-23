module
public import ContextualComposition.NativeFubiniTreeTags
@[expose] public section

/-! Interpret each occurrence tag by the appropriate leaf coefficient.
Equal coefficients do not imply equality of taggings. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [cat : Category.{v} C] [add : MonoidalCategory C] [sa : SymmetricCategory C]
variable {I : C} {Tag : Type w} {T : Bi (coeff (C:=C))}
variable (V : Tag → C)

def Tagging.Matches : {a : DependentFubiniTree I} → Tagging Tag a → a.Address → Prop
  | _, .unit, _ => True
  | _, .leaf A tag, z => V tag = T.obj (A.V z.1) (A.A z.1 z.2)
  | _, .fork l r, z => Matches l z.1 ∧ Matches r z.2

theorem Tagging.matches_eval (mul : MonoidalCategory C) :
    let Iₘ := @MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct
    (t : @DependentFubiniTree C cat add sa Iₘ) →
      (s : @Tagging C cat add sa Iₘ Tag t) → (z : @Address C cat add sa Iₘ t) →
      @Tagging.Matches C cat add sa Iₘ Tag (binary (@Binary.ofMonoidal C cat mul)) V t s z →
      @SumTree.eval C cat mul Tag V (@Tagging.expr C cat add sa Iₘ Tag t s) =
        @separateCoeff C cat add sa (binary (@Binary.ofMonoidal C cat mul)) Iₘ t z := by
  intro Iₘ t
  induction t with
  | unit => intro s z h; cases s; rfl
  | leaf a => intro s z h; cases s; exact h
  | fork a b ha hb =>
    intro s z h
    cases s with
    | fork l r =>
      exact congrArg₂ (@MonoidalCategoryStruct.tensorObj C cat mul.toMonoidalCategoryStruct)
        (ha l z.1 h.1) (hb r z.2 h.2)

theorem AssocMove.tagForward_matches {a b : DependentFubiniTree I} (p : AssocMove a b)
    (s : Tagging Tag a) (z : a.Address) (h : s.Matches (T:=T) V z) :
    (p.tagForward s).target.Matches (T:=T) V ((p.tagForward s).read z) := by
  induction p with
  | root _ _ _ =>
    cases s with | fork ab c =>
      cases ab with | fork a b =>
        exact ⟨h.1.1,h.1.2,h.2⟩
  | left f c ih =>
    cases s with | fork a c =>
      exact ⟨ih a z.1 h.1,h.2⟩
  | right c f ih =>
    cases s with | fork c a =>
      exact ⟨h.1,ih a z.2 h.2⟩

theorem AssocMove.tagBackward_matches {a b : DependentFubiniTree I} (p : AssocMove a b)
    (s : Tagging Tag b) (z : b.Address) (h : s.Matches (T:=T) V z) :
    (p.tagBackward s).target.Matches (T:=T) V ((p.tagBackward s).read z) := by
  induction p with
  | root _ _ _ =>
    cases s with | fork a bc =>
      cases bc with | fork b c =>
        exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩
  | left f c ih =>
    cases s with | fork a c =>
      exact ⟨ih a z.1 h.1,h.2⟩
  | right c f ih =>
    cases s with | fork c a =>
      exact ⟨h.1,ih a z.2 h.2⟩

theorem StructuralMove.tagForward_matches {a b : DependentFubiniTree I} (p : StructuralMove a b)
    (s : Tagging Tag a) (z : a.Address) (h : s.Matches (T:=T) V z) :
    (p.tagForward s).target.Matches (T:=T) V ((p.tagForward s).read z) := by
  induction p with
  | assoc f => exact f.tagForward_matches V s z h
  | swap a b => cases s with | fork a b => exact ⟨h.2,h.1⟩
  | eraseRight a =>
    cases s with | fork a u =>
      cases u
      exact h.1
  | left f c ih =>
    cases s with | fork a c =>
      exact ⟨ih a z.1 h.1,h.2⟩
  | right c f ih =>
    cases s with | fork c a =>
      exact ⟨h.1,ih a z.2 h.2⟩

theorem StructuralMove.tagBackward_matches {a b : DependentFubiniTree I} (p : StructuralMove a b)
    (s : Tagging Tag b) (z : b.Address) (h : s.Matches (T:=T) V z) :
    (p.tagBackward s).target.Matches (T:=T) V ((p.tagBackward s).read z) := by
  induction p with
  | assoc f => exact f.tagBackward_matches V s z h
  | swap a b => cases s with | fork b a => exact ⟨h.2,h.1⟩
  | eraseRight a => exact ⟨h,True.intro⟩
  | left f c ih =>
    cases s with | fork a c =>
      exact ⟨ih a z.1 h.1,h.2⟩
  | right c f ih =>
    cases s with | fork c a =>
      exact ⟨h.1,ih a z.2 h.2⟩

theorem StructuralPath.tagTransport_matches {a b : DependentFubiniTree I} (p : StructuralPath a b)
    (s : Tagging Tag a) (z : a.Address) (h : s.Matches (T:=T) V z) :
    (p.tagTransport s).target.Matches (T:=T) V ((p.tagTransport s).read z) := by
  induction p with
  | ident _ => exact h
  | next f g ih =>
    exact ih (f.tagForward s).target ((f.tagForward s).read z) (f.tagForward_matches V s z h)
  | prev f g ih =>
    exact ih (f.tagBackward s).target ((f.tagBackward s).read z) (f.tagBackward_matches V s z h)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
