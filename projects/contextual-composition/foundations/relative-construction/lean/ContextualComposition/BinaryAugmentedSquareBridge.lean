module
public import ContextualComposition.BinaryNativeSquare

@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)

theorem NativeAugmentedIso.native_square_preserves_joint {I : C} {A B A' B' : Aug ℙ I}
    (e : NativeAugmentedIso A A') (d : NativeAugmentedIso B B')
    (p : AugHom ℙ A B) (q : Hom ℙ A'.base B'.base)
    (hs : p.native.comp d.hom.native = e.hom.native.comp q) :
    q.comp B'.ε = A'.ε := by
  have base : e.inv.native.comp e.hom.native = Hom.ident A'.base :=
    congrArg AugHom.native e.inv_hom
  have qeq : q = e.inv.native.comp (p.native.comp d.hom.native) := by
    rw [hs, ← Hom.comp_assoc, base, Hom.ident_comp]
  rw [qeq, Hom.comp_assoc, Hom.comp_assoc, d.hom.preserves, p.preserves, e.inv.preserves]

/-- Once the separate side is known to preserve the augmentation, the
same independently constructed joint side does too. No new native
arrow is substituted for the original joint one. -/
def NativeAugmentedIso.lift_square {I : C} {A B A' B' : Aug ℙ I}
    (e : NativeAugmentedIso A A') (d : NativeAugmentedIso B B')
    (p : AugHom ℙ A B) (q : Hom ℙ A'.base B'.base)
    (hs : p.native.comp d.hom.native = e.hom.native.comp q) :
    AugHom ℙ A' B' :=
  ⟨q, e.native_square_preserves_joint d p q hs⟩

theorem NativeAugmentedIso.lift_square_commutes {I : C} {A B A' B' : Aug ℙ I}
    (e : NativeAugmentedIso A A') (d : NativeAugmentedIso B B')
    (p : AugHom ℙ A B) (q : Hom ℙ A'.base B'.base)
    (hs : p.native.comp d.hom.native = e.hom.native.comp q) :
    p.comp d.hom = e.hom.comp (e.lift_square d p q hs) :=
  AugHom.ext hs

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
