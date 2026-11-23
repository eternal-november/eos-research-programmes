module
public import ContextualComposition.OrderedShapeReassociation
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.End

/-! Ordered substitution as a monoidal operation on actual collection
grades. Execution order gives the product of C then D as Sub(D,C).
Faithfulness of the polynomial realization transfers the endofunctor
pentagon and triangle to the native, arity-preserving grade maps. -/

@[expose] public section
namespace ContextualComposition.OrderedSubstitutionCoherence
open CategoryTheory MonoidalCategory OrderedArityReflection ConstantCollectionFraming
open OrderedShapeReassociation OrderedLeafReadout
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] endofunctorMonoidalCategory

def realize : Collection.{u} ⥤ (Type u ⥤ Type u) where
  obj := extF
  map := change
  map_id _ := rfl
  map_comp _ _ := rfl

instance : realize.{u}.Faithful where
  map_injective {C D} {_ _} h := change_injective (C := C) (D := D) h

def leftBody (C : Collection.{u}) : extF (sub C OrderedArityReflection.identity) ≅ extF C :=
  (substitutionIso C OrderedArityReflection.identity).symm ≪≫ Functor.isoWhiskerRight unaryIso.symm _ ≪≫ Functor.leftUnitor _

def rightBody (C : Collection.{u}) : extF (sub OrderedArityReflection.identity C) ≅ extF C :=
  (substitutionIso OrderedArityReflection.identity C).symm ≪≫ Functor.isoWhiskerLeft _ unaryIso.symm ≪≫ Functor.rightUnitor _

theorem read_unary_list {B : Type u} (p : Point OrderedArityReflection.identity B) :
    listBody p = [readUnary p] := by
  conv_lhs => rw [← unary_read p]
  rfl

theorem left_leaves (C : Collection.{u}) : PreservesLeaves (leftBody C).hom := by
  intro B q
  let p := unpack q
  rw [← pack_unpack q]
  change listBody ((extF C).map (TypeCat.ofHom readUnary) (unpack (pack p))) = _
  rw [unpack_pack,listBody_pack]
  have em : listBody ((extF C).map (TypeCat.ofHom readUnary) p) = (listBody p).map readUnary := by
    simp only [listBody,List.map_ofFn]; rfl
  rw [em]
  generalize listBody p = xs
  induction xs <;> simp_all [read_unary_list]

theorem right_leaves (C : Collection.{u}) : PreservesLeaves (rightBody C).hom := by
  intro B q
  let p := unpack q
  rw [← pack_unpack q]
  change listBody (readUnary (unpack (pack p))) = _
  rw [unpack_pack,listBody_pack,read_unary_list]
  simp
  rfl

def tensorator (X Y : Collection.{u}) : realize.obj X ⊗ realize.obj Y ≅ realize.obj (sub Y X) :=
  substitutionIso Y X

theorem reverse_leaves {C D : Collection.{u}} (t : extF C ≅ extF D) (lh : PreservesLeaves t.hom) : PreservesLeaves t.inv :=
  fun B p => (lh B (t.inv.app B p)).symm.trans (congrArg listBody ((t.app B).toEquiv.apply_symm_apply p))

instance : MonoidalCategoryStruct Collection.{u} where
  tensorObj X Y := sub Y X
  tensorHom f g := subMap g f
  whiskerLeft X {_ _} f := subMap f (𝟙 X)
  whiskerRight f X := subMap (𝟙 X) f
  tensorUnit := OrderedArityReflection.identity
  associator X Y Z := gradeIso (reassociate Z Y X).symm (reverse_leaves _ (reassociate_leaves Z Y X))
  leftUnitor X := gradeIso (leftBody X) (left_leaves X)
  rightUnitor X := gradeIso (rightBody X) (right_leaves X)

def inducing : Monoidal.InducingFunctorData realize.{u} where
  μIso := tensorator
  εIso := unaryIso
  whiskerLeft_eq X {Y Z} f := by
    apply NatTrans.ext; funext B; apply ConcreteCategory.hom_ext; intro q
    rw [← pack_unpack q]
    change _ = pack ((change f).app _ (unpack (pack (unpack q))))
    rw [unpack_pack]; rfl
  whiskerRight_eq {X X'} f Y := by
    apply NatTrans.ext; funext B; apply ConcreteCategory.hom_ext; intro q
    rw [← pack_unpack q]
    change _ = pack ((extF Y).map ((change f).app B) (unpack (pack (unpack q))))
    rw [unpack_pack]; rfl
  tensorHom_eq {X X' Y Y'} f g := by
    apply NatTrans.ext; funext B; apply ConcreteCategory.hom_ext; intro q
    rw [← pack_unpack q]
    change _ = pack (((change f ◫ change g).app B) (unpack (pack (unpack q))))
    rw [NatTrans.hcomp_app,unpack_pack]; rfl
  associator_eq X Y Z := by
    refine (gradeIso_hom (reassociate Z Y X).symm _).trans ?_
    simp only [Iso.trans_hom,Iso.symm_hom,MonoidalCategory.tensorIso_hom,Iso.refl_hom,tensorHom_id,id_tensorHom]
    apply NatTrans.ext; funext B; apply ConcreteCategory.hom_ext; intro q
    rfl
  leftUnitor_eq X := by
    refine (gradeIso_hom (leftBody X) _).trans ?_
    simp only [Iso.trans_hom,Iso.symm_hom,MonoidalCategory.tensorIso_hom,Iso.refl_hom,tensorHom_id]
    apply NatTrans.ext; funext B; apply ConcreteCategory.hom_ext; intro q
    rfl
  rightUnitor_eq X := by
    refine (gradeIso_hom (rightBody X) _).trans ?_
    simp only [Iso.trans_hom,Iso.symm_hom,MonoidalCategory.tensorIso_hom,Iso.refl_hom,id_tensorHom]
    apply NatTrans.ext; funext B; apply ConcreteCategory.hom_ext; intro q
    rfl

instance monoidal : MonoidalCategory Collection.{u} := Monoidal.induced realize inducing

def realizationMonoidal : realize.{u}.CoreMonoidal := Monoidal.fromInducedCoreMonoidal realize inducing

theorem realization_tensor (C D : Collection.{u}) :
    realizationMonoidal.μIso C D = substitutionIso D C := rfl

end ContextualComposition.OrderedSubstitutionCoherence
