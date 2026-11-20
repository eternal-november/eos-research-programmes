module
public import ContextualComposition.ContentCovariantGrothendieck
public import ContextualComposition.RepresentableComma
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentComma
open CategoryTheory CategoryTheory.Functor Opposite
open ContentCovariantGrothendieck
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B] (P : Endpoints.{u,u,u,u} Bᵒᵖ)
variable (A D : B)

abbrev Native := StructuredArrow A (dest P D)
abbrev Context := CostructuredArrow (P.extend (op D)) (op A)

def read : (Context P A D)ᵒᵖ ⥤ Native P A D where
  obj x := StructuredArrow.mk (Y := op x.unop.left) x.unop.hom.unop
  map t := StructuredArrow.homMk t.unop.left.op
    (congrArg Quiver.Hom.unop (CostructuredArrow.w t.unop))
  map_id x := by ext; rfl
  map_comp s t := by ext; rfl

def write : Native P A D ⥤ (Context P A D)ᵒᵖ where
  obj x := op (CostructuredArrow.mk (Y := x.right.unop) x.hom.op)
  map {x y} t :=
    Quiver.Hom.op (X := (CostructuredArrow.mk (Y := y.right.unop) y.hom.op))
      (Y := (CostructuredArrow.mk (Y := x.right.unop) x.hom.op))
      (CostructuredArrow.homMk t.right.unop (congrArg Quiver.Hom.op (StructuredArrow.w t)))
  map_id x := by
    apply Quiver.Hom.unop_inj
    apply CostructuredArrow.hom_ext
    rfl
  map_comp {x y z} s t := by
    apply Quiver.Hom.unop_inj
    apply CostructuredArrow.hom_ext
    rfl

theorem readWrite (x : Native P A D) : (read P A D).obj ((write P A D).obj x) = x := by
  obtain ⟨⟨⟨⟩⟩,p,f⟩ := x
  rfl
theorem writeRead (x : (Context P A D)ᵒᵖ) : (write P A D).obj ((read P A D).obj x) = x := by
  obtain ⟨⟨p,⟨⟨⟩⟩,f⟩⟩ := x
  rfl

def iso : CategoryTheory.IsoCat ((Context P A D)ᵒᵖ) (Native P A D) where
  functor := read P A D
  inverse := write P A D
  unit_eq := by
    fapply Functor.ext
    · intro x; exact (writeRead P A D x).symm
    · intro x y t
      have a := writeRead P A D x
      have b := writeRead P A D y
      -- The constant comma leg is forced; the grade is the actual input.
      cases x with | op x =>
        cases y with | op y =>
          obtain ⟨p,⟨⟨⟩⟩,f⟩ := x
          obtain ⟨q,⟨⟨⟩⟩,g⟩ := y
          simp only [Functor.id_map,eqToHom_refl,Category.id_comp,Category.comp_id]
          apply Quiver.Hom.unop_inj; ext; rfl
  counit_eq := by
    fapply Functor.ext
    · exact readWrite P A D
    · intro x y t
      obtain ⟨⟨⟨⟩⟩,p,f⟩ := x
      obtain ⟨⟨⟨⟩⟩,q,g⟩ := y
      simp only [Functor.id_map,eqToHom_refl,Category.id_comp,Category.comp_id]
      ext; rfl

theorem gradeRetained {x y : (Context P A D)ᵒᵖ} (t : x ⟶ y) :
  ((read P A D).map t).right = t.unop.left.op := rfl

end ContextualComposition.GrothendieckStep.ContentComma
