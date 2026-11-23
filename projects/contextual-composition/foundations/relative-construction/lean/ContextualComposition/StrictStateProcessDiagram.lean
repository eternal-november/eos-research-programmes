module

public import ContextualComposition.DirectedStateNativeFaithfulness
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-! The actual strict hom-process bifunctor induced by pure input and output state actions. All native two-cells act by ordinary bicategorical whiskering. -/

@[expose] public section
namespace ContextualComposition.StrictStateProcessDiagram

open CategoryTheory CategoryTheory.Bicategory Opposite DirectedStateBalance
universe w v u j k
variable {H : Type u} [Bicategory.{w,v} H] [Strict H]
set_option backward.isDefEq.respectTransparency false

abbrev pre {A B : H} (f : A ⟶ B) (D : H) := (precomposing A B D).obj f
abbrev post (A : H) {B D : H} (g : B ⟶ D) := (postcomposing A B D).obj g

theorem pre_id (A B : H) : pre (𝟙 A) B = 𝟭 _ :=
  Functor.ext_of_iso (leftUnitorNatIso A B) (fun _ => Strict.id_comp _)
    (fun x => congrArg Iso.hom (Strict.leftUnitor_eqToIso x))

theorem post_id (A B : H) : post A (𝟙 B) = 𝟭 _ :=
  Functor.ext_of_iso (rightUnitorNatIso A B) (fun _ => Strict.comp_id _)
    (fun x => congrArg Iso.hom (Strict.rightUnitor_eqToIso x))

theorem pre_comp {A B C : H} (f : A ⟶ B) (g : B ⟶ C) (D : H) :
    pre (f ≫ g) D = pre g D ⋙ pre f D :=
  Functor.ext_of_iso (associatorNatIsoRight f g D) (fun x => Strict.assoc f g x)
    (fun x => congrArg Iso.hom (Strict.associator_eqToIso f g x))

theorem post_comp (A : H) {B C D : H} (f : B ⟶ C) (g : C ⟶ D) :
    post A f ⋙ post A g = post A (f ≫ g) :=
  Functor.ext_of_iso (associatorNatIsoLeft A f g) (fun x => Strict.assoc x f g)
    (fun x => congrArg Iso.hom (Strict.associator_eqToIso x f g))

theorem pre_post {A B C D : H} (f : A ⟶ B) (g : C ⟶ D) :
    pre f C ⋙ post A g = post B g ⋙ pre f D :=
  Functor.ext_of_iso (associatorNatIsoMiddle f g) (fun x => Strict.assoc f x g)
    (fun x => congrArg Iso.hom (Strict.associator_eqToIso f x g))

abbrev act {A A' B B' : H} (f : A' ⟶ A) (g : B ⟶ B') := pre f B ⋙ post A' g

theorem act_comp {A A' A'' B B' B'' : H} (l : A' ⟶ A) (l' : A'' ⟶ A') (r : B ⟶ B') (r' : B' ⟶ B'') :
    act (l' ≫ l) (r ≫ r') = act l r ⋙ act l' r' := by
  unfold act
  rw [pre_comp, ← post_comp]
  exact congrArg (fun f => pre l B ⋙ f ⋙ post A'' r') (pre_post l' r)

variable {S : Type j} [Category.{k} S] (L R : S ⥤ H)

def homDiagram : Sᵒᵖ × S ⥤ Cat.{w,v} where
  obj p := Cat.of (L.obj p.1.unop ⟶ R.obj p.2)
  map f := (act (L.map f.1.unop) (R.map f.2)).toCatHom
  map_id p := by
    apply congrArg Functor.toCatHom
    change pre (L.map (𝟙 _)) _ ⋙ post _ (R.map (𝟙 _)) = _
    rw [L.map_id,R.map_id,pre_id,post_id]; rfl
  map_comp f g := by
    apply congrArg Functor.toCatHom
    change act (L.map (g.1.unop ≫ f.1.unop)) (R.map (f.2 ≫ g.2)) = _
    rw [L.map_comp,R.map_comp]
    exact act_comp _ _ _ _

/-- Native faithfulness for the strict process instance, including when two state maps have the same pure image. -/
theorem faithful (i : S) : (insertion (strict (homDiagram L R)) i).Faithful :=
  DirectedStateNativeFaithfulness.faithful _ i

end ContextualComposition.StrictStateProcessDiagram
