module
public import ContextualComposition.PullLaws

/-! Base laws for the tagged evaluation operand of the all-length evaluation square.
The target constraints are transports along the equalities of the actual packed
presheaf; the source constraints are the maps of its separately chosen lifts. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedBaseLaws
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue CoproductSpan.All SumChange
universe b w u v
variable {B : Type b} [Category.{w} B]
namespace Zero
variable (Y : Bᵒᵖ ⥤ Cat.{v,u})
noncomputable def unit (A : B) : ZeroPower.pull Y (𝟙 A) ≅ 𝟭 _ :=
  isoWhiskerLeft (FibreTotal.into Y (𝟭 B) (𝟭 B) A)
    (isoWhiskerRight (Route.unitIso (choice Y) A) (FibreTotal.out Y (𝟭 B) (𝟭 B) A))
noncomputable def comp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    ZeroPower.pull Y (a ≫ b) ≅ ZeroPower.pull Y b ⋙ ZeroPower.pull Y a :=
  isoWhiskerLeft (FibreTotal.into Y (𝟭 B) (𝟭 B) E)
    (isoWhiskerRight (Route.compIso (choice Y) a b) (FibreTotal.out Y (𝟭 B) (𝟭 B) A))
theorem unitLaw (A : B) : Paste.UnitLaw (F := ZeroPower.eval Y A)
    (ZeroPower.baseSquare Y (𝟙 A)) (unit Y A).hom (eqToHom (strictUnit Y A)) :=
  fun x => NatTrans.congr_app (valueUnit Y A) ((FibreTotal.into Y (𝟭 B) (𝟭 B) A).obj x)
theorem compLaw {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (F := ZeroPower.eval Y A) (G := ZeroPower.eval Y D) (H := ZeroPower.eval Y E)
      (X := ZeroPower.pull Y a) (Y := ZeroPower.pull Y b) (W := ZeroPower.pull Y (a ≫ b))
      (X' := (Y.map a.op).toFunctor) (Y' := (Y.map b.op).toFunctor) (W' := (Y.map (a ≫ b).op).toFunctor)
      (ZeroPower.baseSquare Y (a ≫ b)) (ZeroPower.baseSquare Y a) (ZeroPower.baseSquare Y b)
      (comp Y a b).hom (eqToHom (strictComp Y a b)) :=
  fun x => NatTrans.congr_app (valueComp Y a b) ((FibreTotal.into Y (𝟭 B) (𝟭 B) E).obj x)
end Zero
variable {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) (Y : Bᵒᵖ ⥤ Cat.{w,b})
noncomputable def leafUnit (A : B) : (n : Nat) → leafPull R Y (𝟙 A) n ≅ 𝟭 _
  | 0 => Zero.unit Y A
  | n+1 => nativeId Y R n A
noncomputable def leafComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) : (n : Nat) →
    leafPull R Y (a ≫ b) n ≅ leafPull R Y b n ⋙ leafPull R Y a n
  | 0 => Zero.comp Y a b
  | n+1 => nativeComp Y R n a b
theorem leafUnitLaw (A : B) : (n : Nat) → Paste.UnitLaw (X := leafPull R Y (𝟙 A) n)
    (F := (component R Y A n).functor) (Y := ((Iterates.layer Q R Y n).map (𝟙 A).op).toFunctor)
    (componentBase R Y (𝟙 A) n) (leafUnit R Y A n).hom (eqToHom (strictUnit (Iterates.layer Q R Y n) A))
  | 0 => Zero.unitLaw Y A
  | n+1 => evalUnit R Y n A
theorem leafCompLaw {A D E : B} (a : A ⟶ D) (b : D ⟶ E) : (n : Nat) →
    Paste.CompLaw (X := leafPull R Y a n) (Y := leafPull R Y b n) (W := leafPull R Y (a ≫ b) n)
      (F := (component R Y A n).functor) (G := (component R Y D n).functor) (H := (component R Y E n).functor)
      (X' := ((Iterates.layer Q R Y n).map a.op).toFunctor)
      (Y' := ((Iterates.layer Q R Y n).map b.op).toFunctor)
      (W' := ((Iterates.layer Q R Y n).map (a ≫ b).op).toFunctor)
      (componentBase R Y (a ≫ b) n) (componentBase R Y a n) (componentBase R Y b n)
      (leafComp R Y a b n).hom (eqToHom (strictComp (Iterates.layer Q R Y n) a b))
  | 0 => Zero.compLaw Y a b
  | n+1 => evalComp R Y n a b
noncomputable def sourceUnit (A : B) : ZeroPower.Sum.map (leafPull R Y (𝟙 A)) ⟶ 𝟭 _ :=
  Sigma.natTrans fun n => whiskerRight (leafUnit R Y A n).hom
    (Sigma.incl (C := fun n => Total Y (CoproductSpan.leg (src R) (dst R) A n)) n)
noncomputable def sourceComp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    ZeroPower.Sum.map (leafPull R Y (a ≫ b)) ⟶ ZeroPower.Sum.map (leafPull R Y b) ⋙ ZeroPower.Sum.map (leafPull R Y a) :=
  Sigma.natTrans fun n => whiskerRight (leafComp R Y a b n).hom
    (Sigma.incl (C := fun n => Total Y (CoproductSpan.leg (src R) (dst R) A n)) n)

/-- The source edge correction used in the concrete forward square. -/
theorem sourceEq {A D : B} (a : A ⟶ D) :
    ZeroPower.Sum.map (SpanPull.componentPull (src R) (dst R) (SpanPull.All.parts R) Y a) =
      ZeroPower.Sum.map (leafPull R Y a) :=
  congrArg ZeroPower.Sum.map (SpanPull.All.pull_eq_leaf R Y a)

/-- Constraint compatibility across the two source presentations. Checking only
their functors would not justify using the same middle edge in a paste. -/
theorem sourceEq_unit (A : B) :
    eqToHom (sourceEq R Y (𝟙 A)) ≫ sourceUnit R Y A =
      PullLaws.taggedUnit (src R) (dst R) (SpanPull.All.parts R) Y A := by
  apply NatTrans.ext
  funext ⟨n,x⟩
  simp only [NatTrans.comp_app,eqToHom_app]
  cases n <;> exact Category.id_comp _
theorem sourceEq_comp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    eqToHom (sourceEq R Y (a ≫ b)) ≫ sourceComp R Y a b =
      PullLaws.taggedComp (src R) (dst R) (SpanPull.All.parts R) Y a b ≫
        eqToHom (congrArg₂ (· ⋙ ·) (sourceEq R Y b) (sourceEq R Y a)) := by
  apply NatTrans.ext
  funext ⟨n,x⟩
  simp only [NatTrans.comp_app,eqToHom_app]
  cases n <;> exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem packedUnitApp (A : B) (n : Nat) (x : (Iterates.layer Q R Y n).obj (op A)) :
    (eqToHom (Iterates.packedMap_id Q R Y (op A))).app ⟨n,x⟩ =
    (Iterates.inclusion Q R Y n (op A)).map ((eqToHom (strictUnit (Iterates.layer Q R Y n) A)).app x) := by
  simp only [eqToHom_app,eqToHom_map]; rfl
theorem packedCompApp {A D E : B} (a : A ⟶ D) (b : D ⟶ E) (n : Nat) (x : (Iterates.layer Q R Y n).obj (op E)) :
    (eqToHom (Iterates.packedMap_comp Q R Y b.op a.op)).app ⟨n,x⟩ =
    (Iterates.inclusion Q R Y n (op A)).map ((eqToHom (strictComp (Iterates.layer Q R Y n) a b)).app x) := by
  simp only [eqToHom_app,eqToHom_map]; rfl
theorem taggedUnitLaw (A : B) :
    Paste.UnitLaw (X := ZeroPower.Sum.map (leafPull R Y (𝟙 A)))
      (F := (ZeroPower.Sum.equiv (component R Y A)).functor) (Y := Iterates.packedMap Q R Y (𝟙 A).op)
      (taggedBase R Y (𝟙 A)) (sourceUnit R Y A) (eqToHom (Iterates.packedMap_id Q R Y (op A))) := by
  rintro ⟨n,x⟩
  rw [packedUnitApp]
  exact congrArg Sigma.SigmaHom.mk (leafUnitLaw R Y A n x)
theorem taggedCompLaw {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    Paste.CompLaw (X := ZeroPower.Sum.map (leafPull R Y a)) (Y := ZeroPower.Sum.map (leafPull R Y b))
      (W := ZeroPower.Sum.map (leafPull R Y (a ≫ b)))
      (F := (ZeroPower.Sum.equiv (component R Y A)).functor) (G := (ZeroPower.Sum.equiv (component R Y D)).functor)
      (H := (ZeroPower.Sum.equiv (component R Y E)).functor)
      (X' := Iterates.packedMap Q R Y a.op) (Y' := Iterates.packedMap Q R Y b.op)
      (W' := Iterates.packedMap Q R Y (a ≫ b).op)
      (taggedBase R Y (a ≫ b)) (taggedBase R Y a) (taggedBase R Y b)
      (sourceComp R Y a b) (eqToHom (Iterates.packedMap_comp Q R Y b.op a.op)) := by
  rintro ⟨n,x⟩
  rw [packedCompApp]
  exact congrArg Sigma.SigmaHom.mk (leafCompLaw R Y a b n x)
end ContextualComposition.GrothendieckStep.TaggedBaseLaws
