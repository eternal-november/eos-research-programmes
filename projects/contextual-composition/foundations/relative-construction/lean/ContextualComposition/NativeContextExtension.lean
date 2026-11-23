module
public import ContextualComposition.NativeContextAdmissibility
public import ContextualComposition.NativeDependentPairFubini
@[expose] public section

/-! Pointwise whole native dependent maps and the extension
reassociation, natural without any restriction on their carrier maps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {I : C} {A B : Type u}

set_option backward.isDefEq.respectTransparency false in
def extensionMap {P Q : IndexedNativeFamily (C:=C) A I} (p : P ⟶ Q) : P.Extension → Q.Extension :=
  fun z => ⟨z.1,⟨(p z.1).native.addr z.2.down⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem extensionMap_ident (P : IndexedNativeFamily (C:=C) A I) : extensionMap (𝟙 P) = id :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem extensionMap_comp {P Q R : IndexedNativeFamily (C:=C) A I} (p : P ⟶ Q) (q : Q ⟶ R) :
    extensionMap (p ≫ q) = extensionMap q ∘ extensionMap p :=
  rfl

noncomputable def reindexFunctor (f : B → A) :
    IndexedNativeFamily (C:=C) A I ⥤ IndexedNativeFamily (C:=C) B I where
  obj P := P.reindex f
  map p x := p (f x)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The arrows do not acquire a membership condition in the display
map class when reindexing is restricted to admissible objects. -/
noncomputable def admissibleReindex (J : NativeProjectionClass.{u}) (f : B → A) :
    Admissible (C:=C) (I:=I) (A:=A) J ⥤ Admissible (C:=C) (I:=I) (A:=B) J where
  obj P := ⟨P.obj.reindex f,reindex_admissible J P.obj P.property f⟩
  map p := ObjectProperty.homMk ((reindexFunctor f).map p.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
variable {P P' : IndexedNativeFamily (C:=C) A I}
variable {Q : IndexedNativeFamily (C:=C) P.Extension I} {Q' : IndexedNativeFamily (C:=C) P'.Extension I}
variable (p : P ⟶ P')
variable (q : ∀ z : P.Extension, AugHom (standardPush (C:=C)) (Q z) (Q' (extensionMap p z)))

noncomputable def accumulateMap : accumulate R L J P Q ⟶ accumulate R L J P' Q' :=
  fun x =>
    NativeDependentPairHom.accumulate R L J N NL hl
      (⟨p x,fun i => q ⟨x,⟨i⟩⟩⟩ : NativeDependentPairHom (P.pairAt Q x) (P'.pairAt Q' x))

def extensionMapOver : Q.Extension → Q'.Extension :=
  fun z => ⟨extensionMap p z.1,⟨(q z.1).native.addr z.2.down⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem accumulateExtension_natural :
    accumulateExtension R L J P' Q' ∘ extensionMap (accumulateMap R L J N NL hl p q) =
    extensionMapOver p q ∘ accumulateExtension R L J P Q := by
  funext z
  let x := z.1
  let g : NativeDependentPairHom (P.pairAt Q x) (P'.pairAt Q' x) :=
    ⟨p x,fun i => q ⟨x,⟨i⟩⟩⟩
  exact congrArg (fun b : (P'.pairAt Q' x).Branch => (⟨⟨x,⟨b.1⟩⟩,⟨b.2⟩⟩ : Q'.Extension))
    (g.read_addr R L J N NL hl z.2.down)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
