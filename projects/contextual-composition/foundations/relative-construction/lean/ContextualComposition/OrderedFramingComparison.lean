module
public import ContextualComposition.OrderedNativeFrameAction
public import ContextualComposition.ConstantGradeFraming

/-! Compare the ordered augmented calculation with the admitted-family
comma presentation of the general constant-content Set action. -/

@[expose] public section
namespace ContextualComposition.OrderedFramingComparison
open CategoryTheory NativeFinitePush ConstantCollectionFraming OrderedArityReflection
open OrderedNativeFraming OrderedNativeFrameAction
universe u v
set_option backward.isDefEq.respectTransparency false
variable {V : Type u} {K : Coeff.{u,v} V} (P : Push K) (I : V)
variable {A B : Type u}

structure Grade (P : Push K) (I : V) where
  data : Aug P I

instance : Category (Grade P I) where
  Hom p q := AugHom P p.data q.data
  id _ := AugHom.ident _
  comp := AugHom.comp
  id_comp := AugHom.ident_comp
  comp_id := AugHom.comp_ident
  assoc := AugHom.comp_assoc

def raw : Grade P I ⥤ Type u where
  obj p := ULift.{u} (Pos p.data)
  map f := TypeCat.ofHom (fun w => ⟨f.native.addr w.down⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

def content : Collection.{u} ⥤ (Type u ⥤ Type u) where
  obj := extF
  map := change
  map_id _ := rfl
  map_comp _ _ := rfl

variable (J : MorphismProperty (Type u)) [J.IsStableUnderBaseChange]

structure Admitted (A B : Type u) where
  op : Operation P I A B
  admitted : J (AdmittedContextFamily.projection (raw P I) (fun a => Grade.mk (op.ctx a)))

def liftTotal (F : Operation P I A B) :
    Total F ≅ AdmittedContextFamily.extent (raw P I) (fun a => Grade.mk (F.ctx a)) :=
  (show _ ≃ _ from ⟨fun z => ⟨z.1, ⟨z.2⟩⟩,fun z => ⟨z.1,z.2.down⟩,fun _ => rfl,fun _ => rfl⟩).toIso

theorem admitted_iff (F : Operation P I A B) : J (project F) ↔
    J (AdmittedContextFamily.projection (raw P I) (fun a => Grade.mk (F.ctx a))) := by
  constructor
  · exact J.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk (show
      (liftTotal P I F).inv ≫ project F = AdmittedContextFamily.projection (raw P I) (fun a => Grade.mk (F.ctx a)) ≫ 𝟙 A from rfl)))
  · exact J.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk (show
      (liftTotal P I F).hom ≫ AdmittedContextFamily.projection (raw P I) (fun a => Grade.mk (F.ctx a)) = project F ≫ 𝟙 A from rfl)))

instance : Category (Admitted P I J A B) where
  Hom p q := p.op ⟶ q.op
  id p := 𝟙 p.op
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

abbrev Mixed (A B : Type u) := ConstantGradeFraming.Mixed (raw P I) J content A B

def encode : Admitted P I J A B ⥤ Mixed P I J A B where
  obj F := ⟨⟨fun a => ⟨F.op.ctx a⟩,F.admitted⟩,F.op.collection,TypeCat.ofHom fun z => F.op.body z.1 z.2.down⟩
  map f := ⟨f.context,f.shape,by
    apply ConcreteCategory.hom_ext
    intro z
    exact f.body z.1 z.2.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def decode : Mixed P I J A B ⥤ Admitted P I J A B where
  obj F := ⟨⟨fun a => (F.left.grade a).data,F.right,fun a w => F.hom ⟨a,⟨w⟩⟩⟩,F.left.admitted⟩
  map f := ⟨f.left,f.right,fun a w => ConcreteCategory.congr_hom f.w ⟨a,⟨w⟩⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def equivalence : Admitted P I J A B ≌ Mixed P I J A B where
  functor := encode P I J
  inverse := decode P I J
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ f; simp; exact Square.ext rfl rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intro _ _ f; simp; exact Comma.hom_ext _ _ rfl rfl)

def frame (X : Type u) : Admitted P I J A B ⥤ Admitted P I J (X × A) (X × B) where
  obj F := ⟨frameOp X F.op, J.of_isPullback (AdmittedContextFamily.extension_pullback (raw P I)
      (fun a => Grade.mk (F.op.ctx a)) (TypeCat.ofHom (Prod.snd : X × A → A))) F.admitted⟩
  map := frameSquare X
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Strict agreement on all objects and morphisms of the admitted
comma presentation. Context aggregate maps survive the comparison. -/
theorem action_compares (X : Type u) : frame (A := A) (B := B) P I J X ⋙ encode P I J =
    encode P I J ⋙ ConstantGradeFraming.framed (raw P I) J content X := rfl

end ContextualComposition.OrderedFramingComparison
