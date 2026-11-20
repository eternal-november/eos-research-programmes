module
public import ContextualComposition.StrictTelFunctorial
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelCategories
open CategoryTheory SpanApex NativeBlocks
open NativeBlocks.Nested (Over)
open StrictSpanAlgebra StrictSpanCart StrictTelOperations StrictTelMapLaws StrictTelAlgebra
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
variable {B : Type b} [Category.{max b w} B]

theorem bothId (U V : Span (B := B)) :
    both (StrictSpanAlgebra.id U) (StrictSpanAlgebra.id V) = StrictSpanAlgebra.id _ := by
  apply overExt
  exact Strict.uniq _ _ _ _ rfl rfl

theorem bothComp {U V W U' V' W' : Span (B := B)} (F : Over U V) (F' : Over U' V')
    (G : Over V W) (G' : Over V' W') :
    both (StrictSpanAlgebra.comp F G) (StrictSpanAlgebra.comp F' G') =
      StrictSpanAlgebra.comp (both F F') (both G G') := by
  apply overExt
  exact Strict.uniq _ _ _ _ rfl rfl

theorem monId {U : Span (B := B)} (M : Ops U) :
    Multiplicative (StrictSpanAlgebra.id U) (M := M) (N := M) where
  unit := Functor.comp_id _
  tensor := by rw [bothId]; exact (Functor.comp_id _).trans (Functor.id_comp _).symm

theorem monComp {U V W : Span (B := B)} {M : Ops U} {N : Ops V} {O : Ops W}
    {F : Over U V} {G : Over V W} (h : Multiplicative F (M := M) (N := N))
    (k : Multiplicative G (M := N) (N := O)) :
    Multiplicative (StrictSpanAlgebra.comp F G) (M := M) (N := O) where
  unit := (congrArg (· ⋙ G.functor) h.unit).trans k.unit
  tensor := by
    change (M.tensor.functor ⋙ F.functor) ⋙ G.functor =
      (both (StrictSpanAlgebra.comp F G) (StrictSpanAlgebra.comp F G)).functor ⋙ O.tensor.functor
    rw [h.tensor,bothComp]
    change (both F F).functor ⋙ (N.tensor.functor ⋙ G.functor) = _
    rw [k.tensor]
    rfl

structure Carrier (B : Type b) [Category.{max b w} B] where
  P : Endpoints.{b,max b w,b,max b w} B
  S : P.Split

abbrev classOf (X : Carrier B) := power X.S 1

structure Ctx (B : Type b) [Category.{max b w} B] where
  carrier : Carrier B
  data : Contextad (classOf carrier)
structure Alg (B : Type b) [Category.{max b w} B] where
  carrier : Carrier B
  data : Algebra carrier.S

structure CtxHom (X Y : Ctx B) where
  f : Over (classOf X.carrier) (classOf Y.carrier)
  cart : CartesianMap f
  law : Multiplicative f (M := X.data.operations) (N := Y.data.operations)
structure AlgHom (X Y : Alg B) where
  f : Over (classOf X.carrier) (classOf Y.carrier)
  cart : CartesianMap f
  law : AlgebraMap X.carrier.S Y.carrier.S f X.data.action Y.data.action

theorem ctxExt {X Y : Ctx B} {f g : CtxHom X Y} (h : f.f.functor = g.f.functor) : f = g := by
  obtain ⟨f,p,q⟩ := f; obtain ⟨g,r,s⟩ := g
  cases overExt h; rfl
theorem algExt {X Y : Alg B} {f g : AlgHom X Y} (h : f.f.functor = g.f.functor) : f = g := by
  obtain ⟨f,p,q⟩ := f; obtain ⟨g,r,s⟩ := g
  cases overExt h; rfl

instance contextCategory : Category (Ctx B) where
  Hom := CtxHom
  id X := ⟨StrictSpanAlgebra.id _,identity _,monId (M := X.data.operations)⟩
  comp f g := ⟨StrictSpanAlgebra.comp f.f g.f,compose f.cart g.cart,monComp f.law g.law⟩
  id_comp _f := ctxExt (Functor.id_comp _)
  comp_id _f := ctxExt (Functor.comp_id _)
  assoc _f _g _h := ctxExt (Functor.assoc _ _ _)

instance algebraCategory : Category (Alg B) where
  Hom := AlgHom
  id X := ⟨StrictSpanAlgebra.id _,identity _,by
    change X.data.action.functor ⋙ 𝟭 _ = (StrictTelMap.map X.carrier.S X.carrier.S (StrictSpanAlgebra.id _)).functor ⋙ _
    rw [StrictTelFunctorial.mapId]
    exact (Functor.comp_id _).trans (Functor.id_comp _).symm⟩
  comp {X Y Z} f g := ⟨StrictSpanAlgebra.comp f.f g.f,compose f.cart g.cart,by
    change (X.data.action.functor ⋙ f.f.functor) ⋙ g.f.functor =
      (StrictTelMap.map X.carrier.S Z.carrier.S (StrictSpanAlgebra.comp f.f g.f)).functor ⋙ Z.data.action.functor
    rw [f.law,StrictTelFunctorial.mapComp X.carrier.S Y.carrier.S Z.carrier.S]
    change (StrictTelMap.map X.carrier.S Y.carrier.S f.f).functor ⋙
      (Y.data.action.functor ⋙ g.f.functor) = _
    rw [g.law]
    rfl⟩
  id_comp _f := algExt (Functor.id_comp _)
  comp_id _f := algExt (Functor.comp_id _)
  assoc _f _g _h := algExt (Functor.assoc _ _ _)

noncomputable def decode : Alg B ⥤ Ctx B where
  obj X := ⟨X.carrier,read X.carrier.S X.data⟩
  map {X Y} f := ⟨f.f,f.cart,map_read X.carrier.S Y.carrier.S f.f _ _ f.law⟩

def encode : Ctx B ⥤ Alg B where
  obj X := ⟨X.carrier,write X.carrier.S X.data⟩
  map {X Y} f := ⟨f.f,f.cart,eval_natural X.carrier.S Y.carrier.S f.f _ _ f.law⟩

theorem readWriteObj (X : Ctx B) : (encode ⋙ decode).obj X = X :=
  congrArg (Ctx.mk X.carrier) (readWrite X.carrier.S X.data)
theorem writeReadObj (X : Alg B) : (decode ⋙ encode).obj X = X :=
  congrArg (Alg.mk X.carrier) (writeRead X.carrier.S X.data)

/-- The underlying directed apex functor of each map is unchanged. -/
theorem encode_hom {X Y : Ctx B} (f : X ⟶ Y) : ((encode (B := B)).map f).f.functor = f.f.functor := rfl
theorem decode_hom {X Y : Alg B} (f : X ⟶ Y) : ((decode (B := B)).map f).f.functor = f.f.functor := rfl

theorem ctxHExt {X X' Y Y' : Ctx B} (hx : X = X') (hy : Y = Y')
    (f : CtxHom X Y) (g : CtxHom X' Y') (h : HEq f.f.functor g.f.functor) : HEq f g := by
  subst X'; subst Y'; exact heq_of_eq (ctxExt (eq_of_heq h))
theorem algHExt {X X' Y Y' : Alg B} (hx : X = X') (hy : Y = Y')
    (f : AlgHom X Y) (g : AlgHom X' Y') (h : HEq f.f.functor g.f.functor) : HEq f g := by
  subst X'; subst Y'; exact heq_of_eq (algExt (eq_of_heq h))

/-- Strict algebra maps on native carriers and contextad maps with identity
comparisons form isomorphic ordinary categories. This does not identify
maps whose monoid comparisons are only invertible. -/
noncomputable def isomorphism : IsoCat (Alg B) (Ctx B) where
  functor := decode
  inverse := encode
  unit_eq := by
    symm
    apply Functor.hext writeReadObj
    intro X Y f
    exact algHExt (writeReadObj X) (writeReadObj Y) _ f HEq.rfl
  counit_eq := by
    apply Functor.hext readWriteObj
    intro X Y f
    exact ctxHExt (readWriteObj X) (readWriteObj Y) _ f HEq.rfl

end ContextualComposition.GrothendieckStep.StrictTelCategories
