module
public import ContextualComposition.RelativeTensorUnitRowMap
public import ContextualComposition.RelativeTensorRowStrongSquares

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vY uY
variable {B : Type u} [Category.{v} B]

private theorem insertedTransport {L R T : Type*} [Category* L] [Category* R] [Category* T]
    (J : L × R ⥤ T) {x x' : L} (f : x ⟶ x') (h : ∃ e, f = eqToHom e) (y : R) :
    ∃ e, J.map (productMap f (𝟙 y)) = eqToHom e := by
  obtain ⟨rfl,rfl⟩ := h
  exact ⟨rfl,J.map_id (x,y)⟩

private theorem discreteTransport {A : Type*} {p q : Discrete A} (h : p ⟶ q) : ∃ e, h = eqToHom e :=
  ⟨congrArg Discrete.mk (Discrete.eq_of_hom h), Discrete.hom_eq⟩

variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

theorem unitRow_source_id (a : LocallyDiscrete Bᵒᵖ) (z : (rightInner (unitModule B) Y).obj a) :
    ∃ e, ((rightInner (unitModule B) Y).mapId a).hom.toNatTrans.app z = eqToHom e := by
  obtain ⟨⟨j,p,y⟩⟩ := z
  have h := right_unit (b := a.as.unop) (unitModule B) Y j p y
  obtain ⟨e,he⟩ := insertedTransport (insertion (row (unitModule B) a.as.unop) Y j) _
    (discreteTransport (((column (unitModule B) j).mapId a).hom.toNatTrans.app p)) y
  exact ⟨e,h.trans he⟩

theorem unitRow_source_comp {a b c : LocallyDiscrete Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (z : (rightInner (unitModule B) Y).obj a) :
    ∃ e, ((rightInner (unitModule B) Y).mapComp f g).hom.toNatTrans.app z = eqToHom e := by
  obtain ⟨⟨j,p,y⟩⟩ := z
  have h := right_comp (unitModule B) Y g.as.unop f.as.unop j p y
  obtain ⟨e,he⟩ := insertedTransport (insertion (row (unitModule B) c.as.unop) Y j) _
    (discreteTransport (((column (unitModule B) j).mapComp f g).hom.toNatTrans.app p)) y
  exact ⟨e,h.trans he⟩

theorem unitRow_packed_transport {A C : Type*} [Category* A] [Category* C] (E : A ⥤ C)
    {a b : A} {c d : C} (s : a ⟶ b) (t : c ⟶ d) (hs : ∃ e, s = eqToHom e) (ht : ∃ e, t = eqToHom e) (p : E.obj a = c) :
    OuterRow.pack (E.map s) = OuterRow.pack t := by
  obtain ⟨rfl,rfl⟩ := hs
  obtain ⟨rfl,rfl⟩ := ht
  subst c
  exact congrArg OuterRow.pack (E.map_id a)

/-- A strictly commuting family into an ordinary Cat diagram is strong when each source unit and compositor is an object transport. -/
def strongToOrdinary {I : Type*} [Category* I] (F : LocallyDiscrete I ⥤ᵖ Cat.{vY,uY}) (G : I ⥤ Cat.{vY,uY})
    (E : ∀ a, F.obj a ⥤ G.obj a.as)
    (sq : ∀ {a b} (f : a ⟶ b), (F.map f).toFunctor ⋙ E b = E a ⋙ (G.map f.as).toFunctor)
    (one : ∀ a z, ∃ e, (F.mapId a).hom.toNatTrans.app z = eqToHom e)
    (two : ∀ {a b c} (f : a ⟶ b) (g : b ⟶ c) z, ∃ e, (F.mapComp f g).hom.toNatTrans.app z = eqToHom e) :
    F ⟶ G.toPseudofunctor' :=
  OuterRow.strongOfSquares F G.toPseudofunctor' E sq
    (fun a z => unitRow_packed_transport (E a) _ _ (one a z)
      ⟨_, Cat.eqToHom_app _ _ (G.map_id a.as) ((E a).obj z)⟩ (Functor.congr_obj (sq (𝟙 a)) z))
    (fun {a _ _} f g z => unitRow_packed_transport (E _) _ _ (two f g z)
      ⟨_, Cat.eqToHom_app _ _ (G.map_comp f.as g.as) ((E a).obj z)⟩ (Functor.congr_obj (sq (f ≫ g)) z))

end ContextualComposition.RelativeTensor.Iterated
