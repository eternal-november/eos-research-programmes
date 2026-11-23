module
public import ContextualComposition.RelativeTensorOuterRowNative

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.OuterRow
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vD uD vT uT vY uY
variable {B : Type uB} {D : Type uD} [Category.{vB} B] [Category.{vD} D]

/-- Include source and target when comparing arrows between two differently presented functors. -/
structure TypedArrow (E : Type*) [Category* E] where
  source : E
  target : E
  arrow : source ⟶ target

def pack {E : Type*} [Category* E] {a b : E} (f : a ⟶ b) : TypedArrow E := ⟨a,b,f⟩

theorem pack_injective {E : Type*} [Category* E] {a b : E} {f g : a ⟶ b} (h : pack f = pack g) : f = g := by
  cases h
  rfl

variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

private def insertPacked (F : LocallyDiscrete D ⥤ᵖ Cat.{vT,uT}) (d : D) (y : Y.obj ⟨op d⟩)
    (p : TypedArrow (F.obj ⟨d⟩)) : TypedArrow (Tensor F Y) :=
  pack (atVertex (F := F) Y d y p.arrow)

variable (T : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vT,uT}))
variable {a b c : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b) (v : b ⟶ c)
variable {A : LocallyDiscrete D ⥤ᵖ Cat.{vT,uT}} {C : LocallyDiscrete D ⥤ᵖ Cat.{vT,uT}}
variable (E : row T a.as.unop ⟶ A) (J : row T c.as.unop ⟶ C)
variable {s t : A ⟶ C} (m : s ⟶ t)

private theorem lift_source (z : Tensor (row T a.as.unop) Y) :
    pack ((mapFirst (G := Y) J).map (((rightInner T Y).mapComp u v).hom.toNatTrans.app z)) =
      insertPacked Y C z.as.mid z.as.second (pack ((J.app ⟨z.as.mid⟩).toFunctor.map
        (((T.obj ⟨z.as.mid⟩).mapComp u v).hom.toNatTrans.app z.as.first))) := by
  have h := source_comp_vertex Y T u v z
  have k := First.on_native J (((T.obj ⟨z.as.mid⟩).mapComp u v).hom.toNatTrans.app z.as.first) (𝟙 z.as.second)
  exact congrArg pack ((congrArg (mapFirst (G := Y) J).map h).trans k)

private theorem lift_target (z : Tensor (row T a.as.unop) Y) :
    pack ((First.mapCell (G := Y) m.as).app ((mapFirst (G := Y) E).obj z)) =
      insertPacked Y C z.as.mid z.as.second (pack ((m.as.app ⟨z.as.mid⟩).toNatTrans.app ((E.app ⟨z.as.mid⟩).toFunctor.obj z.as.first))) := rfl

/-- Transport the outer compositor by checking its component on the underlying middle object in each column. -/
theorem normalize_from_columns
    (columns : ∀ (d : D) (p : (T.obj ⟨d⟩).obj a), pack ((J.app ⟨d⟩).toFunctor.map (((T.obj ⟨d⟩).mapComp u v).hom.toNatTrans.app p)) =
      pack ((m.as.app ⟨d⟩).toNatTrans.app ((E.app ⟨d⟩).toFunctor.obj p))) (z : Tensor (row T a.as.unop) Y) :
    pack ((mapFirst (G := Y) J).map (((rightInner T Y).mapComp u v).hom.toNatTrans.app z)) =
      pack ((First.mapCell (G := Y) m.as).app ((mapFirst (G := Y) E).obj z)) :=
  (lift_source Y T u v J z).trans ((congrArg (insertPacked Y C z.as.mid z.as.second) (columns z.as.mid z.as.first)).trans
    (lift_target Y T E m z).symm)

end ContextualComposition.RelativeTensor.Iterated.OuterRow
