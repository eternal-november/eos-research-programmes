module
public import ContextualComposition.AmbientRoutePaste
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientMateReindex
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction ContextadWeakWeight AmbientMateCalculus SpanApex BoundaryPaste
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B A D A' D' : Type u} [Category.{v} B] [Category.{v} A] [Category.{v} D] [Category.{v} A'] [Category.{v} D']
variable {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
variable (e : A ⥤ B) (d : D ⥤ B) (r : A ⥤ D) (l : r ⋙ d ⟶ e)
variable (U : A' ⥤ A) (V : D' ⥤ D) {e' : A' ⥤ B} {d' : D' ⥤ B} (u : U ⋙ e = e') (v : V ⋙ d = d')
abbrev pull (Y : Bᵒᵖ ⥤ Cat.{v,u}) := SpanPayload.totalMap Y U e u
theorem leafPull (Y : Bᵒᵖ ⥤ Cat.{v,u}) (U : A' ⥤ A) (e : A ⥤ B) {e' : A' ⥤ B} (u : U ⋙ e = e') : pull e U u Y ⋙ leafAt Y e = leafAt Y e' := by subst e'; rfl
theorem actionPull : pull e U u Y ⋙ atEndpoint a e = atEndpoint a e' ⋙ pull e U u Z := by
  apply fold_ext
  · apply (congrArg (pull e U u Y ⋙ ·) (actionGrade e (totalStrong a) (strongOver a))).trans
    apply (SpanPayload.total_projection Y U e u).trans
    exact ((congrArg (atEndpoint a e' ⋙ ·) (SpanPayload.total_projection Z U e u)).trans (congrArg (· ⋙ U) (actionGrade e' (totalStrong a) (strongOver a)))).symm
  · apply (congrArg (pull e U u Y ⋙ ·) (actionLeaf e (totalStrong a) (strongOver a))).trans
    apply (congrArg (· ⋙ totalStrong a) (leafPull Y U e u)).trans
    exact ((congrArg (atEndpoint a e' ⋙ ·) (leafPull Z U e u)).trans (actionLeaf e' (totalStrong a) (strongOver a))).symm
variable (s : A' ⥤ D') (l' : s ⋙ d' ⟶ e')
abbrev Square (Y : Bᵒᵖ ⥤ Cat.{v,u}) := restrict Y e' d' s l' ⋙ pull d V v Y = pull e U u Y ⋙ restrict Y e d r l
theorem tipPull (Y : Bᵒᵖ ⥤ Cat.{v,u}) (sq : Square e d r l U V u v s l' Y)
    (ll : ∀ z, Aligned (l'.app z) (l.app (U.obj z))) (x : Total Y e') :
    Aligned ((tip Y e' d' s l').app x) ((tip Y e d r l).app ((pull e U u Y).obj x)) := by
  apply ContextadUnitTotal.pureAlign Y (𝟭 B)
  · exact (Functor.congr_obj (leafPull Y V d v).symm _).trans (congrArg (leafAt Y d).obj (Functor.congr_obj sq x))
  · exact Functor.congr_obj (leafPull Y U e u).symm x
  · apply (ll _).trans
    exact ContextadPayloadModification.appChange l (Functor.congr_obj (SpanPayload.total_projection Y U e u).symm x)
  · exact pureId _
  · exact pureId _
theorem routesL (sq : Square e d r l U V u v s l' Y) :
    lRoute e' d' s l' a ⋙ pull d V v Z = pull e U u Y ⋙ lRoute e d r l a := by
  exact (congrArg (restrict Y e' d' s l' ⋙ ·) (actionPull a d V v).symm).trans (congrArg (· ⋙ atEndpoint a d) sq)
theorem routesR (sq : Square e d r l U V u v s l' Z) :
    rRoute e' d' s l' a ⋙ pull d V v Z = pull e U u Y ⋙ rRoute e d r l a := by
  exact (congrArg (atEndpoint a e' ⋙ ·) sq).trans (congrArg (· ⋙ restrict Z e d r l) (actionPull a e U u).symm)
theorem reindex (sy : Square e d r l U V u v s l' Y) (sz : Square e d r l U V u v s l' Z)
    (ll : ∀ z, Aligned (l'.app z) (l.app (U.obj z))) (x : Total Y e') :
    Aligned ((pull d V v Z).map ((q e' d' s l' a).app x)) ((q e d r l a).app ((pull e U u Y).obj x)) := by
  let t := (q e' d' s l' a).app x
  let k := (pull d V v Z).map t
  let y := (pull e U u Y).obj x
  let A := Functor.congr_obj (routesL a e d r l U V u v s l' sy) x
  let B := Functor.congr_obj (routesR a e d r l U V u v s l' sz) x
  let w := eqToHom A.symm ≫ k ≫ eqToHom B
  have tr : Aligned w k := AmbientDescentRecognition.trim _ _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
  have gr : Pure (gradeMap k) := pureOfAligned (NativeCube.functorAlign (SpanPayload.total_projection Z V d v) t) (pureMap V (weakGrade _ _ _ _ a x))
  have eq : w = (q e d r l a).app y := by
    apply cancelTip e d r l ((atEndpoint a e).obj y) _ _ (pureOfAligned (tr.map gradeProjection) gr) (weakGrade _ _ _ _ a y)
    let J := leafAt Z d
    have h := (tr.map J).trans (NativeCube.functorAlign (leafPull Z V d v) t)
    have tipZ := tipPull e d r l U V u v s l' Z sz ll ((atEndpoint a e').obj x)
    have tZ := tipZ.trans (ContextadPayloadModification.appChange (tip Z e d r l) (Functor.congr_obj (actionPull a e U u).symm x))
    exact (h.comp tZ.symm).trans ((factor e' d' s l' a x).trans (((tipPull e d r l U V u v s l' Y sy ll x).map _).trans (factor e d r l a y).symm))
  exact tr.symm.trans (NativeCube.ofEq eq)
end ContextualComposition.GrothendieckStep.AmbientMateReindex
