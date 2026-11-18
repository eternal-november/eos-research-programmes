module
public import ContextualComposition.TaggedCorner
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedTripleFaces
open CategoryTheory CategoryTheory.Functor Opposite SpanApex MovingCoordinates MovingCell ProjectedCharts
section General
variable {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
theorem transportAlong {P Q : C ⥤ D} (e : P = Q) {x y : C} (a : x ⟶ y) (t : IsTransport (Q.map a)) : IsTransport (P.map a) := by subst Q; exact t
theorem composeCast {F G K : C ⥤ D} (q : D ⥤ E) (a : F ≅ G) (b : G ≅ K)
    (v : ∀ x, IsTransport (q.map (a.hom.app x))) (w : ∀ x, IsTransport (q.map (b.hom.app x))) (x : C) :
    IsTransport (q.map ((a ≪≫ b).hom.app x)) := by
  change IsTransport (q.map (a.hom.app x ≫ b.hom.app x)); rw [q.map_comp]; exact trans (v x) (w x)
theorem glueCast (K : C ⥤ D) (R : D ⥤ C) (k : R ⋙ K ≅ 𝟭 D) (F : D ⥤ E) (T : C ⥤ E) (b : K ⋙ F = T)
    (q : E ⥤ H) (p : D ⥤ H) (h : F ⋙ q = p) (v : ∀ x, IsTransport (p.map (k.hom.app x))) (x : D) :
    IsTransport (q.map ((glue K R k F T b).hom.app x)) := by
  apply composeCast
  · intro y; simp only [eqToIso.hom,eqToHom_app]; apply castMap
  · intro y; exact transportAlong h (k.hom.app y) (v y)
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
theorem bridgeCast (h : ∀ i, CutRead S Y i) (x : X S Y) : IsTransport ((proj S Y).map ((stageBridge S Y h).hom.app x)) :=
  composeCast _ (ChartRealization.gauge (MovingCell.L S Y) (MovingCell.left S Y)) _ (lCast S Y)
    (glueCast (MovingCoordinates.chart S Y).functor (read S Y) (recover S Y) (binaryStages S Y) (Sigma.desc (ChartRealization.refL S Y))
      (allRead S Y h) (proj S Y) (base S Y) (binaryOver S Y) (adjustCast S Y)) x
theorem bridgeVertical (h : ∀ i, CutRead S Y i) : SuffixCell.vertical (base S Y) (proj S Y) (leftOver S Y) (binaryOver S Y) (stageBridge S Y h).hom :=
  fun x => (bridgeCast S Y h x).choose_spec
end ContextualComposition.GrothendieckStep.TaggedTripleFaces
