module
public import ContextualComposition.RelativeTensorThreeStep

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.Pentagon
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

open OuterRow (TypedArrow pack)
set_option Elab.async false
set_option maxHeartbeats 45000

/-- Apply a functor to an arrow together with its endpoints. -/
def mapped {A E : Type*} [Category* A] [Category* E] (F : A ⥤ E) (p : TypedArrow A) : TypedArrow E :=
  pack (F.map p.arrow)

section Binary
universe w k u v u' v'
variable {I : Type k} [Category.{w} I] (F : LocallyDiscrete I ⥤ᵖ Cat.{v,u})
variable (G : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{v',u'})
private def inserted (b : I) (f : TypedArrow (F.obj ⟨b⟩)) (r : TypedArrow (G.obj ⟨op b⟩)) : TypedArrow (Tensor F G) :=
  pack ((insertion F G b).map (productMap f.arrow r.arrow))

private theorem onPair (G' : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{v',u'}) (V : G ⟶ G') (b : I)
    (P : G.obj ⟨op b⟩ ⥤ G'.obj ⟨op b⟩) (e : Second.part V b = P)
    (f : TypedArrow (F.obj ⟨b⟩)) (r : TypedArrow (G.obj ⟨op b⟩)) (q : TypedArrow (G'.obj ⟨op b⟩)) (h : mapped P r = q) :
    mapped (mapSecond (F := F) V) (inserted F G b f r) = inserted F G' b f q := by
  subst P; subst q
  exact congrArg pack (Second.on_native (F := F) (G := G) (G' := G') (i := b) V f.arrow r.arrow)
private theorem pack_application {J L : Type*} [Category* J] [Category* L] (A : J ⥤ L) {x y : J} (f : x ⟶ y) : pack (A.map f) = mapped A (pack f) := rfl

private theorem composePacked {J L R : Type*} [Category* J] [Category* L] [Category* R] (A : J ⥤ L) (B : L ⥤ R)
    (p : TypedArrow J) (q : TypedArrow L) (r : TypedArrow R) (h : mapped A p = q) (k : mapped B q = r) :
    mapped (A ⋙ B) p = r := (congrArg (mapped B) h).trans k
end Binary

universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

section Central
variable {b : B} {c c' : C} {d : D} (v : c ⟶ c') (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩)
variable (n : (column N d).obj ⟨op c'⟩) (y : Y.obj ⟨op d⟩)

/-- The right-associated image of the native middle balance, keeping both endpoints. -/
theorem finalWhisker_middle_packed :
    mapped (mapSecond (F := X) (OuterRow.whisker M N Y)) (pack (innerRightMiddleBalance X M N Y v x m n y)) =
      pack (finalMiddleBalance X M N Y v x m n y) := by
  let r : TypedArrow (OuterRow.source M N Y ⟨op b⟩) := pack ((insertM (middleComposite M N) Y b d).map
    (productMap (balancing (row M b) (column N d) v m n).hom (𝟙 y)))
  let q : TypedArrow (OuterRow.target M N Y ⟨op b⟩) := pack (balancing (row M b) (rightInner N Y) v m ((insertM N Y c' d).obj (n,y))).hom
  have h : mapped (OuterRow.direct M N Y ⟨op b⟩) r = q := congrArg pack (lastRow_middle M N Y v m n y)
  exact onPair X (rightInner (middleComposite M N) Y) (rightInner M (rightInner N Y)) (OuterRow.whisker M N Y) b
    (OuterRow.direct M N Y ⟨op b⟩) rfl (pack (𝟙 x)) r q h

theorem threeStep_middle_packed :
    pack ((threeStep X M N Y).functor.map (farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y)) =
      pack (finalMiddleBalance X M N Y v x m n y) := by
  let T := mapSecond (F := X) (OuterRow.whisker M N Y)
  let p : TypedArrow (farLeft X M N Y) := pack (farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y)
  let q : TypedArrow (innerRight X M N Y) := pack (innerRightMiddleBalance X M N Y v x m n y)
  let r : TypedArrow (farRight X M N Y) := pack (finalMiddleBalance X M N Y v x m n y)
  have first : mapped (firstTwoEdges X M N Y).functor p = q := congrArg (pack (E := innerRight X M N Y)) (firstTwo_middle X M N Y v x m n y)
  have last : mapped T q = r := finalWhisker_middle_packed X M N Y v x m n y
  have route : (threeStep X M N Y).functor = (firstTwoEdges X M N Y).functor ⋙ T := rfl
  have seq : mapped ((firstTwoEdges X M N Y).functor ⋙ T) p = r := composePacked (J := farLeft X M N Y) (L := innerRight X M N Y) (R := farRight X M N Y) (firstTwoEdges X M N Y).functor T p q r first last
  have reorganized : mapped (threeStep X M N Y).functor p = r := Eq.trans (congrArg (fun (F : farLeft X M N Y ⥤ farRight X M N Y) => mapped F p) route) seq
  exact (pack_application (threeStep X M N Y).functor (farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y)).trans reorganized

theorem threeStep_middle :
    (threeStep X M N Y).functor.map (farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y) =
      finalMiddleBalance X M N Y v x m n y := by
  apply OuterRow.pack_injective
  exact threeStep_middle_packed X M N Y v x m n y
end Central
section Native
variable {b : B} {c : C} {d : D} {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩}
variable {n n' : (column N d).obj ⟨op c⟩} {y y' : Y.obj ⟨op d⟩}
variable (f : x ⟶ x') (g : m ⟶ m') (h : n ⟶ n') (i : y ⟶ y')

/-- Computation of the last whisker on all four varying native arrows, with endpoints included. -/
theorem finalWhisker_native_packed :
    mapped (mapSecond (F := X) (OuterRow.whisker M N Y)) (pack (innerRightNative X M N Y f g h i)) =
      pack (rightFourNative X M N Y f g h i) := by
  let r : TypedArrow (OuterRow.source M N Y ⟨op b⟩) := pack ((insertM (middleComposite M N) Y b d).map
    (productMap ((insertion (row M b) (column N d) c).map (productMap g h)) i))
  let q : TypedArrow (OuterRow.target M N Y ⟨op b⟩) := pack ((insertM M (rightInner N Y) b c).map
    (productMap g ((insertM N Y c d).map (productMap h i))))
  have hr : mapped (OuterRow.direct M N Y ⟨op b⟩) r = q := congrArg pack (lastRow_native M N Y g h i)
  exact onPair X (rightInner (middleComposite M N) Y) (rightInner M (rightInner N Y)) (OuterRow.whisker M N Y) b
    (OuterRow.direct M N Y ⟨op b⟩) rfl (pack f) r q hr

theorem threeStep_native_packed :
    pack ((threeStep X M N Y).functor.map (leftFourNative X M N Y f g h i)) = pack (rightFourNative X M N Y f g h i) := by
  let T := mapSecond (F := X) (OuterRow.whisker M N Y)
  let p : TypedArrow (farLeft X M N Y) := pack (leftFourNative X M N Y f g h i)
  let q : TypedArrow (innerRight X M N Y) := pack (innerRightNative X M N Y f g h i)
  let r : TypedArrow (farRight X M N Y) := pack (rightFourNative X M N Y f g h i)
  have first : mapped (firstTwoEdges X M N Y).functor p = q := congrArg (pack (E := innerRight X M N Y)) (firstTwo_native X M N Y f g h i)
  have last : mapped T q = r := finalWhisker_native_packed X M N Y f g h i
  have route : (threeStep X M N Y).functor = (firstTwoEdges X M N Y).functor ⋙ T := rfl
  have seq : mapped ((firstTwoEdges X M N Y).functor ⋙ T) p = r := composePacked (J := farLeft X M N Y) (L := innerRight X M N Y) (R := farRight X M N Y) (firstTwoEdges X M N Y).functor T p q r first last
  have reorganized : mapped (threeStep X M N Y).functor p = r := Eq.trans (congrArg (fun (F : farLeft X M N Y ⥤ farRight X M N Y) => mapped F p) route) seq
  exact (pack_application (threeStep X M N Y).functor (leftFourNative X M N Y f g h i)).trans reorganized

theorem threeStep_native :
    (threeStep X M N Y).functor.map (leftFourNative X M N Y f g h i) = rightFourNative X M N Y f g h i := by
  apply OuterRow.pack_injective
  exact threeStep_native_packed X M N Y f g h i
end Native

end ContextualComposition.RelativeTensor.Iterated.Pentagon
