module
public import ContextualComposition.RelativeTensorPentagonPorts
public import ContextualComposition.RelativeTensorPentagonInteriorConcrete
public import ContextualComposition.RelativeTensorFourBalanceB
public import ContextualComposition.RelativeTensorPentagonOuterBalance

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

private theorem compare_packed {S T : Type*} [Category* S] [Category* T] {H K : S ⥤ T}
    (p : ∀ z, H.obj z = K.obj z) {z z' : S} (g : z ⟶ z') (e : OuterRow.pack (H.map g) = OuterRow.pack (K.map g)) :
    CompareAt (H := H) (K := K) (fun z => eqToIso (p z)) g := by
  have aux {a b c d : T} (f : a ⟶ b) (g : c ⟶ d) (l : a = c) (r : b = d) (k : OuterRow.pack f = OuterRow.pack g) :
      f ≫ eqToHom r = eqToHom l ≫ g := by
    subst c; subst d
    rw [OuterRow.pack_injective k]
    simp
  exact aux (H.map g) (K.map g) (p z) (p z') e

/-- It suffices to check an object predicate on the native vertices of the tensor. -/
private theorem onInsertedObjects {I : Type*} [Category* I] (F : LocallyDiscrete I ⥤ᵖ Cat.{vX,uX})
    (G : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{vM,uM}) (P : Tensor F G → Prop)
    (h : ∀ (b : I) (x : F.obj ⟨b⟩) (m : G.obj ⟨op b⟩), P ((insertion F G b).obj (x,m))) (z : Tensor F G) : P z := by
  obtain ⟨⟨b,x,m⟩⟩ := z
  exact h b x m

/-- Extend the comparison from primitive middle vertices while the two functors are arbitrary. -/
private theorem compareMiddle {T : Type*} [Category* T] (H K : farLeft X M N Y ⥤ T)
    (q : ∀ z, H.obj z = K.obj z) {c c' : C} {d : D} (v : c ⟶ c') (n : (column N d).obj ⟨op c'⟩) (y : Y.obj ⟨op d⟩)
    (h : ∀ (b : B) (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩),
      let a := farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y
      OuterRow.pack (E := T) (H.map a) = OuterRow.pack (E := T) (K.map a))
    (z : Tensor X (column M c)) : CompareAt (H := H) (K := K) (fun w => eqToIso (q w)) (farLeftBalanceC X M N Y v z n y) := by
  let P (w : Tensor X (column M c)) := CompareAt (H := H) (K := K) (fun a => eqToIso (q a)) (farLeftBalanceC X M N Y v w n y)
  apply onInsertedObjects X (column M c) P ?_ z
  intro b x m
  exact compare_packed (H := H) (K := K) q (farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y) (h b x m)

section Compare
variable (V : rightInner (middleComposite M N) Y ⟶ rightInner M (rightInner N Y))
variable (q : ∀ z, (twoStep X M N Y).functor.obj z = ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V).obj z)
include q in
/-- Identify the proposed route once, then use the actual port and both outer balance calculations on the quotient. -/
private theorem assembled (candidate : farLeft X M N Y ⥤ farRight X M N Y)
    (route : ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V) = candidate)
    (components : ∀ b : B, Second.part V b = OuterRow.direct M N Y ⟨op b⟩)
    (ports : ∀ {a b : B} (u : a ⟶ b) (z : (rightInner (middleComposite M N) Y).obj ⟨op b⟩), ∃ h, (Second.port V u z).hom = eqToHom h)
    (native : ∀ {b : B} {c : C} {d : D} {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩}
      {n n' : (column N d).obj ⟨op c⟩} {y y' : Y.obj ⟨op d⟩} (f : x ⟶ x') (g : m ⟶ m') (h : n ⟶ n') (i : y ⟶ y'),
      OuterRow.pack (E := farRight X M N Y) ((twoStep X M N Y).functor.map (leftFourNative X M N Y f g h i)) = OuterRow.pack (E := farRight X M N Y) (candidate.map (leftFourNative X M N Y f g h i)))
    (central : ∀ {b : B} {c c' : C} {d : D} (v : c ⟶ c') (x : X.obj ⟨b⟩) (m : (column M c).obj ⟨op b⟩) (n : (column N d).obj ⟨op c'⟩) (y : Y.obj ⟨op d⟩),
      let a := farLeftBalanceC X M N Y v ((insertion X (column M c) b).obj (x,m)) n y
      OuterRow.pack (E := farRight X M N Y) ((twoStep X M N Y).functor.map a) = OuterRow.pack (E := farRight X M N Y) (candidate.map a)) : (twoStep X M N Y).functor = candidate := by
  subst candidate
  apply extFourGenerators (H := (twoStep X M N Y).functor) (K := ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V)) X M N Y q
  constructor
  · intro b c d x x' m m' n n' y y' f g h i
    exact compare_packed (H := (twoStep X M N Y).functor) (K := ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V)) q (leftFourNative X M N Y f g h i) (native f g h i)
  · intro a b c d u x m n y
    let z := middleRowPoint M N Y m n y
    exact balanceB_compare_of_port (a := a) (b := b) (c := c) (d := d) X M N Y u x m n y V q
      ((Functor.congr_obj (components b) z).trans (direct_row_point M N Y m n y)) (ports u z)
  · intro c c' d v z n y
    exact compareMiddle X M N Y (twoStep X M N Y).functor
      ((firstPentagonEdge X M N Y ⋙ associate X (middleComposite M N) Y) ⋙ mapSecond (F := X) V)
      q v n y (fun _ x m => central v x m n y) z
  · intro d e w z y
    exact Pentagon.balanceD_test_of_components (d := d) (e := e) X M N Y w y V components q z
end Compare

/-- At the represented outer endpoints the two independently constructed fourfold reassociations have equal forward functors on the whole quotient. -/
theorem pentagon : (twoStep X M N Y).functor = (threeStep X M N Y).functor := by
  let V := OuterRow.whisker M N Y
  have comps (b : B) : Second.part V b = OuterRow.direct M N Y ⟨op b⟩ := rfl
  apply assembled X M N Y V (route_objects X M N Y V comps) (threeStep X M N Y).functor
    (threeStep_functor X M N Y).symm comps (fun u z => whisker_port M N Y u z)
  · intro b c d x x' m m' n n' y y' f g h i
    have short := congrArg (OuterRow.pack (E := farRight X M N Y)) (twoStep_native X M N Y f g h i)
    exact short.trans (Pentagon.threeStep_native_packed X M N Y f g h i).symm
  · intro b c c' d v x m n y
    have short := congrArg (OuterRow.pack (E := farRight X M N Y)) (twoStep_middle X M N Y v x m n y)
    exact short.trans (Pentagon.threeStep_middle_packed X M N Y v x m n y).symm

end ContextualComposition.RelativeTensor.Iterated
