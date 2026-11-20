import ContextualComposition.AmbientCoherentObserver
import ContextualComposition.ContextadCoherentDetection
import ContextualComposition.ContextadInsideCoordinates
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks
namespace CentralProbe
noncomputable section
set_option backward.isDefEq.respectTransparency false
inductive O | pt
instance : Groupoid O where
  Hom _ _ := Bool
  id _ := false
  comp a b := xor a b
  inv a := a
  id_comp := by intro _ _ f; cases f <;> rfl
  comp_id := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl
  inv_comp := by intro _ _ f; cases f <;> rfl
  comp_inv := by intro _ _ f; cases f <;> rfl
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of O)
  extend a := (Functor.const _).obj a
  lift f := { app := fun _ => f }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
def bit {K : Type*} [Category* K] {e : K ⥤ Nat} {x y : Total P.grades e} (f : x ⟶ y) : Bool := payloadMap f
theorem castBit {x y : O} (h : x = y) : (eqToHom h : x ⟶ y) = false := by cases h; rfl
theorem bitId {K : Type*} [Category* K] {e : K ⥤ Nat} (x : Total P.grades e) : bit (𝟙 x) = false := by
  obtain ⟨h,t⟩ := WeightedCells.totalPureId P.grades e x
  exact t.trans (castBit h)
theorem bitComp {K : Type*} [Category* K] {e : K ⥤ Nat} {x y z : Total P.grades e} (f : x ⟶ y) (g : y ⟶ z) :
    bit (f ≫ g) = xor (bit f) (bit g) := by
  unfold bit; rw [payload_comp]
  rw [castBit (comp_target (Y := P.grades) (e := e) (gradeMap f) (gradeMap g) (payload P.grades e z))]
  exact congrArg (xor (payloadMap f)) (Bool.xor_false _)
theorem gradeExt {x y : Apex P} {f g : x ⟶ y} (h : bit f = bit g) : f=g := by
  apply (homEquiv _ _).injective
  apply Sigma.ext (Subsingleton.elim _ _)
  exact heq_of_eq h
def grade : (power S 2).apex ⥤ Apex P where
  obj x := pair _ _ ((power S 2).source.obj x) O.pt
  map f := arrow ((power S 2).source.map f) (xor (bit (gradeMap f)) (bit f))
  map_id x := by apply gradeExt; change xor (bit (gradeMap (𝟙 x))) (bit (𝟙 x)) = _; rw [grade_id,bitId,bitId,bitId]; rfl
  map_comp f g := by
    apply gradeExt
    change xor (bit (gradeMap f ≫ gradeMap g)) (bit (f ≫ g)) = bit (_ ≫ _)
    rw [bitComp,bitComp,bitComp]
    change xor (xor _ _) (xor _ _) = xor (xor (bit (gradeMap f)) (bit f)) (xor (bit (gradeMap g)) (bit g))
    cases bit (gradeMap f) <;> cases bit (gradeMap g) <;> cases bit f <;> cases bit g <;> rfl
def m : ContextadTotal.Native S where
  grade := grade
  over := rfl
  delta := {app := fun _ => 𝟙 _}
  cart {x y} f _ := by
    let h : O.pt ⟶ O.pt := xor (bit (gradeMap f)) (bit f)
    have : IsIso (payloadMap (grade.map f)) := (inferInstance : IsIso h)
    exact ContextadCartesian.cart_of_payload _ _ (grade.map f)
def d : ContextadUnit.Data P where
  grade _ := O.pt
  discharge _ := 𝟙 _
  reindex _ := rfl
  square _ := Subsingleton.elim _ _
end
end CentralProbe
namespace CentralProbe
open ContextadRoutes ContextadSchedule ContextadLawTransport ContextadNativeLaws ContextadOuterCharts NativeAssoc FibreValue TelescopeSquares
noncomputable section
set_option backward.isDefEq.respectTransparency false
theorem alignedBit {K : Type*} [Category* K] {e : K ⥤ Nat} {x y x' y' : Total P.grades e} {f : x ⟶ y} {g : x' ⟶ y'} (h : Aligned f g) : bit f = bit g := by
  obtain ⟨rfl,rfl,k⟩ := h; simp at k; rw [k]
theorem pureBit {K : Type*} [Category* K] {e : K ⥤ Nat} {x y : Total P.grades e} (f : x ⟶ y) (h : Pure (payloadMap f)) : bit f = false := h.choose_spec.trans (castBit _)
theorem eqBit {K : Type*} [Category* K] {F G : K ⥤ Apex P} (e : F=G) {x y : K} (h : x ⟶ y) : bit (F.map h) = bit (G.map h) := alignedBit (NativeCube.functorAlign e h)
theorem snocBit {i j : Nat} (f : Map S i j) {x y : (power S (i+1)).apex} (h : x ⟶ y) :
    bit ((last S j).map ((suffix f).grade.map h)) = bit ((last S i).map h) := by
  have k := congrArg bit ((snocArrow f).naturality h)
  rw [bitComp,bitComp,pureBit _ (snocPure f x),pureBit _ (snocPure f y)] at k
  simpa using k
theorem headBit {i} (f : Map S i 1) {x y : (power S (i+1)).apex} (h : x ⟶ y) :
    bit ((front S 1).map ((suffix f).grade.map h)) = bit (f.grade.map ((front S i).map h)) := eqBit (snocHead f) h
theorem inLeftBit {i} (f : Map S i 1) {x y : (power S (1+i)).apex} (h : x ⟶ y) :
    bit ((front S 1).map ((inside 1 f).grade.map h)) = bit ((blocks S 1 i).first.map h) := eqBit (inHead 1 f) h
theorem inRightBit {i} (f : Map S i 1) {x y : (power S (1+i)).apex} (h : x ⟶ y) :
    bit ((last S 1).map ((inside 1 f).grade.map h)) = bit (f.grade.map ((blocks S 1 i).rest.map h)) :=
  eqBit ((congrArg ((inside 1 f).grade ⋙ ·) (tailOne (S := S) 1).symm).trans (inTail 1 f)) h
theorem readTensor {x y : (power S 2).apex} (h : x ⟶ y) : bit (m.grade.map h) = xor (bit ((front S 1).map h)) (bit ((last S 1).map h)) := rfl
theorem readUnit {x y : Nat} (h : x ⟶ y) : bit ((insert S d).grade.map h) = false := rfl
theorem leftMap {x y : (power S 1).apex} (h : x ⟶ y) : bit ((comp (leftUnit d) (tensor m)).grade.map h) = bit h := by
  change bit (m.grade.map ((suffix (insert S d)).grade.map h)) = _
  rw [readTensor,headBit,snocBit,readUnit,Bool.false_xor]; rfl
theorem rightMap {x y : (power S 1).apex} (h : x ⟶ y) : bit ((comp (rightUnit d) (tensor m)).grade.map h) = bit h := by
  change bit (m.grade.map ((inside 1 (insert S d)).grade.map h)) = _
  rw [readTensor,inLeftBit,inRightBit,readUnit]; simp only [Bool.xor_false]; rfl
theorem assocMap {x y : (power S 3).apex} (h : x ⟶ y) :
    bit ((comp (firstTwo m) (tensor m)).grade.map h) = bit ((comp (lastTwo m) (tensor m)).grade.map h) := by
  change bit (m.grade.map ((suffix (tensor m)).grade.map h)) = bit (m.grade.map ((inside 1 (tensor m)).grade.map h))
  rw [readTensor,readTensor,headBit,snocBit,inLeftBit,inRightBit]
  change xor (bit (m.grade.map ((front S 2).map h))) (bit ((last S 2).map h)) =
    xor (bit ((blocks S 1 2).first.map h)) (bit (m.grade.map ((blocks S 1 2).rest.map h)))
  rw [readTensor,readTensor,ContextadDisjointCut.tail₁]
  change xor (xor _ _) _ = xor (bit ((front S 1).map ((front S 2).map h))) (xor (bit ((last S 1).map ((front S 2).map h))) (bit ((last S 2).map h)))
  exact Bool.xor_assoc .. 
theorem baseEq {n} (p q : Map S n 1) (x) : (left P).obj (p.grade.obj x) = (left P).obj (q.grade.obj x) :=
  (Functor.congr_obj p.over x).trans (Functor.congr_obj q.over x).symm
def signIso {n} (p q : Map S n 1) (c : Bool) (x) : p.grade.obj x ≅ q.grade.obj x where
  hom := arrow (eqToHom (baseEq p q x)) c
  inv := arrow (eqToHom (baseEq p q x).symm) c
  hom_inv_id := by apply gradeExt; rw [bitComp,bitId]; change xor c c = false; cases c <;> rfl
  inv_hom_id := by apply gradeExt; rw [bitComp,bitId]; change xor c c = false; cases c <;> rfl
def signed {n} (p q : Map S n 1) (c : Bool) (maps : ∀ {x y} (f : x ⟶ y), bit (p.grade.map f) = bit (q.grade.map f)) : Cell p q where
  grade := NatIso.ofComponents (signIso p q c) (fun {x y} f => by
    apply gradeExt
    exact (bitComp (p.grade.map f) (signIso p q c y).hom).trans ((congrArg (xor · c) (maps f)).trans
      ((Bool.xor_comm _ _).trans (bitComp (signIso p q c x).hom (q.grade.map f)).symm)))
  source x := ⟨baseEq p q x,rfl⟩
  endpoint := NatTrans.ext (funext fun _ => Subsingleton.elim _ _)
def constraints (l r s : Bool) : Constraints d m :=
  ⟨signed _ _ l (fun h => leftMap h), signed _ _ r (fun h => rightMap h),signed _ _ s (fun h => assocMap h)⟩
end
end CentralProbe
namespace CentralProbe
open ContextadRoutes ContextadSchedule ContextadLawTransport ContextadNativeLaws ContextadOuterCharts NativeAssoc FibreValue TelescopeSquares
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws ContextadDisjointCut ContextadAppendCells ContextadInsideCells
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
abbrev HasBit {n} {p q : Map S n 1} (a : Cell p q) (c : Bool) := ∀ x, bit (a.grade.hom.app x) = c
theorem totalPureBit {x y : Apex P} {f : x ⟶ y} (h : Pure f) : bit f = false := by
  obtain ⟨rfl,rfl⟩ := h; exact bitId _
theorem castBitCell {n} {p q : Map S n 1} (e : p=q) : HasBit (castCell e) false := by cases e; intro x; exact bitId _
theorem pasteBit {n} {p q r : Map S n 1} {a : Cell p q} {b : Cell q r} {c d} (h : HasBit a c) (k : HasBit b d) : HasBit (thenCell a b) (xor c d) :=
  fun x => (bitComp (a.grade.hom.app x) (b.grade.hom.app x)).trans (congrArg₂ xor (h x) (k x))
theorem beforeBit {i j} {p q : Map S i 1} {a : Cell p q} {c} (h : HasBit a c) (r : Map S j i) : HasBit (before a r) c := fun x => h (r.grade.obj x)
theorem outBit {i} {p q : Map S i 1} {a : Cell p q} {c} (h : HasBit a c) : HasBit (after (suffixCell a) (tensor m)) c := by
  intro x; change bit (m.grade.map ((suffixCell a).grade.hom.app x)) = _; rw [readTensor]
  cases i <;>
    exact (congrArg₂ xor (congrArg bit (WeightedCells.weightGrade P.grades _ _ a.grade a.endpoint x)) (pureBit _ (WeightedCells.weightPayloadPure P.grades _ _ a.grade a.endpoint x))).trans
      ((congrArg (xor · false) (h _)).trans (Bool.xor_false _))
theorem insideBit {i} {p q : Map S i 1} {a : Cell p q} {c} (h : HasBit a c) : HasBit (after (insideCell 1 a) (tensor m)) c := by
  intro x; change bit (m.grade.map ((insideCell 1 a).grade.hom.app x)) = _; rw [readTensor]
  have s := totalPureBit (prefixPure 1 a x)
  have e := (eqBit (tailOne (S := S) 1).symm ((insideCell 1 a).grade.hom.app x)).trans (alignedBit (restAligned 1 a x))
  exact (congrArg₂ xor s (e.trans (h _))).trans (Bool.false_xor _)
abbrev M := tensor m
theorem exBit (x) : bit ((exchange M M m.cart).hom.app x) = false := by
  have l := alignedBit (leftTip M M x)
  have z : bit (m.grade.map ((move M).app x)) = false := rfl
  have r := (alignedBit (rightTip M M x)).trans (pureBit _ (snocPure M _))
  have k := congrArg bit (exchangeFac M M m.cart x)
  rw [bitComp,r,l,Bool.xor_false] at k
  exact k.trans z
theorem crossed : HasBit (after (disjoint M M m.cart) M) false := by
  intro x; change bit (m.grade.map ((assembled M M m.cart).hom.app x)) = _; rw [readTensor]
  have a := totalPureBit (assembledHead M M m.cart x)
  have b := (congrArg bit (assembledTip M M m.cart x)).trans (exBit x)
  exact (congrArg₂ xor a b).trans rfl
def c := constraints true false true
theorem assocSign : HasBit c.assoc true := fun _ => rfl
theorem lSign : HasBit c.left true := fun _ => rfl
theorem rSign : HasBit c.right false := fun _ => rfl
theorem nativeTriangle : TriangleLaw d m c := by
  let T := canonicalTriangle d m c
  have t : HasBit (composite (triLong d m c T)) false :=
    pasteBit (castBitCell _) (pasteBit (beforeBit assocSign _) (pasteBit (castBitCell _) (pasteBit (insideBit lSign) (castBitCell _))))
  have u : HasBit (composite (triShort d m c)) false := outBit rSign
  intro x; exact gradeExt ((t x).trans (u x).symm)
theorem longOdd : HasBit (composite (pentLong d m c (canonicalPentagon d m c))) true :=
  pasteBit (outBit assocSign) (pasteBit (castBitCell _) (pasteBit (beforeBit assocSign _) (pasteBit (castBitCell _) (insideBit assocSign))))
theorem linkNeutral : HasBit (canonicalPentagon d m c).fourFive false :=
  pasteBit (castBitCell (compAssoc (wide M) (inside 1 M) M).symm) (pasteBit crossed (castBitCell (compAssoc (inside 2 M) (suffix M) M)))
theorem shortEven : HasBit (composite (pentShort d m c (canonicalPentagon d m c))) false := by
  have start : HasBit (canonicalPentagon d m c).start false := castBitCell (pentStartRoute d m c)
  have finish : HasBit (canonicalPentagon d m c).finish false := castBitCell (pentEndRoute d m c)
  have fourth : HasBit (pent4 d m c).cell true := beforeBit assocSign (suffix (firstTwo m))
  have fifth : HasBit (pent5 d m c).cell true := beforeBit assocSign (inside 2 M)
  exact pasteBit start (pasteBit fourth (pasteBit linkNeutral (pasteBit fifth finish)))
def row₄ : (power S 4).apex := pair _ _ (pair _ _ (pair _ _ (pair _ _ (0:Nat) O.pt) O.pt) O.pt) O.pt
theorem notNativePentagon : ¬ PentagonLaw d m c := by
  intro h
  have e := (longOdd row₄).symm.trans ((congrArg bit (h row₄)).trans (shortEven row₄))
  cases e
end
end CentralProbe

namespace CentralProbe
open ContextualComposition.GrothendieckStep AmbientObserverRead
open CategoryTheory
noncomputable section
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks
open ContextadRoutes ContextadSchedule ContextadLawTransport ContextadNativeLaws ContextadOuterCharts NativeAssoc FibreValue TelescopeSquares
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws ContextadDisjointCut ContextadAppendCells ContextadInsideCells
def positive := constraints true true false
theorem passAssoc : HasBit positive.assoc false := fun _ => rfl
theorem passLeft : HasBit positive.left true := fun _ => rfl
theorem passRight : HasBit positive.right true := fun _ => rfl
theorem passTriangle : TriangleLaw d m positive := by
  let T := canonicalTriangle d m positive
  have t : HasBit (composite (triLong d m positive T)) true :=
    pasteBit (castBitCell _) (pasteBit (beforeBit passAssoc _) (pasteBit (castBitCell _) (pasteBit (insideBit passLeft) (castBitCell _))))
  have u : HasBit (composite (triShort d m positive)) true := outBit passRight
  intro x; exact gradeExt ((t x).trans (u x).symm)
theorem longClear : HasBit (composite (pentLong d m positive (canonicalPentagon d m positive))) false :=
  pasteBit (outBit passAssoc) (pasteBit (castBitCell _) (pasteBit (beforeBit passAssoc _) (pasteBit (castBitCell _) (insideBit passAssoc))))
theorem neutralLink : HasBit (canonicalPentagon d m positive).fourFive false :=
  pasteBit (castBitCell (compAssoc (wide M) (inside 1 M) M).symm) (pasteBit crossed (castBitCell (compAssoc (inside 2 M) (suffix M) M)))
theorem shortClear : HasBit (composite (pentShort d m positive (canonicalPentagon d m positive))) false := by
  have start : HasBit (canonicalPentagon d m positive).start false := castBitCell (pentStartRoute d m positive)
  have finish : HasBit (canonicalPentagon d m positive).finish false := castBitCell (pentEndRoute d m positive)
  have fourth : HasBit (pent4 d m positive).cell false := beforeBit passAssoc (suffix (firstTwo m))
  have fifth : HasBit (pent5 d m positive).cell false := beforeBit passAssoc (inside 2 M)
  exact pasteBit start (pasteBit fourth (pasteBit neutralLink (pasteBit fifth finish)))
theorem passPentagon : PentagonLaw d m positive := fun x => gradeExt ((longClear x).trans (shortClear x).symm)
theorem nativeGood : Coherent d m positive := ⟨passTriangle,passPentagon⟩
noncomputable def actualGood : AmbientCoherentPseudomonad.Data S := AmbientCoherentPseudomonad.build d m positive nativeGood
theorem actualTriangleEverywhere (X : AmbientBicategory.Obj.{0,0} Nat) : AmbientHorizontalDiagrams.Triangle S d m c X := AmbientTriangle.original X d m c nativeTriangle
theorem actualPentagonFails : ¬ AmbientHorizontalDiagrams.Pentagon S d m c (Eye.{0,0} (B := Nat)) := fun h => notNativePentagon ((AmbientCoherentObserver.pentIff d m c).mp h)
end
end CentralProbe
#print axioms CentralProbe.actualPentagonFails

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open ContextualComposition.GrothendieckStep NativeBlocks SpanApex FibreValue
open ContextadAmbientPayload AmbientBicategory AmbientCoordinates AmbientRoundTrip
open scoped CategoryTheory.Pseudofunctor.StrongTrans
namespace SignedDirectedBundle
noncomputable section
set_option backward.isDefEq.respectTransparency false
def V : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of Nat)
theorem thin (a b : Nat) (f g : a ⟶ b) : f = g := Subsingleton.elim _ _
def constF (n : Nat) : StrongTrans V.toPseudofunctor' V.toPseudofunctor' :=
  ContextadStrong.assemble (G := V) (H := V) (fun _ => (Functor.const Nat).obj n)
    (fun _ => Iso.refl _) (fun _ _ => thin _ _ _ _) (fun _ _ _ => thin _ _ _ _)
def up : StrongTrans.Modification (constF 0) (constF 1) where
  app _ := { app := fun _ => homOfLE (Nat.zero_le 1) : (Functor.const Nat).obj 0 ⟶ (Functor.const Nat).obj 1 }.toCatHom₂
  naturality _ := by apply Cat.Hom₂.ext; ext; exact thin _ _ _ _
open CentralProbe
abbrev X : Obj.{0,0} Nat := V
abbrev f (n : Nat) : X ⟶ X := Bicategory.InducedBicategory.mkHom (constF n)
abbrev lifted : AmbientBicategory.map S 1 (f 0) ⟶ AmbientBicategory.map S 1 (f 1) := AmbientBicategory.cell S 1 (Bicategory.InducedBicategory.mkHom₂ ⟨up⟩)
def x : Raw S X 1 := pair _ _ (pair _ _ (2:Nat) CentralProbe.O.pt) (4:Nat)
theorem noReverse (n : Nat) (w : Raw S X n) :
    ¬ Nonempty (AmbientBicategory.map S n (f 1) ⟶ AmbientBicategory.map S n (f 0)) := by
  rintro ⟨m⟩
  let h := atRaw S m w
  let e := (power S n).dest
  let L := NativeTrace.leaf V e
  have hi (k : Nat) : encode S (AmbientBicategory.map S n (f k)) ⋙ L = L ⋙ totalStrong (constF k) :=
    (congrArg (· ⋙ L) (mapEncode S (f k) n)).trans (ContextadWeakAction.actionLeaf e (totalStrong (constF k)) (strongOver _))
  let k := eqToHom (Functor.congr_obj (hi 1) w).symm ≫ L.map h ≫ eqToHom (Functor.congr_obj (hi 0) w)
  have b : (1:Nat) ≤ 0 := leOfHom (payloadMap k)
  exact (by decide : ¬ (1:Nat) ≤ 0) b
example : ¬ IsIso lifted := by intro h; exact noReverse 1 x ⟨inv lifted⟩
set_option linter.defProp false in
def originalAssociator := actualGood.laws.assoc_natural (f 0)
theorem bothPolygons : AmbientHorizontalDiagrams.Triangle S d m positive X ∧ AmbientHorizontalDiagrams.Pentagon S d m positive X :=
  ⟨actualGood.laws.triangle X,actualGood.laws.pentagon X⟩
end
end SignedDirectedBundle
#print axioms SignedDirectedBundle.originalAssociator
#print axioms SignedDirectedBundle.bothPolygons
