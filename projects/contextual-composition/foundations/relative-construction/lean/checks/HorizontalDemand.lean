import ContextualComposition.AmbientScheduleRealization
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
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
open ContextadHorizontalLaws ContextadSchedule ContextadModification AmbientScheduleRealization
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev l := pentLong d m c (canonicalPentagon d m c)
abbrev r := pentShort d m c (canonicalPentagon d m c)
theorem u : gradeCart (pent1 d m c).src := pentStartCart d m c
theorem v : gradeCart (pent3 d m c).dst := presIso (composite l).grade.symm u
example : ¬ realize l u v = realize r u v := fun e => notNativePentagon ((faithfulPaths l r u v).mp e)
example : realize (triLong d m c (canonicalTriangle d m c)) (triStartCart d m c) (presIso (composite (triShort d m c)).grade.symm (triStartCart d m c)) =
    realize (triShort d m c) (triStartCart d m c) (presIso (composite (triShort d m c)).grade.symm (triStartCart d m c)) :=
  AmbientScheduleRealization.triangle d m c nativeTriangle
end
end CentralProbe
