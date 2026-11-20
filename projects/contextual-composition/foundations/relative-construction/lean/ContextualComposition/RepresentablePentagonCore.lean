module
public import ContextualComposition.RepresentablePentagonWordPasting
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePentagonCore
open CategoryTheory CategoryTheory.Bicategory
open RepresentablePentagonWord RepresentablePentagonWordPasting AmbientHorizontalNaturality
open scoped CategoryTheory.Bicategory
local infixl:81 " ▹ " => whiskerRightIso
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
section
variable {C : Type*} [Bicategory C]
variable {X2 X1 Y3 Y2 Y1 Z4 Z3 Z2 Z1 : C}
variable {m : X2 ⟶ X1} {k : X1 ⟶ Y2} {n : Y2 ⟶ Y1} {l : Y1 ⟶ Z2} {q : Z2 ⟶ Z1}
variable {j : X2 ⟶ Y3} {mA mB : Y3 ⟶ Y2}
variable {l2 : Y2 ⟶ Z3} {l3 : Y3 ⟶ Z4} {nA nB : Z3 ⟶ Z2} {mC mD mE : Z4 ⟶ Z3}
variable (dh : m ≫ k ≅ j ≫ mA) (di : n ≫ l ≅ l2 ≫ nA) (dI : mA ≫ l2 ≅ l3 ≫ mC)
variable (bdi : mB ≫ l2 ≅ l3 ≫ mD) (dq : mC ≫ nB ≅ mE ≫ nA)
variable (ay : mA ≫ n ≅ mB ≫ n) (az : nA ≫ q ≅ nB ≫ q)
variable (aZ : mC ≫ nA ≅ mD ≫ nA) (faz : mD ≫ nB ≅ mE ≫ nB)
theorem shortSwap (az : nA ≫ q ≅ nB ≫ q) :
    short dh di dI dq az = shared (q := q) dh di dI ≪≫ outShort dq az (j ≫ l3) := by
  have w1 := congrArg Iso.hom (swap (dh ▹ l2) az)
  have aux := congrArg (· ▹ q) (swap dh di)
  rw [rightDistr,rightDistr] at aux
  have w2 := congrArg Iso.hom aux
  have w3 := congrArg Iso.hom (swap (L j dI) az)
  apply Iso.ext
  simp only [short,shared,outShort,Iso.trans_hom,Category.assoc]
  simp only [Iso.trans_hom,Category.assoc] at w1 w2 w3
  rw [reassoc_of% w1,reassoc_of% w2,reassoc_of% w3]
theorem longBody :
    L j ay ▹ l ≪≫ L (j ≫ mB) di ≪≫ L j bdi ▹ nA =
    frame j mA n l ≪≫ whiskerLeftIso j
      (ay ▹ l ≪≫ (serial bdi.symm di.symm).symm ≪≫ (α_ l3 mD nA).symm) ≪≫ (frame j l3 mD nA).symm := by
  apply Iso.ext
  simp only [frame,L,serial,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    whiskerLeftIso_hom,whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_inv]
  bicategory
theorem shortBody :
    L (j ≫ mA) di ≪≫ L j dI ▹ nA ≪≫ L (j ≫ l3) aZ =
    frame j mA n l ≪≫ whiskerLeftIso j
      ((serial dI.symm di.symm).symm ≪≫ whiskerLeftIso l3 aZ ≪≫ (α_ l3 mD nA).symm) ≪≫ (frame j l3 mD nA).symm := by
  apply Iso.ext
  simp only [frame,L,serial,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,Iso.symm_inv,
    whiskerLeftIso_hom,whiskerRightIso_hom,whiskerRightIso_inv,whiskerLeftIso_inv]
  bicategory
theorem commonBody (H : ay ▹ l ≪≫ (serial bdi.symm di.symm).symm =
    (serial dI.symm di.symm).symm ≪≫ whiskerLeftIso l3 aZ) :
    L j ay ▹ l ≪≫ L (j ≫ mB) di ≪≫ L j bdi ▹ nA =
    L (j ≫ mA) di ≪≫ L j dI ▹ nA ≪≫ L (j ≫ l3) aZ := by
  rw [longBody,shortBody,← Iso.trans_assoc (ay ▹ l),H,Iso.trans_assoc]
theorem longSwap (H : ay ▹ l ≪≫ (serial bdi.symm di.symm).symm =
    (serial dI.symm di.symm).symm ≪≫ whiskerLeftIso l3 aZ) :
    long dh di bdi ay az faz = shared (q := q) dh di dI ≪≫ outLong az aZ faz (j ≫ l3) := by
  have w1 := congrArg Iso.hom (swap (L j bdi) az)
  have aux := congrArg (· ▹ q) (commonBody (j := j) di dI bdi ay aZ H)
  simp only [rightDistr] at aux
  have w2 := congrArg Iso.hom aux
  apply Iso.ext
  simp only [long,shared,outLong,Iso.trans_hom,Category.assoc]
  simp only [Iso.trans_hom,Category.assoc] at w1 w2
  rw [reassoc_of% w1,reassoc_of% w2]
theorem outLongFrame (p : X2 ⟶ Z4) :
    outLong az aZ faz p = frame p mC nA q ≪≫ whiskerLeftIso p (outerLong az aZ faz) ≪≫ (frame p mE nB q).symm := by
  apply Iso.ext
  simp only [frame,outLong,outerLong,L,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,whiskerLeftIso_hom,whiskerRightIso_hom,whiskerRightIso_inv]
  bicategory
theorem outShortFrame (p : X2 ⟶ Z4) :
    outShort dq az p = frame p mC nA q ≪≫ whiskerLeftIso p (outerShort dq az) ≪≫ (frame p mE nB q).symm := by
  apply Iso.ext
  simp only [frame,outShort,outerShort,L,Iso.trans_hom,Iso.trans_inv,Iso.symm_hom,whiskerLeftIso_hom,whiskerRightIso_hom,whiskerRightIso_inv]
  bicategory
theorem core
    (H : ay ▹ l ≪≫ (serial bdi.symm di.symm).symm = (serial dI.symm di.symm).symm ≪≫ whiskerLeftIso l3 aZ)
    (Z : outerLong az aZ faz = outerShort dq az) :
    long dh di bdi ay az faz = short dh di dI dq az := by
  rw [longSwap dh di dI bdi ay az aZ faz H,shortSwap, outLongFrame, outShortFrame,Z]
end
end ContextualComposition.GrothendieckStep.RepresentablePentagonCore
