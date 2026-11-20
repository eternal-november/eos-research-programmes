module
public import ContextualComposition.RepresentableKleisliOriginal
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePentagonWord
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
section
variable {C : Type*} [Bicategory C]
def L {a b b' c d : C} (p : a ⟶ b) {u : b ⟶ c} {v : c ⟶ d} {u' : b ⟶ b'} {v' : b' ⟶ d}
    (J : u ≫ v ≅ u' ≫ v') : (p ≫ u) ≫ v ≅ (p ≫ u') ≫ v' :=
  (α_ p u v) ≪≫ whiskerLeftIso p J ≪≫ (α_ p u' v').symm
local infixl:81 " ▹ " => whiskerRightIso
variable {X2 X1 Y3 Y2 Y1 Z4 Z3 Z2 Z1 : C}
variable {m : X2 ⟶ X1} {k : X1 ⟶ Y2} {n : Y2 ⟶ Y1} {l : Y1 ⟶ Z2} {q : Z2 ⟶ Z1}
variable {j : X2 ⟶ Y3} {mA mB : Y3 ⟶ Y2}
variable {l2 : Y2 ⟶ Z3} {l3 : Y3 ⟶ Z4} {nA nB : Z3 ⟶ Z2} {mC mD mE : Z4 ⟶ Z3}
variable (dh : m ≫ k ≅ j ≫ mA) (di : n ≫ l ≅ l2 ≫ nA) (dI : mA ≫ l2 ≅ l3 ≫ mC)
variable (bdi : mB ≫ l2 ≅ l3 ≫ mD) (dq : mC ≫ nB ≅ mE ≫ nA)
variable (ay : mA ≫ n ≅ mB ≫ n) (az : nA ≫ q ≅ nB ≫ q)
variable (aZ : mC ≫ nA ≅ mD ≫ nA) (faz : mD ≫ nB ≅ mE ≫ nB)
def long := dh ▹ n ▹ l ▹ q ≪≫ L j ay ▹ l ▹ q ≪≫ L (j ≫ mB) di ▹ q ≪≫
  L ((j ≫ mB) ≫ l2) az ≪≫ L j bdi ▹ nB ▹ q ≪≫ L (j ≫ l3) faz ▹ q
def short := L (m ≫ k) di ▹ q ≪≫ L (((m ≫ k) ≫ l2)) az ≪≫ dh ▹ l2 ▹ nB ▹ q ≪≫
  L j dI ▹ nB ▹ q ≪≫ L (j ≫ l3) dq ▹ q ≪≫ L (((j ≫ l3) ≫ mE)) az
def shared := dh ▹ n ▹ l ▹ q ≪≫ L (j ≫ mA) di ▹ q ≪≫ L j dI ▹ nA ▹ q
def outLong (p : X2 ⟶ Z4) := L p aZ ▹ q ≪≫ L (p ≫ mD) az ≪≫ L p faz ▹ q
def outShort (p : X2 ⟶ Z4) := L (p ≫ mC) az ≪≫ L p dq ▹ q ≪≫ L (p ≫ mE) az
def outerLong :=
  aZ ▹ q ≪≫ L mD az ≪≫ faz ▹ q
def outerShort :=
  L mC az ≪≫ dq ▹ q ≪≫ L mE az
end
end ContextualComposition.GrothendieckStep.RepresentablePentagonWord
