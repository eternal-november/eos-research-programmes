import Mathlib
namespace ExactDockResult

theorem oneByteCannotCover (encode : Fin 257 → Fin 256)
    (decode : Fin 256 → Fin 257) :
    ¬ (∀ x, decode (encode x) = x) := by
  intro h
  have inj : Function.Injective encode := fun x y he => by
    have he' := congrArg decode he
    simpa only [h x, h y] using he'
  have size := Fintype.card_le_of_injective encode inj
  simp at size

def pageOf (code : ℕ) := (code-1)/128
def residual (code : ℕ) := if code=0 then 0 else 1+(code-1)%128
def assemble (page octet : ℕ) := if octet=0 then 0 else 128*page+octet

theorem recover (code : ℕ) :
    assemble (pageOf code) (residual code) = code := by
  by_cases z : code = 0
  · simp [z, assemble, residual]
  · have p : 0 < code := Nat.pos_of_ne_zero z
    have h := Nat.mod_add_div (code-1) 128
    simp [assemble, pageOf, residual, z]
    omega

theorem scopedOctet (code : ℕ) : residual code ≤ 128 := by
  unfold residual
  have hm : (code-1)%128 < 128 := Nat.mod_lt _ (by decide)
  split_ifs <;> omega

theorem oldPrefixWrong : assemble (pageOf 0) (residual 256) = 128 := by decide

def receiveFits (active report cap : ℕ) := active+report ≤ cap

theorem twoCuts :
    receiveFits 1 3 4 ∧ ¬ receiveFits 2 3 4 ∧
    receiveFits 3 1 4 ∧ ¬ receiveFits 3 2 4 := by unfold receiveFits; decide

end ExactDockResult
#print axioms ExactDockResult.oneByteCannotCover
#print axioms ExactDockResult.recover
#print axioms ExactDockResult.scopedOctet
#print axioms ExactDockResult.oldPrefixWrong
#print axioms ExactDockResult.twoCuts
