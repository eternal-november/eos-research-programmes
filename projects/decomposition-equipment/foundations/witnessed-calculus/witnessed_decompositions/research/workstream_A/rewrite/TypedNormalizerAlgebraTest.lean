import TypedNormalizerAlgebra
open TypedNormalizer
private def sample : Term Nat (ZMod 3) 0 2 :=
  .cut (.deco 1 (.leaf (by decide : (0 : Fin 3) ≤ 1) 12))
    (.deco 2 (.leaf (by decide : (1 : Fin 3) ≤ 2) 34))
#eval sample.normalize.1.blocks
#eval sample.normalize.2.val
#eval (reify sample.normalize).leafCount
#eval decide (E sample (reify sample.normalize))
#eval decide (E (Term.leaf (M := ZMod 3) (by decide : (0 : Fin 3) ≤ 0) 0)
  (Term.unit 0))
#print axioms Term.IsChain
#print axioms Term.IsBare
#print axioms Term.IsNormal
#print axioms Term.isChain_isNormal
#print axioms Term.isBare_isNormal
#print axioms Step.not_isNormal
#print axioms Spine.comb_isChain
#print axioms Spine.comb_isBare
#print axioms reify_isNormal
