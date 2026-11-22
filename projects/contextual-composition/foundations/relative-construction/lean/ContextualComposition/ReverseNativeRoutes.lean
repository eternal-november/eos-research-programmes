module
public import ContextualComposition.NativeRouteReduction
public import ContextualComposition.NativeFibreAdapter
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
universe u
theorem leftGatherNatural : GatherLeftNat left.{u} where
  inner _ := ⟨fun _ _ => by funext ⟨_,v⟩; cases v <;> rfl⟩
  outer _ := ⟨by funext z; exact z.2.elim, fun _ _ => by funext ⟨_,v⟩; cases v <;> rfl⟩
/-- Application to whole native cells; only the chosen branch chart remains
as input coordinate convention. -/
theorem Pair.native_binary (p q : Pair.{u}) (i : Fin p.target.n) (j : Fin q.target.n)
    (s : Fin (p.dstCont i).n) (t : Fin (q.dstCont j).n) :
  let e := p.atTarget i s
  let f := q.atTarget j t;
    coeff.seq (actRect (S:=sum) (Z:=PEmpty) e.xs f.xs (fun x y => separateInnerNative gather left (e.V x) (f.V y) (e.J.terms x) (f.J.terms y)))
      (coeff.seq (actRect (S:=sum) (Z:=PEmpty) e.xs f.xs
        (fun x y => tensor.map (tensor.map (coeff.id (e.V x)) (e.β x)) (tensor.map (coeff.id (f.V y)) (f.β y))))
        (coeff.seq (nativeLeft gather left e.V f.V e.xs f.xs e.b f.b)
          (coeff.seq (tensor.map (tensor.map e.α (coeff.id e.b)) (tensor.map f.α (coeff.id f.b))) (middle.cell e.a e.b f.a f.b)))) =
    coeff.seq (actRect (S:=sum) (Z:=PEmpty) e.xs f.xs
      (fun x y => actRect (S:=sum) (Z:=PEmpty) (e.J.terms x) (f.J.terms y) (fun v w => middle.cell (e.V x) v (f.V y) w)))
      (coeff.seq (actRect (S:=sum) (Z:=PEmpty) e.xs f.xs (fun x y => togetherInnerNative gather left (e.V x) (f.V y) (e.J.terms x) (f.J.terms y)))
        (coeff.seq (actRect (S:=sum) (Z:=PEmpty) e.xs f.xs
          (fun x y => tensor.map (tensor.map (coeff.id (e.V x)) (coeff.id (f.V y))) (tensor.map (e.β x) (f.β y))))
          (coeff.seq (nativeRight gather left e.V f.V e.xs f.xs e.b f.b) (tensor.map (tensor.map e.α f.α) (tensor.map (coeff.id e.b) (coeff.id f.b)))))) :=
  let e := p.atTarget i s
  let f := q.atTarget j t
  native_binary_on_chart gather left gatherNat leftGatherNatural
    e.V f.V e.xs f.xs e.b f.b middle outerLaws innerLaws e.J.terms f.J.terms e.β f.β e.α f.α
end ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
