module
public import ContextualComposition.DependentCarrier
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.Carrier

variable (d : Carrier) (j : Fin d.m) (z : Fin (d.l j))
abbrev Flat := {p : (x : Fin d.n) × Fin (d.k x) // d.map p = ⟨j,z⟩}
abbrev Ragged := (p : d.Parent j) × {y : Fin (d.k p.val) // y ∈ d.children p z}
def toFlat (p : d.Ragged j z) : d.Flat j z :=
  ⟨⟨p.1.val,p.2.val⟩,(d.child_mem p.1 z p.2.val).mp p.2.property⟩
def toRagged (p : d.Flat j z) : d.Ragged j z :=
  let x : d.Parent j := ⟨p.val.1,congrArg Sigma.fst p.property⟩
  ⟨x,⟨p.val.2,(d.child_mem x z p.val.2).mpr p.property⟩⟩
theorem toFlat_toRagged (p : d.Flat j z) : d.toFlat j z (d.toRagged j z p) = p := rfl
theorem toRagged_toFlat (p : d.Ragged j z) : d.toRagged j z (d.toFlat j z p) = p := rfl
variable (e : Carrier) (k : Fin e.m) (w : Fin (e.l k))
/-- Products of actual dependent preimages, with the joint preimage
condition proved from the map on both occurrence carriers. -/
abbrev FlatTwo := {p : ((x : Fin d.n) × Fin (d.k x)) × ((y : Fin e.n) × Fin (e.k y)) //
  (d.map p.1,e.map p.2) = (⟨j,z⟩,⟨k,w⟩)}
def toFlatTwo (p : d.Ragged j z × e.Ragged k w) : d.FlatTwo j z e k w :=
  let x := d.toFlat j z p.1
  let y := e.toFlat k w p.2
  ⟨(x.val,y.val),(congrArg (fun a => (a,e.map y.val)) x.property).trans (congrArg (fun b => ((⟨j,z⟩ : (x : Fin d.m) × Fin (d.l x)),b)) y.property)⟩
def toRaggedTwo (p : d.FlatTwo j z e k w) : d.Ragged j z × e.Ragged k w :=
  (d.toRagged j z ⟨p.val.1,congrArg Prod.fst p.property⟩,
    e.toRagged k w ⟨p.val.2,congrArg Prod.snd p.property⟩)
theorem flat_binary_round (p : d.FlatTwo j z e k w) :
    d.toFlatTwo j z e k w (d.toRaggedTwo j z e k w p) = p := rfl
theorem ragged_binary_round (p : d.Ragged j z × e.Ragged k w) :
    d.toRaggedTwo j z e k w (d.toFlatTwo j z e k w p) = p := rfl
end ContextualComposition.NativeFinitePush.DependentFibre.Carrier
