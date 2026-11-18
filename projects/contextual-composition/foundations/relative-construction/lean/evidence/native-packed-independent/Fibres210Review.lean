import ContextualComposition.PackedCuts
open CategoryTheory Opposite ContextualComposition.GrothendieckStep PackedCuts
namespace Fibres210
set_option backward.isDefEq.respectTransparency false
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split) (Y : Psh.{b,w,u,v} B) (A : B)
abbrev D := Iterates.Packed P S ((PackedFree.free S).obj Y) (op A)
theorem hom_image_iff {x y : D S Y A} (f : (mu S Y A).obj x ⟶ (mu S Y A).obj y) :
    (∃! g : x ⟶ y, (mu S Y A).map g = f) ↔ profile S Y A x = profile S Y A y := by
  constructor
  · rintro ⟨g,_,_⟩; exact profile_map S Y A g
  · intro same
    have h := joinIncoming S Y A
    obtain ⟨⟨z,g⟩,eq⟩ := (h y).surjective ⟨(mu S Y A).obj x,f⟩
    have zx : z = x := obj_ext S Y A ((profile_map S Y A g).trans same.symm) (congrArg Sigma.fst eq)
    subst z
    refine ⟨g,(Sigma.mk.inj_iff.mp eq).2.eq,?_⟩
    intro v hv
    let _ := BlockCartesian.faithful (mu S Y A) h
    exact (mu S Y A).map_injective (hv.trans (Sigma.mk.inj_iff.mp eq).2.eq.symm)
noncomputable def homAtCut {x y : D S Y A} (h : profile S Y A x = profile S Y A y) :
    (x ⟶ y) ≃ ((mu S Y A).obj x ⟶ (mu S Y A).obj y) :=
  Equiv.ofBijective (mu S Y A).map
    ⟨(BlockCartesian.faithful _ (joinIncoming S Y A)).map_injective,
      fun f => ((hom_image_iff S Y A f).mpr h).exists⟩
/-- A positive output exposes a failure of fullness of the actual monad multiplication. -/
theorem notFullAtPositive (x : Iterates.Packed P S Y (op A)) (pos : 0 < x.1) : ¬ (mu S Y A).Full := by
  let c₀ : choices S Y A x := ⟨(0,x.1),Nat.zero_add _⟩
  let c₁ : choices S Y A x := ⟨(x.1,0),Nat.add_zero _⟩
  let a := (cutFibre S Y A x).symm c₀
  let b := (cutFibre S Y A x).symm c₁
  intro hf; let _ := hf
  let z : a.1 ⟶ b.1 := (mu S Y A).preimage (eqToHom (a.2.trans b.2.symm))
  have h := profile_map S Y A z
  have ha : profile S Y A a.1 = c₀.1 := congrArg Subtype.val ((cutFibre S Y A x).apply_symm_apply c₀)
  have hb : profile S Y A b.1 = c₁.1 := congrArg Subtype.val ((cutFibre S Y A x).apply_symm_apply c₁)
  have e := congrArg Prod.fst (ha.symm.trans (h.trans hb))
  change 0 = x.1 at e
  omega
/-- More precise than the count alone: the ordinary strict categorical fibre is discrete on the cut positions;
in the fibre a morphism must map to the identity, not just between identical output objects. -/
local instance (x : Iterates.Packed P S Y (op A)) : Category.{max u v} ((mu S Y A).Fiber x) :=
  Functor.Fiber.fiberCategory (p := mu S Y A) (S := x)
theorem fibreHomSubsingleton (x : Iterates.Packed P S Y (op A)) (a b : (mu S Y A).Fiber x) : Subsingleton (a ⟶ b) := by
  constructor
  intro f g
  apply Subtype.ext
  let _ := BlockCartesian.faithful (mu S Y A) (joinIncoming S Y A)
  apply (mu S Y A).map_injective
  exact (NativeCleavage.Reindex.vertical_map f).trans (NativeCleavage.Reindex.vertical_map g).symm
theorem fibreHomEq (x : Iterates.Packed P S Y (op A)) (a b : (mu S Y A).Fiber x) (f : a ⟶ b) : a = b :=
  Subtype.ext (obj_ext S Y A (profile_map S Y A f.1) (a.property.trans b.property.symm))
end Fibres210
