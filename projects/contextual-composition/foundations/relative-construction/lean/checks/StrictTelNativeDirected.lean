import ContextualComposition.StrictTelCategories
import ContextualComposition.StrictTelNormal
open CategoryTheory CategoryTheory.Limits Opposite ContextualComposition.GrothendieckStep
open SpanApex NativeCleavage NativeBlocks NativeBlocks.Nested StrictSpanAlgebra
namespace StrictTelNativeDirected
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
inductive Token where | leaf
instance : Category.{0} Token where
  Hom _ _ := Nat
  id _ := 0
  comp a b := a + b
  id_comp := by intros; apply Nat.zero_add
  comp_id := by intros; apply Nat.add_zero
  assoc := by intros; apply Nat.add_assoc
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Token)
  extend A := (Functor.const Token).obj A
  lift u := { app := fun _ => u }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))

abbrev U := power S 1
abbrev A := U.apex
abbrev l : A ⥤ Nat := U.source
def atBase (n : Nat) : A := pair P.grades (𝟭 _) n Token.leaf
abbrev wt {x y : A} (f : x ⟶ y) : Nat := payloadMap f
theorem token_eq (z : Token) : Token.leaf = z := by cases z; rfl
theorem at_eq (x : A) : atBase (l.obj x) = x := by
  change pair P.grades (𝟭 _) (grade P.grades (𝟭 _) x) Token.leaf = x
  rw [token_eq (payload P.grades (𝟭 _) x)]
  rfl
theorem edge_ext {x y : A} {f g : x ⟶ y} (h : wt f = wt g) : f = g := by
  apply (homEquiv x y).injective
  exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq h)
theorem id_wt (x : A) : wt (𝟙 x) = 0 := by
  change (Grothendieck.Hom.fiber (𝟙 x.unop)).unop = _
  rw [Grothendieck.id_fiber]
  rfl
theorem comp_wt {x y z : A} (f : x ⟶ y) (g : y ⟶ z) : wt (f ≫ g) = wt f + wt g := by
  show payloadMap (f ≫ g) = _
  rw [payload_comp]
  have h : (P.grades.map ((𝟭 Nat).map (gradeMap f)).op).toFunctor.map (payloadMap g) = payloadMap g := rfl
  rw [h]
  have q : eqToHom (comp_target (gradeMap f) (gradeMap g) (payload P.grades (𝟭 _) z)) = 𝟙 _ := rfl
  rw [q,Category.comp_id]
  rfl

theorem sameFeet : U.source = U.dest := by
  apply Functor.hext (fun _ => rfl)
  intro x y f
  exact heq_of_eq (Subsingleton.elim _ _)

def build {X : Type} [Category X] (F : X ⥤ Nat)
    (w : ∀ {x y : X}, (x ⟶ y) → Nat)
    (hi : ∀ x, w (𝟙 x) = 0) (hc : ∀ {x y z} (f : x ⟶ y) (g : y ⟶ z), w (f ≫ g) = w f + w g) :
    X ⥤ A where
  obj x := atBase (F.obj x)
  map f := arrow (F.map f) (w f)
  map_id x := edge_ext ((hi x).trans (id_wt _).symm)
  map_comp {x y z} f g := by
    apply edge_ext
    let a : atBase (F.obj x) ⟶ atBase (F.obj y) := arrow (F.map f) (w f)
    let b : atBase (F.obj y) ⟶ atBase (F.obj z) := arrow (F.map g) (w g)
    change w (f ≫ g) = wt (a ≫ b)
    rw [comp_wt a b]
    exact hc f g

theorem byWeights {X : Type} [Category X] (F G : X ⥤ A) (e : F ⋙ l = G ⋙ l)
    (h : ∀ {x y} (k : x ⟶ y), wt (F.map k) = wt (G.map k)) : F = G := by
  have o : ∀ x, F.obj x = G.obj x := fun x =>
    ((at_eq (F.obj x)).symm.trans (congrArg atBase (Functor.congr_obj e x))).trans (at_eq (G.obj x))
  apply Functor.hext o
  intro x y k
  let f := F.map k
  let g := G.map k
  have nh : wt f = wt g := h k
  have q {a b c d : A} (oa : a = c) (ob : b = d) (f : a ⟶ b) (g : c ⟶ d)
      (hh : wt f = wt g) : HEq f g := by
    subst c; subst d
    exact heq_of_eq (edge_ext hh)
  exact q (o x) (o y) f g nh

def eU : Over I U where
  functor := build (𝟭 _) (fun _ => 0) (fun _ => rfl) (fun _ _ => rfl)
  source := rfl
  dest := sameFeet ▸ rfl

def tU : Over (Pair U U) U where
  functor := build (Pair U U).source (fun f => wt f.hom.fst + wt f.hom.snd)
    (fun _ => by change wt (𝟙 _) + wt (𝟙 _) = 0; simp only [id_wt])
    (fun f g => by change wt (f.hom.fst ≫ g.hom.fst) + wt (f.hom.snd ≫ g.hom.snd) = _
                   rw [comp_wt,comp_wt]; omega)
  source := rfl
  dest := by
    let F := Strict.fst U.dest U.source
    let G := Strict.snd U.dest U.source
    let k : (Pair U U).apex ⥤ A := build (Pair U U).source
      (fun f => wt f.hom.fst + wt f.hom.snd)
      (fun _ => by change wt (𝟙 _) + wt (𝟙 _) = 0; simp only [id_wt])
      (fun f g => by change wt (f.hom.fst ≫ g.hom.fst) + wt (f.hom.snd ≫ g.hom.snd) = _
                     rw [comp_wt,comp_wt]; omega)
    change k ⋙ U.dest = G ⋙ U.dest
    exact (congrArg (k ⋙ ·) sameFeet.symm).trans
      ((congrArg (F ⋙ ·) sameFeet).trans ((Strict.commute _ _).trans (congrArg (G ⋙ ·) sameFeet)))
def M : Ops U := ⟨eU,tU⟩
theorem mLaws : Laws M where
  left F := by
    apply byWeights _ _ ((join_src M _ _ _).trans (one_src M _))
    intro x y f; exact Nat.zero_add _
  right F := by
    apply byWeights _ _ (join_src M _ _ _)
    intro x y f; exact Nat.add_zero _
  assoc F G H e d := by
    apply byWeights _ _ ((join_src M _ _ _).trans ((join_src M _ _ _).trans (join_src M _ _ _).symm))
    intro x y f; exact Nat.add_assoc _ _ _

theorem cartWeight {x y : A} (f : x ⟶ y) : Cartesian l f ↔ wt f = 0 := by
  constructor
  · intro h
    let g : x ⟶ y := arrow (l.map f) (0:Nat)
    obtain ⟨i,⟨_,hi⟩,_⟩ := h x g (𝟙 _) (Subsingleton.elim _ _)
    have hf := (comp_wt i f).symm.trans (congrArg (fun k : x ⟶ y => wt k) hi)
    change wt i + wt f = 0 at hf
    omega
  · intro hf z g a _
    let i : z ⟶ x := arrow a (wt g)
    refine ⟨i,⟨rfl,edge_ext ?_⟩,?_⟩
    · rw [comp_wt i f,hf,Nat.add_zero]; rfl
    · intro j hj
      apply edge_ext
      have h := (comp_wt j f).symm.trans (congrArg (fun k : z ⟶ y => wt k) hj.2)
      rw [hf,Nat.add_zero] at h
      exact h

noncomputable def c : Cleavage l := StrictTelNormal.normalize l (SpanPull.All.parts S 1)
noncomputable def context : Contextad U where
  operations := M
  laws := mLaws
  cleavage := c
  normal := StrictTelNormal.normal _ _
  unitCart := fun _ _ => (cartWeight _).mpr rfl
  tensorCart := by
    intro x y f H
    obtain ⟨h,k⟩ := StrictSpanCart.pairTo c c f H
    change Cartesian l ((tU.functor).map f)
    apply (cartWeight _).mpr
    change wt f.hom.fst + wt f.hom.snd = 0
    rw [(cartWeight _).mp h,(cartWeight _).mp k]

def scale : Over U U where
  functor := build l (fun f => 2 * wt f)
    (fun x => by rw [id_wt])
    (fun f g => by rw [comp_wt]; omega)
  source := rfl
  dest := (congrArg (· ⋙ U.dest) (show _ = _ from rfl)).trans
    ((congrArg ((build l (fun f => 2 * wt f) _ _) ⋙ ·) sameFeet.symm).trans sameFeet)

theorem scaleCart : CartesianMap scale := by
  intro x y f h
  apply (cartWeight _).mpr
  change 2 * wt f = 0
  rw [(cartWeight _).mp h]

theorem scaleMon : StrictTelOperations.Multiplicative scale (M := M) (N := M) where
  unit := by
    apply byWeights _ _ ((congrArg (eU.functor ⋙ ·) scale.source).trans (Functor.comp_id _).symm |>.trans (Functor.comp_id _))
    intro _ _ _; rfl
  tensor := by
    apply byWeights _ _ (by rfl)
    intro x y f
    change 2 * (wt f.hom.fst + wt f.hom.snd) = 2 * wt f.hom.fst + 2 * wt f.hom.snd
    omega

noncomputable def K : StrictTelCategories.Ctx Nat := ⟨⟨P,S⟩,context⟩
noncomputable def f : StrictTelCategories.CtxHom K K := ⟨scale,scaleCart,scaleMon⟩
noncomputable def alg := (StrictTelCategories.encode (B := Nat)).obj K
noncomputable def F := (StrictTelCategories.encode (B := Nat)).map f

def drift : (0:Nat) ⟶ 4 := homOfLE (by decide)
def leg (n : Nat) : atBase 0 ⟶ atBase 4 := arrow drift n
def vertex (n : Nat) : (Pair U U).apex := ⟨atBase n,atBase n,rfl⟩
def bothLegs (m n : Nat) : vertex 0 ⟶ vertex 4 := ⟨⟨leg m,leg n,Subsingleton.elim _ _⟩⟩
noncomputable def actualPair := (StrictTelNested.concatenate S 1 1).functor ⋙ incl S 2

theorem congrWeight {X : Type} [Category X] {F G : X ⥤ A} (h : F = G) {a b : X} (k : a ⟶ b) :
    wt (F.map k) = wt (G.map k) := by subst G; rfl

theorem actualWeight (m n : Nat) :
    wt (alg.data.action.functor.map (actualPair.map (bothLegs m n))) = m+n := by
  have h := congrArg (fun a => a.functor) (StrictTelRecovery.restriction_tensor S M mLaws)
  exact congrWeight h (bothLegs m n)
theorem movingFoot : l.map (tU.functor.map (bothLegs 2 3)) = drift := rfl
theorem sameDirectedFunctor : F.f.functor = scale.functor := StrictTelCategories.encode_hom f
/-- The complete exact algebra-map square, at a moving noninvertible
arrow with a nonzero label on each side of its actual two-leaf cut. -/
theorem actualScaledWeight :
    wt (alg.data.action.functor.map ((StrictTelMap.map S S F.f).functor.map
      (actualPair.map (bothLegs 2 3)))) = 10 := by
  have h := congrWeight F.law (actualPair.map (bothLegs 2 3))
  refine h.symm.trans ?_
  change 2 * wt (alg.data.action.functor.map (actualPair.map (bothLegs 2 3))) = 10
  rw [actualWeight]

theorem nontrivial : leg 2 ≠ leg 3 := fun h => (by decide : (2:Nat) ≠ 3) (congrArg wt h)
theorem noReverse : ¬ Nonempty (atBase 4 ⟶ atBase 0) :=
  fun ⟨f⟩ => (by decide : ¬ (4:Nat) ≤ 0) (leOfHom (l.map f))
end StrictTelNativeDirected
#print axioms StrictTelNativeDirected.actualWeight
#print axioms StrictTelNativeDirected.actualScaledWeight
#print axioms StrictTelNativeDirected.sameDirectedFunctor
#print axioms StrictTelNativeDirected.noReverse
