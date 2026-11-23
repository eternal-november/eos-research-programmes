module
public import ContextualComposition.RelativeTensorMixedInputComposition

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section JointSquaresSection
section Joint
variable {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
variable [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
variable [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
variable {i₀ : A₀ ⥤ A₁} {i₁ : A₂ ⥤ A₃} {o₀ : A₀ ⥤ A₂} {o₁ : A₁ ⥤ A₃}
variable {j₀ : B₀ ⥤ B₁} {j₁ : B₂ ⥤ B₃} {p₀ : B₀ ⥤ B₂} {p₁ : B₁ ⥤ B₃}
variable {F₀ : A₀ ⥤ B₀} {F₁ : A₁ ⥤ B₁} {F₂ : A₂ ⥤ B₂} {F₃ : A₃ ⥤ B₃}

/-- Naturality of the output comparison with respect to the input comparison.
The outer faces run input then output to output then input. -/
def JointEndpointSquare (a : i₀ ⋙ o₁ ≅ o₀ ⋙ i₁) (b : j₀ ⋙ p₁ ≅ p₀ ⋙ j₁)
    (l₀ : i₀ ⋙ F₁ ≅ F₀ ⋙ j₀) (l₁ : i₁ ⋙ F₃ ≅ F₂ ⋙ j₁)
    (r₀ : o₀ ⋙ F₂ ≅ F₀ ⋙ p₀) (r₁ : o₁ ⋙ F₃ ≅ F₁ ⋙ p₁) : Prop :=
  ∀ x, r₁.hom.app (i₀.obj x) ≫ p₁.map (l₀.hom.app x) ≫ b.hom.app (F₀.obj x) =
    F₃.map (a.hom.app x) ≫ l₁.hom.app (o₀.obj x) ≫ j₁.map (r₀.hom.app x)

private theorem mapTransport {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {x y : C} (e : x = y) :
    F.map (eqToHom e) = eqToHom (congrArg F.obj e) := by
  cases e
  exact F.map_id x

/-- A cube whose six faces are transports is coherent by proof irrelevance.
This does not hold when any face is merely an arbitrary natural isomorphism. -/
private theorem jointEndpoint_transports
    (a : i₀ ⋙ o₁ = o₀ ⋙ i₁) (b : j₀ ⋙ p₁ = p₀ ⋙ j₁)
    (l₀ : i₀ ⋙ F₁ = F₀ ⋙ j₀) (l₁ : i₁ ⋙ F₃ = F₂ ⋙ j₁)
    (r₀ : o₀ ⋙ F₂ = F₀ ⋙ p₀) (r₁ : o₁ ⋙ F₃ = F₁ ⋙ p₁) :
    JointEndpointSquare (eqToIso a) (eqToIso b) (eqToIso l₀) (eqToIso l₁)
      (eqToIso r₀) (eqToIso r₁) := by
  intro x
  simp only [eqToIso.hom, eqToHom_app, mapTransport, eqToHom_trans]

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
variable {k₀ : C₀ ⥤ C₁} {k₁ : C₂ ⥤ C₃} {q₀ : C₀ ⥤ C₂} {q₁ : C₁ ⥤ C₃}
variable {G₀ : B₀ ⥤ C₀} {G₁ : B₁ ⥤ C₁} {G₂ : B₂ ⥤ C₂} {G₃ : B₃ ⥤ C₃}

theorem pasteJointEndpointSquare
    {a : i₀ ⋙ o₁ ≅ o₀ ⋙ i₁} {b : j₀ ⋙ p₁ ≅ p₀ ⋙ j₁} {c : k₀ ⋙ q₁ ≅ q₀ ⋙ k₁}
    {l₀ : i₀ ⋙ F₁ ≅ F₀ ⋙ j₀} {l₁ : i₁ ⋙ F₃ ≅ F₂ ⋙ j₁}
    {r₀ : o₀ ⋙ F₂ ≅ F₀ ⋙ p₀} {r₁ : o₁ ⋙ F₃ ≅ F₁ ⋙ p₁}
    {m₀ : j₀ ⋙ G₁ ≅ G₀ ⋙ k₀} {m₁ : j₁ ⋙ G₃ ≅ G₂ ⋙ k₁}
    {s₀ : p₀ ⋙ G₂ ≅ G₀ ⋙ q₀} {s₁ : p₁ ⋙ G₃ ≅ G₁ ⋙ q₁}
    (h : JointEndpointSquare a b l₀ l₁ r₀ r₁)
    (k : JointEndpointSquare b c m₀ m₁ s₀ s₁) :
    JointEndpointSquare a c (pasteInputSquare l₀ m₀) (pasteInputSquare l₁ m₁)
      (pasteInputSquare r₀ s₀) (pasteInputSquare r₁ s₁) := by
  intro x
  change (G₃.map (r₁.hom.app (i₀.obj x)) ≫ s₁.hom.app (F₁.obj (i₀.obj x))) ≫
      q₁.map (G₁.map (l₀.hom.app x) ≫ m₀.hom.app (F₀.obj x)) ≫
      c.hom.app (G₀.obj (F₀.obj x)) =
    G₃.map (F₃.map (a.hom.app x)) ≫
      (G₃.map (l₁.hom.app (o₀.obj x)) ≫ m₁.hom.app (F₂.obj (o₀.obj x))) ≫
      k₁.map (G₂.map (r₀.hom.app x) ≫ s₀.hom.app (F₀.obj x))
  have h₁ := s₁.hom.naturality (l₀.hom.app x)
  have h₂ := m₁.hom.naturality (r₀.hom.app x)
  change G₃.map (p₁.map (l₀.hom.app x)) ≫ s₁.hom.app (j₀.obj (F₀.obj x)) =
    s₁.hom.app (F₁.obj (i₀.obj x)) ≫ q₁.map (G₁.map (l₀.hom.app x)) at h₁
  change G₃.map (j₁.map (r₀.hom.app x)) ≫ m₁.hom.app (p₀.obj (F₀.obj x)) =
    m₁.hom.app (F₂.obj (o₀.obj x)) ≫ k₁.map (G₂.map (r₀.hom.app x)) at h₂
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h₁, k, ← reassoc_of% h₂]
  simp only [← Functor.map_comp, ← Category.assoc]
  simp only [Category.assoc, h x]

end Joint

section Actual
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- Actual source and target endpoint interchanger at a pair of boundary arrows,
not a replacement by a commutative square of object functions. -/
def endpointInterchange.{w,k}
    (P : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{w,k}))
    {a b c d : B} (f : a ⟶ b) (g : c ⟶ d) :=
  Cat.Hom.toNatIso ((P.map g.toLoc).naturality f.op.toLoc)

/-- Exact joint compatibility obligation for the existing mixed multiplication
input and output comparison isomorphisms. -/
def MixedMultiplicationJoint (s : middleComposite N M ⟶ middleComposite M N)
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
    {a b c d : B} (f : a ⟶ b) (g : c ⟶ d) : Prop :=
  let H := middleComposite M N
  let HH := middleComposite H H
  JointEndpointSquare (endpointInterchange HH f g) (endpointInterchange H f g)
    (mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n f c)
    (mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n f d)
    (mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n b g)
    (mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a g)

end Actual
end JointSquaresSection

section JointEndpointPinsSection
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable {a b c d : B} (f : a ⟶ b) (g : c ⟶ d)

set_option maxHeartbeats 100000 in
private theorem middleComposite_endpointInterchange :
    endpointInterchange (middleComposite M N) f g =
      eqToIso (factor_order (Middle.change M f.op.toLoc) (N.map g.toLoc)) := rfl

set_option maxHeartbeats 100000 in
private theorem identifyFirst_joint
    {F G F' G' : LocallyDiscrete B ⥤ᵖ Cat.{vM,uM}}
    {K L : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}}
    (h : F = F') (k : G = G') (s : F ⟶ G) (t : F' ⟶ G') (u : K ⟶ L)
    (ιK : mapFirst (G := K) s ⋙ (identifyFirst k K).functor =
      (identifyFirst h K).functor ⋙ mapFirst (G := K) t)
    (ιL : mapFirst (G := L) s ⋙ (identifyFirst k L).functor =
      (identifyFirst h L).functor ⋙ mapFirst (G := L) t) :
    JointEndpointSquare (eqToIso (factor_order s u)) (eqToIso (factor_order t u))
      (eqToIso ιK) (eqToIso ιL) (eqToIso (identifyFirst_last u h)) (eqToIso (identifyFirst_last u k)) :=
  jointEndpoint_transports (factor_order s u) (factor_order t u) ιK ιL
    (identifyFirst_last u h) (identifyFirst_last u k)

set_option maxHeartbeats 150000 in
theorem rightRow_joint :
    JointEndpointSquare
      (endpointInterchange (middleComposite (middleComposite M N) (middleComposite M N)) f g)
      (eqToIso (factor_order (firstMap (Middle.change M f.op.toLoc) N)
        (lastMap M (N.map g.toLoc))))
      (eqToIso (rightRow_change M N f.op.toLoc (column (middleComposite M N) c)))
      (eqToIso (rightRow_change M N f.op.toLoc (column (middleComposite M N) d)))
      (eqToIso (identifyFirst_last ((middleComposite M N).map g.toLoc) (middleRow M N b)))
      (eqToIso (identifyFirst_last ((middleComposite M N).map g.toLoc) (middleRow M N a))) := by
  rw [middleComposite_endpointInterchange]
  exact identifyFirst_joint (middleRow M N b) (middleRow M N a)
    (Middle.change (middleComposite M N) f.op.toLoc) (firstMap (Middle.change M f.op.toLoc) N)
    ((middleComposite M N).map g.toLoc) _ _
end JointEndpointPinsSection

section JointContractionSection
universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]
private theorem interchanger_app
    {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    {G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (t : F ⟶ F') (s : G ⟶ G')
    (x : Tensor F G) :
    (eqToIso (factor_order t s)).hom.app x = 𝟙 _ :=
  Parametric.interchange_app t s x

private theorem contractionFactorsSwap {A D Z : Type*} [Category* A] [Category* D] [Category* Z]
    (J : A × D ⥤ Z) {a a' : A} {d d' : D} (p : a ⟶ a') (q : d ⟶ d') :
    J.map (productMap (𝟙 a) q) ≫ J.map (productMap p (𝟙 d')) =
      J.map (productMap p (𝟙 d)) ≫ J.map (productMap (𝟙 a') q) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg J.map (Prod.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm))

set_option maxHeartbeats 125000 in
private theorem firstThenOutput
    {F F' X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    {G Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}
    (t : F ⟶ F') (t' : X ⟶ X') (r : F ⟶ X) (r' : F' ⟶ X')
    (s' : Y ⟶ Y') (n : G ⟶ Y) (e : t ≫ r' ≅ r ≫ t') (z : Tensor F G) :
    (mapSecond (F := X') s').map ((contractChange t t' r r' n e).hom.app z) =
      (insertion X' Y' z.as.mid).map
        (productMap ((e.hom.as.app ⟨z.as.mid⟩).toNatTrans.app z.as.first)
          (𝟙 ((Second.part s' z.as.mid).obj ((Second.part n z.as.mid).obj z.as.second)))) := by
  erw [contractChange_hom_app, Second.on_native, Functor.map_id]

set_option maxHeartbeats 125000 in
private theorem lastThenInput
    {F X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    {G G' Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}
    (t' : X ⟶ X') (r : F ⟶ X) (s : G ⟶ G') (s' : Y ⟶ Y')
    (n : G ⟶ Y) (n' : G' ⟶ Y') (h : s ≫ n' ≅ n ≫ s') (z : Tensor F G) :
    (mapFirst (G := Y') t').map ((contractChangeLast r s s' n n' h).hom.app z) =
      (insertion X' Y' z.as.mid).map
        (productMap (𝟙 ((First.part t' z.as.mid).obj ((First.part r z.as.mid).obj z.as.first)))
          ((h.hom.as.app ⟨op z.as.mid⟩).toNatTrans.app z.as.second)) := by
  erw [contractChangeLast_app, First.on_native, Functor.map_id]

set_option maxHeartbeats 250000 in
private theorem contractChange_core
    {F F' X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    {G G' Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}
    (t : F ⟶ F') (t' : X ⟶ X') (r : F ⟶ X) (r' : F' ⟶ X')
    (s : G ⟶ G') (s' : Y ⟶ Y') (n : G ⟶ Y) (n' : G' ⟶ Y')
    (e : t ≫ r' ≅ r ≫ t') (h : s ≫ n' ≅ n ≫ s') (z : Tensor F G) :
      (contractChangeLast r' s s' n n' h).hom.app ((mapFirst (G := G) t).obj z) ≫
        (mapSecond (F := X') s').map ((contractChange t t' r r' n e).hom.app z) =
      (contractChange t t' r r' n' e).hom.app ((mapSecond (F := F) s).obj z) ≫
        (mapFirst (G := Y') t').map ((contractChangeLast r s s' n n' h).hom.app z) := by
  have L := contractChangeLast_app r' s s' n n' h ((mapFirst (G := G) t).obj z)
  have R := contractChange_hom_app t t' r r' n' e ((mapSecond (F := F) s).obj z)
  refine (congrArg₂ (· ≫ ·) L (firstThenOutput t t' r r' s' n e z)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· ≫ ·) R (lastThenInput t' r s s' n n' h z)).symm
  exact contractionFactorsSwap (insertion X' Y' z.as.mid)
    ((e.hom.as.app ⟨z.as.mid⟩).toNatTrans.app z.as.first)
    ((h.hom.as.app ⟨op z.as.mid⟩).toNatTrans.app z.as.second)

set_option maxHeartbeats 250000 in
private theorem contractChange_joint
    {F F' X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    {G G' Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}
    (t : F ⟶ F') (t' : X ⟶ X') (r : F ⟶ X) (r' : F' ⟶ X')
    (s : G ⟶ G') (s' : Y ⟶ Y') (n : G ⟶ Y) (n' : G' ⟶ Y')
    (e : t ≫ r' ≅ r ≫ t') (h : s ≫ n' ≅ n ≫ s') :
    JointEndpointSquare (eqToIso (factor_order t s)) (eqToIso (factor_order t' s'))
      (contractChange t t' r r' n e) (contractChange t t' r r' n' e)
      (contractChangeLast r s s' n n' h) (contractChangeLast r' s s' n n' h) := by
  intro z
  rw [interchanger_app, interchanger_app]
  erw [Functor.map_id, Category.id_comp, Category.comp_id]
  exact contractChange_core t t' r r' s s' n n' e h z


section ActualContract
universe vM uM vN uN
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
variable {a b c d : B} (f : a ⟶ b) (g : c ⟶ d)

set_option maxHeartbeats 100000 in
theorem mixedContraction_joint :
    JointEndpointSquare
      (eqToIso (factor_order (firstMap (Middle.change M f.op.toLoc) M)
        (lastMap N (N.map g.toLoc))))
      (eqToIso (factor_order (Middle.change M f.op.toLoc) (N.map g.toLoc)))
      (mixedContractionInput.{v,u,vM,uM,vN,uN} M N m n f c)
      (mixedContractionInput.{v,u,vM,uM,vN,uN} M N m n f d)
      (mixedContractionOutput.{v,u,vM,uM,vN,uN} M N m n b g)
      (mixedContractionOutput.{v,u,vM,uM,vN,uN} M N m n a g) :=
  contractChange_joint (firstMap (Middle.change M f.op.toLoc) M) (Middle.change M f.op.toLoc)
    (rowMultiplication.{v,u,vM,uM} M m b) (rowMultiplication.{v,u,vM,uM} M m a)
    ((middleComposite N N).map g.toLoc) (N.map g.toLoc) (n.app ⟨c⟩) (n.app ⟨d⟩)
    (rowMultiplication_change.{v,u,vM,uM} M m f) (n.naturality g.toLoc)

end ActualContract
end JointContractionSection

section JointCrossingStripSection
universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (t : X ⟶ X')
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable {Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (w : Y ⟶ Y')

set_option maxHeartbeats 150000 in
private theorem exposedCrossing_joint (s : middleComposite N M ⟶ middleComposite M N) :
    JointEndpointSquare
      (eqToIso (factor_order (firstMap t (middleComposite N M)) w))
      (eqToIso (factor_order (firstMap t (middleComposite M N)) w))
      (eqToIso (exposedCrossing_input t M N Y s)) (eqToIso (exposedCrossing_input t M N Y' s))
      (eqToIso (factor_order (liftCrossing X M N s) w).symm)
      (eqToIso (factor_order (liftCrossing X' M N s) w).symm) :=
  jointEndpoint_transports
    (factor_order (firstMap t (middleComposite N M)) w)
    (factor_order (firstMap t (middleComposite M N)) w)
    (exposedCrossing_input t M N Y s) (exposedCrossing_input t M N Y' s)
    (factor_order (liftCrossing X M N s) w).symm (factor_order (liftCrossing X' M N s) w).symm

set_option maxHeartbeats 150000 in
private theorem associator_joint_forward :
    JointEndpointSquare
      (eqToIso (factor_order (firstMap t M) w))
      (eqToIso (factor_order t (lastMap M w)))
      (eqToIso (first_naturality t M Y)) (eqToIso (first_naturality t M Y'))
      (eqToIso (last_naturality X M w)) (eqToIso (last_naturality X' M w)) :=
  jointEndpoint_transports (factor_order (firstMap t M) w) (factor_order t (lastMap M w))
    (first_naturality t M Y) (first_naturality t M Y')
    (last_naturality X M w) (last_naturality X' M w)
end JointCrossingStripSection

section JointMateSection
section
variable {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
variable [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
variable [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
variable {i₀ : A₀ ⥤ A₁} {i₁ : A₂ ⥤ A₃} {o₀ : A₀ ⥤ A₂} {o₁ : A₁ ⥤ A₃}
variable {j₀ : B₀ ⥤ B₁} {j₁ : B₂ ⥤ B₃} {p₀ : B₀ ⥤ B₂} {p₁ : B₁ ⥤ B₃}

set_option maxHeartbeats 150000 in
theorem reverseJointEndpointSquare
    (E₀ : A₀ ≌ B₀) (E₁ : A₁ ≌ B₁) (E₂ : A₂ ≌ B₂) (E₃ : A₃ ≌ B₃)
    {a : i₀ ⋙ o₁ ≅ o₀ ⋙ i₁} {b : j₀ ⋙ p₁ ≅ p₀ ⋙ j₁}
    {l₀ : i₀ ⋙ E₁.functor ≅ E₀.functor ⋙ j₀} {l₁ : i₁ ⋙ E₃.functor ≅ E₂.functor ⋙ j₁}
    {r₀ : o₀ ⋙ E₂.functor ≅ E₀.functor ⋙ p₀} {r₁ : o₁ ⋙ E₃.functor ≅ E₁.functor ⋙ p₁}
    (h : JointEndpointSquare a b l₀ l₁ r₀ r₁) :
    JointEndpointSquare b a (reverseInputSquare E₀ E₁ l₀) (reverseInputSquare E₂ E₃ l₁)
      (reverseInputSquare E₀ E₂ r₀) (reverseInputSquare E₁ E₃ r₁) := by
  intro y
  let x := E₀.inverse.obj y
  let I₀ := (reverseInputSquare E₀ E₁ l₀).hom.app y
  let I₁ := (reverseInputSquare E₂ E₃ l₁).hom.app (p₀.obj y)
  let O₀ := (reverseInputSquare E₀ E₂ r₀).hom.app y
  let O₁ := (reverseInputSquare E₁ E₃ r₁).hom.app (j₀.obj y)
  change O₁ ≫ o₁.map I₀ ≫ a.hom.app x = E₃.inverse.map (b.hom.app y) ≫ I₁ ≫ i₁.map O₀
  apply E₃.functor.map_injective
  apply (cancel_mono (l₁.hom.app (o₀.obj x) ≫ j₁.map (r₀.hom.app x) ≫
    j₁.map (p₀.map (E₀.counitIso.hom.app y)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h x]
  have nr := r₁.hom.naturality I₀
  change E₃.functor.map (o₁.map I₀) ≫ r₁.hom.app (i₀.obj x) =
    r₁.hom.app (E₁.inverse.obj (j₀.obj y)) ≫ p₁.map (E₁.functor.map I₀) at nr
  rw [reassoc_of% nr]
  have nb := b.hom.naturality (E₀.counitIso.hom.app y)
  change p₁.map (j₀.map (E₀.counitIso.hom.app y)) ≫ b.hom.app y =
    b.hom.app (E₀.functor.obj x) ≫ j₁.map (p₀.map (E₀.counitIso.hom.app y)) at nb
  rw [← nb]
  have H₀ := reverseInputSquare_counit E₀ E₁ l₀ y
  change E₁.functor.map I₀ ≫ l₀.hom.app x ≫ _ = _ at H₀
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rw [Category.assoc, H₀]
  have H₁ := reverseInputSquare_counit E₁ E₃ r₁ (j₀.obj y)
  change E₃.functor.map O₁ ≫ _ = _ at H₁
  rw [reassoc_of% H₁]
  have nl := l₁.hom.naturality O₀
  change E₃.functor.map (i₁.map O₀) ≫ l₁.hom.app (o₀.obj x) =
    l₁.hom.app (E₂.inverse.obj (p₀.obj y)) ≫ j₁.map (E₂.functor.map O₀) at nl
  rw [reassoc_of% nl]
  have H₂ := reverseInputSquare_counit E₀ E₂ r₀ y
  change E₂.functor.map O₀ ≫ r₀.hom.app x ≫ _ = _ at H₂
  have J₂ := congrArg j₁.map H₂
  simp only [Functor.map_comp] at J₂ ⊢
  rw [J₂]
  have H₃ := reverseInputSquare_counit E₂ E₃ l₁ (p₀.obj y)
  change E₃.functor.map I₁ ≫ _ = _ at H₃
  rw [H₃]
  exact (E₃.counitIso.hom.naturality (b.hom.app y)).symm

end
end JointMateSection

section JointPentagonSection
universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (t : X ⟶ X')
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

private theorem isoIsTransport {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) (p : ∀ z, F.obj z = G.obj z)
    (h : ∀ z, e.hom.app z = eqToHom (p z)) :
    ∃ q : F = G, e = eqToIso q := by
  refine ⟨Functor.ext_of_iso e p h, ?_⟩
  apply Iso.ext
  apply NatTrans.ext
  funext z
  rw [eqToIso.hom, eqToHom_app, h]

private theorem composeTransport {C : Type*} [Category* C] {a b c d : C}
    (p : a = b) (q : c = d) (i : b ≅ c) (e : ∃ r : b = c, i = eqToIso r) :
    ∃ r : a = d, (eqToIso p ≪≫ i ≪≫ eqToIso q) = eqToIso r := by
  obtain ⟨r, hr⟩ := e
  refine ⟨p.trans (r.trans q), ?_⟩
  rw [hr, eqToIso_trans, eqToIso_trans]

private def pentagonNative :=
  (First.homAction _ _ Y).mapIso (outerAssociatorInput t M N)

set_option maxHeartbeats 100000 in
private theorem pentagonNative_component (z : farLeft X M N Y) :
    (pentagonNative t M N Y).hom.app z =
      eqToHom (show ((mapFirst (G := Y) (firstMap (firstMap t M) N ≫ outerAssociator X' M N)).obj z) =
      ((mapFirst (G := Y) (outerAssociator X M N ≫ firstMap t (middleComposite M N))).obj z) from rfl) := by
  change (First.mapCell (G := Y) (outerAssociatorInput t M N).hom.as).app z = 𝟙 _
  rw [First.cell_app, outerAssociatorInput_app]
  exact (insertion (middleBrackets X' M N) Y z.as.mid).map_id _

set_option maxHeartbeats 100000 in
private theorem firstPentagonInput_transport :
    ∃ (q : _), firstPentagonInput t M N Y = eqToIso q :=
  composeTransport
    (First.map_composite (G := Y) (firstMap (firstMap t M) N) (outerAssociator X' M N)).symm
    (First.map_composite (G := Y) (outerAssociator X M N) (firstMap t (middleComposite M N)))
    (pentagonNative t M N Y)
    (isoIsTransport (pentagonNative t M N Y) (fun _ => rfl) (pentagonNative_component t M N Y))

variable {Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (w : Y ⟶ Y')

set_option maxHeartbeats 150000 in
private theorem firstPentagon_joint :
    JointEndpointSquare
      (eqToIso (factor_order (firstMap (firstMap t M) N) w))
      (eqToIso (factor_order (firstMap t (middleComposite M N)) w))
      (firstPentagonInput t M N Y) (firstPentagonInput t M N Y')
      (eqToIso (factor_order (outerAssociator X M N) w).symm)
      (eqToIso (factor_order (outerAssociator X' M N) w).symm) := by
  obtain ⟨p, hp⟩ := firstPentagonInput_transport t M N Y
  obtain ⟨q, hq⟩ := firstPentagonInput_transport t M N Y'
  rw [hp, hq]
  exact jointEndpoint_transports (factor_order (firstMap (firstMap t M) N) w)
    (factor_order (firstMap t (middleComposite M N)) w) p q
    (factor_order (outerAssociator X M N) w).symm
    (factor_order (outerAssociator X' M N) w).symm
end JointPentagonSection

section JointCrossingSection
universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (t : X ⟶ X')
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable {Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (w : Y ⟶ Y')

set_option maxHeartbeats 250000 in
private theorem exposeMiddle_joint :
    JointEndpointSquare
      (eqToIso (factor_order (firstMap t M) (lastMap N w)))
      (eqToIso (factor_order (firstMap t (middleComposite M N)) w))
      (exposeMiddleInput t M N Y) (exposeMiddleInput t M N Y')
      (exposeMiddleOutput X M N w) (exposeMiddleOutput X' M N w) :=
  pasteJointEndpointSquare
    (reverseJointEndpointSquare (associator (leftInner X M) N Y)
      (associator (leftInner X' M) N Y) (associator (leftInner X M) N Y')
      (associator (leftInner X' M) N Y') (associator_joint_forward (firstMap t M) N w))
    (firstPentagon_joint t M N Y w)

set_option maxHeartbeats 250000 in
theorem crossMiddle_joint (s : middleComposite N M ⟶ middleComposite M N) :
    JointEndpointSquare
      (eqToIso (factor_order (firstMap t N) (lastMap M w)))
      (eqToIso (factor_order (firstMap t M) (lastMap N w)))
      (crossMiddleInput t M N Y s) (crossMiddleInput t M N Y' s)
      (crossMiddleOutput X M N w s) (crossMiddleOutput X' M N w s) :=
  pasteJointEndpointSquare (exposeMiddle_joint t N M w)
    (pasteJointEndpointSquare (exposedCrossing_joint t M N w s)
      (reverseJointEndpointSquare (exposeMiddle X M N Y) (exposeMiddle X' M N Y)
        (exposeMiddle X M N Y') (exposeMiddle X' M N Y') (exposeMiddle_joint t M N w)))
end JointCrossingSection

section JointFullSection
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

set_option maxHeartbeats 400000 in
/-- The original mixed comparison commutes with simultaneous endpoint change,
with the actual interchangers of the source and target actions. -/
theorem mixedMultiplicationInputOutput_compatibility
    (s : middleComposite N M ⟶ middleComposite M N)
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
    {a b c d : B} (f : a ⟶ b) (g : c ⟶ d) :
    MixedMultiplicationJoint.{v,u,vM,uM,vN,uN} M N s m n f g := by
  unfold MixedMultiplicationJoint
  dsimp only
  erw [middleComposite_endpointInterchange M N f g]
  exact pasteJointEndpointSquare (rightRow_joint M N f g)
    (pasteJointEndpointSquare (crossMiddle_joint (Middle.change M f.op.toLoc) M N (N.map g.toLoc) s)
      (mixedContraction_joint.{v,u,vM,uM,vN,uN} M N m n f g))
end JointFullSection

end ContextualComposition.RelativeTensor.Iterated
