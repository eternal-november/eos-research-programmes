module

public import ContextualComposition.NativeFamilyCompletion

/-! Maps of diagrams act on each joint law and on the actual coefficient-limit arrows. Removing an induced law prevents the full universal factorization. -/

@[expose] public section
namespace ContextualComposition.NativeMultilimitComparisons

open CategoryTheory CategoryTheory.Limits NativeMultilimits NativeFamilyCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u j k
variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w} {J : Type j} [Category.{k} J]
  {D E G : J ⥤ F.Elements} (s : Cone (Base F D)) (b : Cone (Base F E)) (l : IsLimit b)

def after (η : D ⟶ E) : Cone (Base F E) where
  pt := s.pt
  π := s.π ≫ Functor.whiskerRight η (Functor.Elements.π F)

def indexMap (η : D ⟶ E) (t : Index F D s) : Index F E b :=
  ⟨F.map (l.lift (after s η)) t.val, fun i => by
    let n := l.lift (after s η)
    calc
      _ = F.map (n ≫ b.π.app i) t.val :=
        (congrArg (fun m : F.obj s.pt ⟶ F.obj (E.obj i).obj => m t.val) (F.map_comp n (b.π.app i))).symm
      _ = F.map (s.π.app i ≫ (η.app i).hom) t.val :=
        congrArg (fun f : s.pt ⟶ (E.obj i).obj => F.map f t.val) (l.fac (after s η) i)
      _ = F.map (η.app i).hom (F.map (s.π.app i) t.val) :=
        congrArg (fun m : F.obj s.pt ⟶ F.obj (E.obj i).obj => m t.val) (F.map_comp _ _)
      _ = (E.obj i).val := (congrArg _ (t.property i)).trans (η.app i).map_val⟩

def transition (η : D ⟶ E) : family F D s ⟶ family F E b :=
  ⟨indexMap s b l η, fun _ => Functor.Elements.homMk (l.lift (after s η)) rfl⟩

theorem transition_projection (η : D ⟶ E) (i : J) :
    transition s b l η ≫ (singletonCone F E b).π.app i =
    (singletonCone F D s).π.app i ≫ (FormalCoproduct.incl F.Elements).map (η.app i) := by
  apply (components _ _).injective
  funext t; apply congrArg (Sigma.mk PUnit.unit); apply Functor.Elements.hom_ext
  exact l.fac (after s η) i

theorem transition_id (h : IsLimit s) : transition s s h (𝟙 D) = 𝟙 _ := by
  apply (singletonIsLimit F D s h).hom_ext
  intro i
  exact (transition_projection s s h (𝟙 D) i).trans ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem transition_comp (c : Cone (Base F G)) (h : IsLimit c) (η : D ⟶ E) (θ : E ⟶ G) :
    transition s b l η ≫ transition b c h θ = transition s c h (η ≫ θ) := by
  apply (singletonIsLimit F G c h).hom_ext
  intro i
  rw [Category.assoc,transition_projection,← Category.assoc,transition_projection,Category.assoc,transition_projection]
  rfl

/-- The component's own native cone detects omission of its index. -/
theorem missing_index (h : IsLimit s) (admitted : Index F D s → Prop) (t : Index F D s) (missing : ¬admitted t) :
    ¬ ∃ (k : Index F D s) (_ : admitted k) (f : joint F D s t ⟶ joint F D s k),
      (Functor.const J).map f ≫ NativeMultilimits.projection F D s k = NativeMultilimits.projection F D s t := by
  rintro ⟨k,good,f,eq⟩
  have same : (⟨k,f⟩ : Σ i, joint F D s t ⟶ joint F D s i) = ⟨t,𝟙 _⟩ := by
    apply (multilimit F D s h _).injective
    exact eq.trans (Category.id_comp _).symm
  have kt : k = t := congrArg Sigma.fst same
  exact missing (kt ▸ good)

end ContextualComposition.NativeMultilimitComparisons
