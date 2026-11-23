module

public import ContextualComposition.NativeMultilimits

/-! Construct limits of families of supplied effects by splitting every component of the underlying family limit over its compatible effects. No limit of the underlying effect functor is required. -/

@[expose] public section
namespace ContextualComposition.NativeFamilyCompletion

open CategoryTheory CategoryTheory.Limits NativeMultilimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u j k
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
abbrev Fam := FormalCoproduct.{w} F.Elements

def strip : Fam F ⥤ FormalCoproduct.{w} C where
  obj A := ⟨A.I,fun i => (A.obj i).obj⟩
  map f := ⟨f.f, fun i => (f.φ i).hom⟩

def components {B : Type*} [Category* B] (A X : FormalCoproduct.{w} B) :
    (A ⟶ X) ≃ (∀ i, Σ j, A.obj i ⟶ X.obj j) where
  toFun f i := ⟨f.f i,f.φ i⟩
  invFun h := ⟨fun i => (h i).1,fun i => (h i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem elem_sigma_ext {I : Type*} (A : F.Elements) (X : I → F.Elements)
    (f g : Σ i, A ⟶ X i)
    (h : (⟨f.1,f.2.hom⟩ : Σ i, A.obj ⟶ (X i).obj) = ⟨g.1,g.2.hom⟩) : f = g := by
  rcases f with ⟨i,f⟩; rcases g with ⟨j,g⟩
  obtain rfl := congrArg Sigma.fst h
  exact congrArg (Sigma.mk i) (Functor.Elements.hom_ext (Sigma.mk.inj_iff.mp h).2.eq)

instance : (strip F).Faithful where
  map_injective {A X f g} h := by
    apply (components A X).injective
    funext i
    exact elem_sigma_ext F _ _ _ _ (congrArg (fun m => components ((strip F).obj A) ((strip F).obj X) m i) h)

variable {J : Type j} [Category.{k} J] (D : J ⥤ Fam F) (s : Cone (D ⋙ strip F))

abbrev Law (i : s.pt.I) := {t : F.obj (s.pt.obj i) //
    ∀ j, F.map ((s.π.app j).φ i) t = ((D.obj j).obj ((s.π.app j).f i)).val}

def limitFamily : Fam F :=
  ⟨Σ i, Law F D s i,fun i => F.elementsMk (s.pt.obj i.1) i.2.val⟩

def erase : (strip F).obj (limitFamily F D s) ⟶ s.pt := ⟨Sigma.fst, fun _ => 𝟙 _⟩

def projection (j : J) : limitFamily F D s ⟶ D.obj j :=
  ⟨fun i => (s.π.app j).f i.1,fun i => Functor.Elements.homMk ((s.π.app j).φ i.1) (i.2.property j)⟩

theorem projection_eq (j : J) : (strip F).map (projection F D s j) = erase F D s ≫ s.π.app j := by
  apply (components _ _).injective
  funext i
  exact congrArg (Sigma.mk _) (Category.id_comp ((s.π.app j).φ i.1)).symm

def cone : Cone D where
  pt := limitFamily F D s
  π := {
    app := projection F D s
    naturality := by
      intro i j f
      refine (Category.id_comp _).trans ?_
      apply (strip F).map_injective
      rw [Functor.map_comp,projection_eq,projection_eq,Category.assoc]
      exact congrArg (erase F D s ≫ ·) (s.w f).symm }

variable (h : IsLimit s)

def baseLift (a : Cone D) : (strip F).obj a.pt ⟶ s.pt := h.lift ((strip F).mapCone a)

theorem eligible (a : Cone D) (i : a.pt.I) :
    ∀ j, F.map ((s.π.app j).φ ((baseLift F D s h a).f i))
      (F.map ((baseLift F D s h a).φ i) (a.pt.obj i).val) =
      ((D.obj j).obj ((s.π.app j).f ((baseLift F D s h a).f i))).val := by
  intro j
  let b := baseLift F D s h a
  have eq : b ≫ s.π.app j = (strip F).map (a.π.app j) := h.fac _ j
  let respects (r : (strip F).obj a.pt ⟶ (strip F).obj (D.obj j)) : Prop :=
    F.map (r.φ i) (a.pt.obj i).val = ((D.obj j).obj (r.f i)).val
  have good : respects (b ≫ s.π.app j) := eq ▸ ((a.π.app j).φ i).map_val
  exact ((congrArg (fun m : F.obj (a.pt.obj i).obj ⟶ _ => m (a.pt.obj i).val)
    (F.map_comp (b.φ i) ((s.π.app j).φ (b.f i)))).symm).trans good

def lift (a : Cone D) : a.pt ⟶ limitFamily F D s :=
  let b := baseLift F D s h a
  ⟨fun i => ⟨b.f i,⟨F.map (b.φ i) (a.pt.obj i).val,eligible F D s h a i⟩⟩,
    fun i => Functor.Elements.homMk (b.φ i) rfl⟩

theorem erase_lift (a : Cone D) : (strip F).map (lift F D s h a) ≫ erase F D s = baseLift F D s h a := by
  apply (components _ _).injective
  funext i
  exact congrArg (Sigma.mk _) (Category.comp_id ((baseLift F D s h a).φ i))

private theorem unique_component (A : F.Elements) (x y : Σ i, A ⟶ (limitFamily F D s).obj i)
    (eq : (⟨x.1.1,x.2.hom⟩ : Σ i, A.obj ⟶ s.pt.obj i) = ⟨y.1.1,y.2.hom⟩) : x = y := by
  rcases x with ⟨⟨i,t⟩,f⟩; rcases y with ⟨⟨j,r⟩,g⟩
  obtain rfl := congrArg Sigma.fst eq
  have e : f.hom = g.hom := (Sigma.mk.inj_iff.mp eq).2.eq
  have et : t = r := Subtype.ext (f.map_val.symm.trans ((congrArg (fun k => F.map k A.val) e).trans g.map_val))
  cases et
  exact congrArg (Sigma.mk _) (Functor.Elements.hom_ext e)

theorem erase_injective {A : Fam F} (f g : A ⟶ limitFamily F D s)
    (eq : (strip F).map f ≫ erase F D s = (strip F).map g ≫ erase F D s) : f = g := by
  apply (components _ _).injective
  funext i
  apply unique_component
  have e := congrArg (fun k => components ((strip F).obj A) s.pt k i) eq
  change (⟨(f.f i).1,(f.φ i).hom ≫ 𝟙 _⟩ : Σ i, (A.obj _).obj ⟶ s.pt.obj i) = ⟨(g.f i).1,(g.φ i).hom ≫ 𝟙 _⟩ at e
  simp only [Category.comp_id] at e
  exact e

/-- Each component of a candidate cone selects its own uniquely determined law at the underlying family limit. -/
def isLimit : IsLimit (cone F D s) where
  lift := lift F D s h
  fac a j := by
    apply (strip F).map_injective
    change (strip F).map (lift F D s h a ≫ projection F D s j) = _
    rw [Functor.map_comp,projection_eq,← Category.assoc,erase_lift]
    exact h.fac _ j
  uniq a f eq := by
    apply erase_injective
    rw [erase_lift]
    apply h.hom_ext
    intro i
    rw [Category.assoc, ← projection_eq, ← Functor.map_comp]
    exact (congrArg (strip F).map (eq i)).trans (h.fac ((strip F).mapCone a) i).symm

/-- Finite limits in the unmarked family base suffice for finite limits of all families of marked objects. -/
theorem family_finite [HasFiniteLimits (FormalCoproduct.{w} C)] : HasFiniteLimits (Fam F) where
  out _ _ _ := ⟨fun D => ⟨⟨cone F D (limit.cone (D ⋙ strip F)), isLimit F D _ (limit.isLimit _)⟩⟩⟩

private theorem famLimits (V : Type*) [Category* V] [HasFiniteLimits V] : HasFiniteLimits (FormalCoproduct.{w} V) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

theorem native_family_finite (T : Type w ⥤ Type w) (V : Type u) [Category.{v} V] [HasFiniteLimits V] :
    HasFiniteLimits (FormalCoproduct.{w} (Native T V)) := by
  let := famLimits.{w} V
  let := famLimits.{w} (FormalCoproduct.{w} V)
  exact family_finite (raw V ⋙ T)

section Singletons

variable (E : J ⥤ F.Elements) (b : Cone (Base F E)) (l : IsLimit b)

def singletonCone : Cone (E ⋙ FormalCoproduct.incl.{w} F.Elements) where
  pt := family F E b
  π := {
    app := fun j => ⟨fun _ => PUnit.unit, fun t => (NativeMultilimits.projection F E b t).app j⟩
    naturality := by
      intro i j f; refine (Category.id_comp _).trans ?_
      apply (components _ _).injective; funext t
      exact congrArg (Sigma.mk PUnit.unit) ((Category.id_comp _).symm.trans ((NativeMultilimits.projection F E b t).naturality f)) }

def componentCone (a : Cone (E ⋙ FormalCoproduct.incl.{w} F.Elements)) (i : a.pt.I) :
    FixedCone E (a.pt.obj i) where
  app j := (a.π.app j).φ i
  naturality _ j f := (Category.id_comp _).trans
    (congrArg (fun m : a.pt ⟶ (FormalCoproduct.incl _).obj (E.obj j) => (show a.pt.obj i ⟶ E.obj j from m.φ i)) (a.w f)).symm

def singletonIsLimit : IsLimit (singletonCone F E b) where
  lift a := (components _ _).symm (fun i => factor F E b l _ (componentCone F E a i))
  fac a j := by
    apply (components _ _).injective
    funext i
    have e := congrArg (fun c : FixedCone E (a.pt.obj i) => c.app j)
      ((multilimit F E b l _).apply_symm_apply (componentCone F E a i))
    have idx : (PUnit.unit : PUnit.{w+1}) = (a.π.app j).f i := Subsingleton.elim _ _
    exact Sigma.ext idx (heq_of_eq e)
  uniq a f hf := by
    apply (components _ _).injective
    funext i
    apply (multilimit F E b l (a.pt.obj i)).injective
    change present F E b _ _ = (multilimit F E b l _) ((multilimit F E b l _).symm _)
    rw [Equiv.apply_symm_apply]
    apply NatTrans.ext; funext j
    exact congrArg (fun m : a.pt ⟶ (FormalCoproduct.incl _).obj (E.obj j) => (show a.pt.obj i ⟶ E.obj j from m.φ i)) (hf j)

end Singletons

end ContextualComposition.NativeFamilyCompletion
