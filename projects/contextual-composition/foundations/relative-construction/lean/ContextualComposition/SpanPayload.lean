module
public import ContextualComposition.SpanArrows
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.SpanPayload
open CategoryTheory CategoryTheory.Functor Opposite
universe b w k j l i u v
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K] {L : Type l} [Category.{i} L]
variable (Y : Bᵒᵖ ⥤ Cat.{v,u}) (r : K ⥤ L) (d : L ⥤ B) {e : K ⥤ B} (h : r ⋙ d = e)

def totalMap : Total Y e ⥤ Total Y d := by
  subst e; exact (Grothendieck.pre (diagram Y d) r.op).op

theorem total_projection : totalMap Y r d h ⋙ gradeProjection = gradeProjection ⋙ r := by subst e; rfl

theorem total_grade {x y : Total Y e} (f : x ⟶ y) :
    HEq (gradeMap ((totalMap Y r d h).map f)) (r.map (gradeMap f)) := by subst e; rfl

theorem total_payload {x y : Total Y e} (f : x ⟶ y) :
    HEq (payloadMap ((totalMap Y r d h).map f)) (payloadMap f) := by subst e; rfl

theorem total_payload_obj (x : Total Y e) :
    HEq (payload Y d ((totalMap Y r d h).obj x)) (payload Y e x) := by subst e; rfl

instance totalIsEquivalence [r.IsEquivalence] : (totalMap Y r d h).IsEquivalence := by
  subst e
  exact (Grothendieck.preEquivalence (diagram Y d) r.asEquivalence.op).op.isEquivalence_functor

theorem total_comp {M : Type*} [Category* M] (s : L ⥤ M) (c : M ⥤ B) (j : s ⋙ c = d) :
    totalMap Y r d h ⋙ totalMap Y s c j =
      totalMap Y (r ⋙ s) c ((congrArg (r ⋙ ·) j).trans h) := by
  subst d; subst e; rfl

variable {Y} {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)
theorem total_payload_natural :
    totalMap Y r d h ⋙ ChainPayload.fibreMap T d = ChainPayload.fibreMap T e ⋙ totalMap Z r d h := by
  subst e; rfl

variable (F : K ⥤ L) {p : K ⥤ B} (q : L ⥤ B) (H : F ⋙ q = p) (A : B)
def fibreFunctor : p.Fiber A ⥤ q.Fiber A := by
  subst p
  exact Functor.Fiber.inducedFunctor (F := Functor.Fiber.fiberInclusion ⋙ F)
    (Functor.Fiber.fiberInclusion_comp_eq_const (p := F ⋙ q) (S := A))

theorem fibre_diagram : fibreFunctor F q H A ⋙ Functor.Fiber.fiberInclusion = Functor.Fiber.fiberInclusion ⋙ F := by subst p; rfl

instance fibreFaithful [F.Faithful] : (fibreFunctor F q H A).Faithful where
  map_injective {x y} f g eq := by
    subst p
    exact Subtype.ext (F.map_injective (congrArg Subtype.val eq))

instance fibreFull [F.Full] : (fibreFunctor F q H A).Full where
  map_surjective {x y} f := by
    subst p
    obtain ⟨g,hg⟩ := F.map_surjective f.val
    have lift : (F ⋙ q).IsHomLift (𝟙 A) g := by
      have hf : q.IsHomLift (𝟙 A) f.val := f.2
      rw [← hg] at hf
      let : q.IsHomLift (𝟙 A) (F.map g) := hf
      exact IsHomLift.of_fac' (F ⋙ q) (𝟙 A) g x.2 y.2 (IsHomLift.fac' q (𝟙 A) (F.map g))
    exact ⟨⟨g,lift⟩,Subtype.ext hg⟩

theorem fibre_obj_surjective (surj : Function.Surjective F.obj) : Function.Surjective (fibreFunctor F q H A).obj := by
  subst p
  rintro ⟨y,hy⟩
  obtain ⟨x,hx⟩ := surj y
  exact ⟨⟨x,(congrArg q.obj hx).trans hy⟩,Subtype.ext hx⟩

theorem fibre_isEquivalence [F.Full] [F.Faithful] (surj : Function.Surjective F.obj) :
    (fibreFunctor F q H A).IsEquivalence := by
  let : (fibreFunctor F q H A).EssSurj :=
    ⟨fun y => by obtain ⟨x,hx⟩ := fibre_obj_surjective F q H A surj y; exact ⟨x,⟨eqToIso hx⟩⟩⟩
  exact {}


include H in
theorem lift_iff {A D : B} (u : A ⟶ D) {x y : K} (k : x ⟶ y) :
    p.IsHomLift u k ↔ q.IsHomLift u (F.map k) := by
  subst p; constructor
  · intro h
    exact IsHomLift.of_fac' q u (F.map k) (IsHomLift.domain_eq (F ⋙ q) u k) (IsHomLift.codomain_eq (F ⋙ q) u k) (IsHomLift.fac' (F ⋙ q) u k)
  · intro h
    exact IsHomLift.of_fac' (F ⋙ q) u k (IsHomLift.domain_eq q u (F.map k)) (IsHomLift.codomain_eq q u (F.map k)) (IsHomLift.fac' q u (F.map k))

include H in
theorem cartesian_iff [F.Full] [F.Faithful] (surj : Function.Surjective F.obj)
    {A D : B} (u : A ⟶ D) {x y : K} (k : x ⟶ y) :
    p.IsStronglyCartesian u k ↔ q.IsStronglyCartesian u (F.map k) := by
  subst p
  constructor
  · intro hc
    refine { toIsHomLift := (lift_iff F q rfl u k).mp hc.toIsHomLift, universal_property' := ?_ }
    intro z a f hf
    obtain ⟨w,rfl⟩ := surj z
    obtain ⟨g,rfl⟩ := F.map_surjective f
    let : (F ⋙ q).IsHomLift (a ≫ u) g := (lift_iff F q rfl _ g).mpr hf
    obtain ⟨t,⟨ht,he⟩,uniq⟩ := hc.universal_property' a g
    refine ⟨F.map t,⟨(lift_iff F q rfl _ t).mp ht,by rw [← F.map_comp,he]⟩,?_⟩
    intro m hm
    obtain ⟨l,rfl⟩ := F.map_surjective m
    apply congrArg F.map
    exact uniq l ⟨(lift_iff F q rfl _ l).mpr hm.1,F.map_injective (by rw [F.map_comp]; exact hm.2)⟩
  · intro hc
    refine { toIsHomLift := (lift_iff F q rfl u k).mpr hc.toIsHomLift, universal_property' := ?_ }
    intro z a f hf
    let : q.IsHomLift (a ≫ u) (F.map f) := (lift_iff F q rfl _ f).mp hf
    obtain ⟨t,⟨ht,he⟩,uniq⟩ := hc.universal_property' a (F.map f)
    obtain ⟨l,rfl⟩ := F.map_surjective t
    refine ⟨l,⟨(lift_iff F q rfl _ l).mpr ht,F.map_injective (by rw [F.map_comp]; exact he)⟩,?_⟩
    intro m hm
    exact F.map_injective (uniq (F.map m) ⟨(lift_iff F q rfl _ m).mp hm.1,by rw [← F.map_comp,hm.2]⟩)

theorem total_obj_surjective (surj : Function.Surjective r.obj) : Function.Surjective (totalMap Y r d h).obj := by
  subst e
  have aux (k : L) (x : Y.obj (op (d.obj k))) : ∃ y, (totalMap Y r d rfl).obj y = pair Y d k x := by
    obtain ⟨l,rfl⟩ := surj k
    exact ⟨pair Y _ l x,rfl⟩
  exact fun x => aux (grade _ _ x) (payload _ _ x)

def pasteIso {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃] {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃}
    {F' : D₁ ⥤ D₂} {G' : D₂ ⥤ D₃} {U : C₁ ⥤ D₁} {V : C₂ ⥤ D₂} {W : C₃ ⥤ D₃}
    (i : F ⋙ V ≅ U ⋙ F') (j : G ⋙ W ≅ V ⋙ G') :
    (F ⋙ G) ⋙ W ≅ U ⋙ (F' ⋙ G') :=
  associator F G W ≪≫ isoWhiskerLeft F j ≪≫ (associator F V G').symm ≪≫
    isoWhiskerRight i G' ≪≫ associator U F' G'

namespace Power
open SpanApex TelescopeSquares
variable {P : Endpoints.{b,w,k,j} B} (S : P.Split) (n : Nat) (A : B)
abbrev native := positivePowers P S n

def nativeEndpoint : (native S n).source.Fiber A ⥤ B := Functor.Fiber.fiberInclusion ⋙ (native S n).dest
def chainsEndpoint : (chainSource S n).Fiber A ⥤ B := Functor.Fiber.fiberInclusion ⋙ chainDest S n

def gradeFunctor : (native S n).source.Fiber A ⥤ (chainSource S n).Fiber A :=
  fibreFunctor (powerComparison S n) (chainSource S n) (comparison_source S n) A

instance gradeIsEquivalence : (gradeFunctor S n A).IsEquivalence :=
  fibre_isEquivalence _ _ _ _ (powerPoints S n).decode.surjective

theorem gradeEndpoint : gradeFunctor S n A ⋙ chainsEndpoint S n A = nativeEndpoint S n A := by
  change (gradeFunctor S n A ⋙ Functor.Fiber.fiberInclusion) ⋙ chainDest S n = _
  rw [show gradeFunctor S n A ⋙ Functor.Fiber.fiberInclusion = _ from fibre_diagram _ _ _ A]
  change Functor.Fiber.fiberInclusion ⋙ (powerComparison S n ⋙ chainDest S n) = _
  rw [comparison_dest]; rfl

variable (Y : Bᵒᵖ ⥤ Cat.{v,u})
def weighted : Total Y (nativeEndpoint S n A) ⥤ Total Y (chainsEndpoint S n A) :=
  totalMap Y _ _ (gradeEndpoint S n A)

instance weightedIsEquivalence : (weighted S n A Y).IsEquivalence :=
  totalIsEquivalence _ _ _ _

noncomputable def weightedEquiv : Total Y (nativeEndpoint S n A) ≌ Total Y (chainsEndpoint S n A) :=
  (weighted S n A Y).asEquivalence

theorem weighted_natural {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z) :
    weighted S n A Y ⋙ ChainPayload.fibreMap T _ = ChainPayload.fibreMap T _ ⋙ weighted S n A Z :=
  total_payload_natural _ _ _ T

def global : Total Y (native S n).dest ⥤ Total Y (chainDest S n) :=
  totalMap Y _ _ (comparison_dest S n)

instance globalIsEquivalence : (global S n Y).IsEquivalence := totalIsEquivalence _ _ _ _

theorem global_source : global S n Y ⋙ gradeProjection ⋙ chainSource S n =
    gradeProjection ⋙ (native S n).source := by
  change (global S n Y ⋙ gradeProjection) ⋙ chainSource S n = _
  rw [show global S n Y ⋙ gradeProjection = _ from total_projection _ _ _ (comparison_dest S n)]
  change gradeProjection ⋙ (powerComparison S n ⋙ chainSource S n) = _
  rw [comparison_source]

theorem global_natural {Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z) :
    global S n Y ⋙ ChainPayload.fibreMap T _ = ChainPayload.fibreMap T _ ⋙ global S n Z :=
  total_payload_natural _ _ _ T
theorem global_cartesian {A D : B} (u : A ⟶ D) {x y : Total Y (native S n).dest} (f : x ⟶ y) :
    (gradeProjection ⋙ (native S n).source).IsStronglyCartesian u f ↔
      (gradeProjection ⋙ chainSource S n).IsStronglyCartesian u ((global S n Y).map f) :=
  cartesian_iff _ _ (global_source S n Y) (total_obj_surjective _ _ _ (powerPoints S n).decode.surjective) u f

def fibreInclude {K : Type*} [Category* K] (p d : K ⥤ B) :
    Total Y (Functor.Fiber.fiberInclusion (p := p) (S := A) ⋙ d) ⥤ Total Y d :=
  totalMap Y _ _ rfl

set_option backward.isDefEq.respectTransparency false in
theorem fibre_global : weighted S n A Y ⋙ fibreInclude A Y (chainSource S n) (chainDest S n) =
    fibreInclude A Y (native S n).source (native S n).dest ⋙ global S n Y := by
  change totalMap Y _ _ (gradeEndpoint S n A) ⋙ totalMap Y _ _ rfl =
    totalMap Y _ _ rfl ⋙ totalMap Y _ _ (comparison_dest S n)
  rw [total_comp Y (gradeFunctor S n A) _ (gradeEndpoint S n A) Functor.Fiber.fiberInclusion _ rfl, total_comp Y Functor.Fiber.fiberInclusion _ rfl (powerComparison S n) _ (comparison_dest S n)]
  congr 1
  exact fibre_diagram _ _ _ A

section Independent
variable (Y : Bᵒᵖ ⥤ Cat.{j,k})
def gradeObj (t : Chain P (n+1) A) : (chainSource S n).Fiber A := ⟨⟨A,t⟩,rfl⟩

def packObj (X : Fibre P Y (n+1) A) : Total Y (chainsEndpoint S n A) :=
  pair _ _ (gradeObj S n A X.chain) X.value

def packOver {X Z : Fibre P Y (n+1) A} {a : A ⟶ A} (h : a = 𝟙 A)
    (f : DecoratedHom Y a X.chain Z.chain X.value Z.value) :
    packObj S n A Y X ⟶ packObj S n A Y Z :=
  arrow (show gradeObj S n A X.chain ⟶ gradeObj S n A Z.chain from
    ⟨⟨a,f.1⟩,IsHomLift.of_fac' _ _ _ rfl rfl (by change a = 𝟙 A ≫ 𝟙 A ≫ 𝟙 A; simpa using h)⟩) f.2

theorem pack_rebase {X Z : Fibre P Y (n+1) A} {a : A ⟶ A} (h : a = 𝟙 A)
    (f : DecoratedHom Y a X.chain Z.chain X.value Z.value) :
    packOver S n A Y (X := X) (Z := Z) rfl (rebaseDecorated Y h f) = packOver S n A Y h f := by subst a; rfl

private theorem payload_ident {K : Type*} [Category* K] {e : K ⥤ B} (x : Total Y e) :
    HEq (payloadMap (𝟙 x)) (𝟙 (payload Y e x)) := by
  change HEq ((Grothendieck.Hom.fiber (𝟙 x.unop)).unop) _
  rw [Grothendieck.id_fiber]
  refine HEq.trans (heq_of_eq (eqToHom_unop (C := (Y.obj (op (e.obj (grade _ _ x))) : Type _)) _)) ?_
  exact eqToHom_heq_id_dom _ _ _

set_option backward.isDefEq.respectTransparency false in
def pack : Fibre.asCat (Y := Y) S (n+1) A ⥤ Total Y (chainsEndpoint S n A) where
  obj := packObj S n A Y
  map {X Z} f := packOver S n A Y (X := X) (Z := Z) rfl f
  map_id X := by
    apply (homEquiv _ _).injective
    refine Sigma.ext (by rfl) ?_
    refine HEq.trans ?_ (payload_ident Y (packObj S n A Y X)).symm
    change HEq (decoratedId S Y X.chain X.value).2 (𝟙 X.value)
    exact eqToHom_heq_id_dom _ _ (by rw [terminal_id,op_id,Y.map_id]; rfl)
  map_comp {X Z W} f g := by
    change packOver S n A Y _ (rebaseDecorated Y _ (decoratedComp S Y f g)) = _
    rw [pack_rebase S n A Y (Category.id_comp (𝟙 A)) (decoratedComp S Y f g)]
    apply (homEquiv _ _).injective
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    symm
    exact payload_comp _ _

theorem packObj_surjective : Function.Surjective (packObj S n A Y) := by
  have aux (k : (chainSource S n).Fiber A) (z : Y.obj (op ((chainsEndpoint S n A).obj k))) :
      ∃ f, packObj S n A Y f = pair Y _ k z := by
    obtain ⟨⟨D,t⟩,h⟩ := k
    change D = A at h
    subst D
    exact ⟨⟨t,z⟩,rfl⟩
  exact fun x => aux (grade _ _ x) (payload _ _ x)

theorem vertical {X Z : Fibre P Y (n+1) A} (f : packObj S n A Y X ⟶ packObj S n A Y Z) :
    (gradeMap f).val.1 = 𝟙 A := by
  exact (@IsHomLift.eq_of_isHomLift _ _ _ _ (chainSource S n) (gradeObj S n A X.chain).val
    (gradeObj S n A Z.chain).val (𝟙 A) (gradeMap f).val (gradeMap f).property).symm

def unpack {X Z : Fibre P Y (n+1) A} (f : packObj S n A Y X ⟶ packObj S n A Y Z) :
    Fibre.Hom X Z :=
  rebaseDecorated Y (vertical S n A Y f)
    (⟨(gradeMap f).val.2,payloadMap f⟩ : DecoratedHom Y (gradeMap f).val.1 X.chain Z.chain X.value Z.value)

set_option backward.isDefEq.respectTransparency false in
theorem pack_unpack {X Z : Fibre P Y (n+1) A} (f : packObj S n A Y X ⟶ packObj S n A Y Z) :
    (pack S n A Y).map (unpack S n A Y f) = f := by
  change packOver S n A Y rfl (rebaseDecorated Y _ _) = _
  rw [pack_rebase S n A Y (vertical S n A Y f)]
  rfl

theorem unpack_pack {X Z : Fibre.asCat (Y := Y) S (n+1) A} (f : X ⟶ Z) :
    unpack S n A Y ((pack S n A Y).map f) = f := rfl

instance packFull : (pack S n A Y).Full where
  map_surjective f := ⟨unpack S n A Y f,pack_unpack S n A Y f⟩
instance packFaithful : (pack S n A Y).Faithful where
  map_injective {X Z} _f _g h := congrArg (unpack S n A Y (X := X) (Z := Z)) h
instance packEssSurj : (pack S n A Y).EssSurj where
  mem_essImage x := by obtain ⟨f,hf⟩ := packObj_surjective S n A Y x; exact ⟨f,⟨eqToIso hf⟩⟩
instance packIsEquivalence : (pack S n A Y).IsEquivalence where

noncomputable def toIterate : Total Y (nativeEndpoint S n A) ≌ (Iterates.layer P S Y (n+1)).obj (op A) :=
  ((weightedEquiv S n A Y).trans (pack S n A Y).asEquivalence.symm).trans (Fibre.equivalence S (n+1) A)

set_option backward.isDefEq.respectTransparency false in
theorem pack_natural {Z : Bᵒᵖ ⥤ Cat.{j,k}} (T : Y ⟶ Z) :
    pack S n A Y ⋙ ChainPayload.fibreMap T _ = ChainPayload.onFibre T S (n+1) A ⋙ pack S n A Z := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    apply (homEquiv _ _).injective
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Aligned.eq
    apply (ChainPayload.fibreMap_payload T _ ((pack S n A Y).map f)).trans
    exact (Aligned.trailing _ _).symm

noncomputable def unpack_natural {Z : Bᵒᵖ ⥤ Cat.{j,k}} (T : Y ⟶ Z) :
    (pack S n A Y).asEquivalence.inverse ⋙ ChainPayload.onFibre T S (n+1) A ≅
      ChainPayload.fibreMap T _ ⋙ (pack S n A Z).asEquivalence.inverse :=
  Iso.isoCompInverse (H := (pack S n A Z).asEquivalence)
    (Iso.inverseCompIso (G := (pack S n A Y).asEquivalence)
      (eqToIso (pack_natural S n A Y T).symm))

noncomputable def toIterate_natural {Z : Bᵒᵖ ⥤ Cat.{j,k}} (T : Y ⟶ Z) :
    (toIterate S n A Y).functor ⋙ ((ChainPayload.layerMap T S (n+1)).app (op A)).toFunctor ≅
      ChainPayload.fibreMap T _ ⋙ (toIterate S n A Z).functor :=
  pasteIso (pasteIso (eqToIso (weighted_natural S n A Y T)) (unpack_natural S n A Y T))
    (eqToIso (ChainPayload.comparison_square T S (n+1) A).symm)

end Independent
end Power
end ContextualComposition.GrothendieckStep.SpanPayload
