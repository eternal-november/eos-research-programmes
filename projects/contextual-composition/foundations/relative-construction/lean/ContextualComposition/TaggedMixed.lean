module
public import ContextualComposition.MateLaws
/-! Mixed base/payload coherence on the tagged evaluation operand. Payload
comparison faces in the final equation are arrows, not equalities of objects. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TaggedMixed
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage TelescopeSquares FinalCube

namespace Cube
/-- A map of base/payload squares with specified changes of presentation.
In particular, the payload comparisons need not be equality transports. -/
structure Map (X Y : Mix.Grid) where
  f : X.A ⥤ Y.A
  g : X.D ⥤ Y.D
  f' : X.A' ⥤ Y.A'
  g' : X.D' ⥤ Y.D'
  s : X.b ⋙ f ⟶ g ⋙ Y.b
  t : X.b' ⋙ f' ⟶ g' ⋙ Y.b'
  l : X.p ⋙ f' ⟶ f ⋙ Y.p
  r : X.q ⋙ g' ⟶ g ⋙ Y.q
variable {X Y : Mix.Grid}
def Law (M : Map X Y) : Prop :=
  ∀ x, (M.f'.map (X.cell.app x) ≫ M.t.app (X.q.obj x)) ≫ Y.b'.map (M.r.app x) =
    M.l.app (X.b.obj x) ≫ (Y.p.map (M.s.app x) ≫ Y.cell.app (M.g.obj x))
theorem diagram_iff (M : Map X Y) : Law M ↔
    (whiskerRight X.cell M.f' ≫ whiskerLeft X.q M.t) ≫ whiskerRight M.r Y.b' =
    whiskerLeft X.b M.l ≫ whiskerRight M.s Y.p ≫ whiskerLeft M.g Y.cell :=
  ⟨fun h => NatTrans.ext (funext h),fun h x => NatTrans.congr_app h x⟩
def fromEqualities (M : Mix.Map X Y) : Map X Y :=
  ⟨M.f,M.g,M.f',M.g',M.s,M.t,eqToHom M.pa,eqToHom M.pd⟩
theorem fromDiagram (M : Mix.Map X Y) (h : Mix.Diagram M) : Law (fromEqualities M) := by
  intro x
  change (_ ≫ _) ≫ Y.b'.map ((eqToHom M.pd).app x) = (eqToHom M.pa).app _ ≫ _ ≫ _
  simpa only [eqToHom_app,fromEqualities,Functor.comp_obj] using h x
end Cube
universe b w u v k j
variable {B : Type b} [Category.{w} B] {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z)

namespace Presented
variable {K : Type k} [Category.{j} K] (e p : K ⥤ B) (C : Cleavage p)
noncomputable abbrev pull (Y : Bᵒᵖ ⥤ Cat.{v,u}) {A D : B} (a : A ⟶ D) :=
  FibreTotal.into Y e p D ⋙ Reindex.functor (extendChoice Y e p C) a ⋙ FibreTotal.out Y e p A
noncomputable def square {A D : B} (a : A ⟶ D) :
    pull e p C Y a ⋙ ChainPayload.fibreMap T (FibreTotal.endpoint e p A) ≅
      ChainPayload.fibreMap T (FibreTotal.endpoint e p D) ⋙ pull e p C Z a :=
  NativeCube.present (FibreTotal.into Y e p D) (FibreTotal.out Z e p A) (Reindex.functor (extendChoice Y e p C) a)
    (Reindex.functor (extendChoice Z e p C) a) (PayloadLift.action T e p A) (PayloadLift.action T e p D)
    (FibreTotal.out Y e p A ⋙ ChainPayload.fibreMap T _) (ChainPayload.fibreMap T _ ⋙ FibreTotal.into Z e p D)
    (PayloadLift.square T e p C a) (NativeCube.outSquare T e p A) (EvalPayload.intoSquare T e p D).symm
noncomputable def grid {A D : B} (a : A ⟶ D) : Mix.Grid where
  A := Total Y (FibreTotal.endpoint e p A)
  D := Total Y (FibreTotal.endpoint e p D)
  A' := Total Z (FibreTotal.endpoint e p A)
  D' := Total Z (FibreTotal.endpoint e p D)
  b := pull e p C Y a
  b' := pull e p C Z a
  p := ChainPayload.fibreMap T _
  q := ChainPayload.fibreMap T _
  cell := (square T e p C a).hom
noncomputable def into {A D : B} (a : A ⟶ D) : Mix.Map (grid T e p C a) (fibres T e p C a) where
  f := FibreTotal.into Y e p A
  g := FibreTotal.into Y e p D
  f' := FibreTotal.into Z e p A
  g' := FibreTotal.into Z e p D
  s := 𝟙 _
  t := 𝟙 _
  pa := EvalPayload.intoSquare T e p A
  pd := EvalPayload.intoSquare T e p D
theorem intoLaw {A D : B} (a : A ⟶ D) : Mix.Law (into T e p C a) := by
  intro x
  have h := (Align.stripPresent (FibreTotal.into Y e p D) (FibreTotal.out Z e p A) _ _ _ _ _ _
    (PayloadLift.square T e p C a) (NativeCube.outSquare T e p A) (EvalPayload.intoSquare T e p D).symm x).map
      (FibreTotal.into Z e p A)
  exact (NativeCube.ofEq (Category.comp_id _)).trans (h.trans
    (NativeCube.ofEq (((Category.id_comp _).symm).trans (congrArg (· ≫ _) ((PayloadLift.action T e p A).map_id _).symm))))
end Presented
namespace Zero
noncomputable def full {A D : B} (a : A ⟶ D) :
    Mix.Map (Presented.grid T (𝟭 B) (𝟭 B) baseChoice a) (values T a) where
  f := ZeroPower.eval Y A
  g := ZeroPower.eval Y D
  f' := ZeroPower.eval Z A
  g' := ZeroPower.eval Z D
  s := (ZeroPower.baseSquare Y a).hom
  t := (ZeroPower.baseSquare Z a).hom
  pa := ZeroPower.payloadSquare T A
  pd := ZeroPower.payloadSquare T D
theorem fullLaw {A D : B} (a : A ⟶ D) : Mix.Law (full T a) := by
  let I := Presented.into T (𝟭 B) (𝟭 B) baseChoice a
  let V := FinalCube.decode T a
  apply Mix.replaceLaw (Mix.join I V) _ _ _ _
  · intro x; change (FibreValue.value Y A).map (𝟙 _) ≫ _ = _
    exact (congrArg (· ≫ _) ((FibreValue.value Y A).map_id _)).trans (Category.id_comp _)
  · intro x; change (FibreValue.value Z A).map (𝟙 _) ≫ _ = _
    exact (congrArg (· ≫ _) ((FibreValue.value Z A).map_id _)).trans (Category.id_comp _)
  · exact Mix.joinLaw _ _ (Presented.intoLaw T _ _ _ a) (decodeLaw T a)
theorem diagram {A D : B} (a : A ⟶ D) : Mix.Diagram (full T a) := Mix.equation _ (fullLaw T a)
end Zero
namespace All
open SumChange CoproductSpan.All
variable {Q : Endpoints.{b,w,b,w} B} (R : Q.Split) {Y Z : Bᵒᵖ ⥤ Cat.{w,b}} (T : Y ⟶ Z)
noncomputable def leafSquare {A D : B} (a : A ⟶ D) : (n : Nat) →
    leafPull R Y a n ⋙ leaf R T A n ≅ leaf R T D n ⋙ leafPull R Z a n
  | 0 => Presented.square T (𝟭 B) (𝟭 B) baseChoice a
  | n+1 => NativeCube.presentedSquare R T n a
noncomputable def leafGrid {A D : B} (a : A ⟶ D) (n : Nat) : Mix.Grid where
  A := Total Y (CoproductSpan.leg (src R) (dst R) A n)
  D := Total Y (CoproductSpan.leg (src R) (dst R) D n)
  A' := Total Z (CoproductSpan.leg (src R) (dst R) A n)
  D' := Total Z (CoproductSpan.leg (src R) (dst R) D n)
  b := leafPull R Y a n
  b' := leafPull R Z a n
  p := leaf R T A n
  q := leaf R T D n
  cell := (leafSquare R T a n).hom
noncomputable def leafMap {A D : B} (a : A ⟶ D) (n : Nat) :
    Cube.Map (leafGrid R T a n) (values (ChainPayload.layerMap T R n) a) where
  f := (component R Y A n).functor
  g := (component R Y D n).functor
  f' := (component R Z A n).functor
  g' := (component R Z D n).functor
  s := (componentBase R Y a n).hom
  t := (componentBase R Z a n).hom
  l := (eqToIso (componentPayload R T A n)).inv
  r := (eqToIso (componentPayload R T D n)).inv
-- Conversion in the successor branch compares the presented positive evaluation
-- to its all-length component; the larger elaboration budget is local to this proof.
set_option maxHeartbeats 1000000 in
theorem leafLaw {A D : B} (a : A ⟶ D) : (n : Nat) → Cube.Law (leafMap R T a n)
  | 0 => Cube.fromDiagram (Zero.full T a) (Zero.diagram T a)
  | n+1 => Cube.fromDiagram (FinalCube.full R T n a) (FinalCube.fullDiagram R T n a)

noncomputable def taggedSource {A D : B} (a : A ⟶ D) :=
  Tagged.square (leafPull R Y a) (leafPull R Z a) (leaf R T D) (leaf R T A) (leafSquare R T a)
noncomputable def taggedGrid {A D : B} (a : A ⟶ D) : Mix.Grid where
  A := Σ n, Total Y (CoproductSpan.leg (src R) (dst R) A n)
  D := Σ n, Total Y (CoproductSpan.leg (src R) (dst R) D n)
  A' := Σ n, Total Z (CoproductSpan.leg (src R) (dst R) A n)
  D' := Σ n, Total Z (CoproductSpan.leg (src R) (dst R) D n)
  b := ZeroPower.Sum.map (leafPull R Y a)
  b' := ZeroPower.Sum.map (leafPull R Z a)
  p := ZeroPower.Sum.map (leaf R T A)
  q := ZeroPower.Sum.map (leaf R T D)
  cell := (taggedSource R T a).hom
noncomputable def tagged {A D : B} (a : A ⟶ D) :
    Cube.Map (taggedGrid R T a) (values (ChainPayload.allIterateMap T R) a) where
  f := (ZeroPower.Sum.equiv (component R Y A)).functor
  g := (ZeroPower.Sum.equiv (component R Y D)).functor
  f' := (ZeroPower.Sum.equiv (component R Z A)).functor
  g' := (ZeroPower.Sum.equiv (component R Z D)).functor
  s := (taggedBase R Y a).hom
  t := (taggedBase R Z a).hom
  l := (taggedPayload R T A).inv
  r := (taggedPayload R T D).inv
theorem targetApp {A D : B} (a : A ⟶ D) (n : Nat) (x : (Iterates.layer Q R Y n).obj (op D)) :
    (eqToHom (DecoderCube.natural (ChainPayload.allIterateMap T R) a)).app ⟨n,x⟩ =
    (Iterates.inclusion Q R Z n (op A)).map ((eqToHom (DecoderCube.natural (ChainPayload.layerMap T R n) a)).app x) := by
  refine (eqToHom_app (DecoderCube.natural (ChainPayload.allIterateMap T R) a) _).trans ?_
  exact (congrArg (Iterates.inclusion Q R Z n (op A)).map (eqToHom_app (DecoderCube.natural (ChainPayload.layerMap T R n) a) x)
    |>.trans (eqToHom_map _ _)).symm
theorem taggedLaw {A D : B} (a : A ⟶ D) : Cube.Law (tagged R T a) := by
  rintro ⟨n,x⟩
  let z := (component R Y D n).functor.obj x
  let l := (taggedPayload R T A).inv.app ((ZeroPower.Sum.map (leafPull R Y a)).obj ⟨n,x⟩)
  let m := (ZeroPower.Sum.map (SumChange.target R T A)).map ((taggedBase R Y a).hom.app ⟨n,x⟩)
  refine Eq.trans ?_ (congrArg (fun c => l ≫ m ≫ c) (targetApp R T a n z).symm)
  exact congrArg Sigma.SigmaHom.mk (leafLaw R T a n x)

/-- Equality of the two three-face pastes with the actual base and payload
comparisons of the tagged evaluations and actual iterate payload naturality. -/
theorem taggedDiagram {A D : B} (a : A ⟶ D) :
    (whiskerRight (taggedSource R T a).hom (ZeroPower.Sum.equiv (component R Z A)).functor ≫
      whiskerLeft (ZeroPower.Sum.map (leaf R T D)) (taggedBase R Z a).hom) ≫
      whiskerRight (taggedPayload R T D).inv (Iterates.packedMap Q R Z a.op) =
    whiskerLeft (ZeroPower.Sum.map (leafPull R Y a)) (taggedPayload R T A).inv ≫
      whiskerRight (taggedBase R Y a).hom (ZeroPower.Sum.map (SumChange.target R T A)) ≫
      whiskerLeft (ZeroPower.Sum.equiv (component R Y D)).functor
        (eqToHom (DecoderCube.natural (ChainPayload.allIterateMap T R) a)) :=
  (Cube.diagram_iff _).mp (taggedLaw R T a)
end All
end ContextualComposition.GrothendieckStep.TaggedMixed
