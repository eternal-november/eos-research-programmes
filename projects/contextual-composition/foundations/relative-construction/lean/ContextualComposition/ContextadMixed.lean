module
public import ContextualComposition.ContextadCoherence
public import ContextualComposition.FinalCube
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadMixed
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue ContextadTotal
open FinalCube
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
universe u v
section Generic
variable {B : Type*} [Category* B]
variable {G H G' H' : Bᵒᵖ ⥤ Cat.{v,u}} (T : G ⟶ G') (U : H ⟶ H')
variable (F : Total G (𝟭 B) ⥤ Total H (𝟭 B)) (F' : Total G' (𝟭 B) ⥤ Total H' (𝟭 B))
variable (over : F ⋙ proj H = proj G) (over' : F' ⋙ proj H' = proj G')
variable (pres : ∀ {x y : Total G (𝟭 B)} (f : x ⟶ y), Cartesian (proj G) f → Cartesian (proj H) (F.map f))
variable (pres' : ∀ {x y : Total G' (𝟭 B)} (f : x ⟶ y), Cartesian (proj G') f → Cartesian (proj H') (F'.map f))
variable (comm : ChainPayload.fibreMap T (𝟭 B) ⋙ F' = F ⋙ ChainPayload.fibreMap U (𝟭 B))
noncomputable def encode {A D : B} (a : A ⟶ D) :
    Mix.Map (values T a) (fibres T (𝟭 B) (𝟭 B) baseChoice a) where
  f := embed G A
  g := embed G D
  f' := embed G' A
  g' := embed G' D
  s := (square G a).hom
  t := (square G' a).hom
  pa := (EvalPayload.embedSquare T A).symm
  pd := (EvalPayload.embedSquare T D).symm
theorem encodeLaw {A D : B} (a : A ⟶ D) : Mix.Law (encode T a) := by
  apply Mix.lawOfEquation
  intro x
  apply pureEq
  · exact pureComp (pureComp (pureMap _ ⟨_,eqToHom_app (DecoderCube.natural T a) x⟩) ⟨_,squareApp _ _ _⟩) (pureMap _ ⟨_,rfl⟩)
  · exact pureComp ⟨_,rfl⟩ (pureComp (pureMap _ ⟨_,squareApp _ _ _⟩)
      (ContextadCoherence.fibrePure G' _ (DecoderCube.squarePure T a _)))
noncomputable def face {A D : B} (a : A ⟶ D) (X V : Bᵒᵖ ⥤ Cat.{v,u})
    (L : Total X (𝟭 B) ⥤ Total V (𝟭 B)) (e : L ⋙ proj V = proj X)
    (p : ∀ {x y} (f : x ⟶ y), Cartesian (proj X) f → Cartesian (proj V) (L.map f)) :
    NativeCube.Face (Route.ofChoice (choice X) a) (Route.ofChoice (choice V) a) L e where
  sq := ContextadCoherence.middle X V L e p a
  fac := NativeCube.changeFac L e _ _ p
include comm in
theorem fibreComm (A : B) :
    PayloadLift.action T (𝟭 B) (𝟭 B) A ⋙ SpanPayload.fibreFunctor F' _ over' A =
      SpanPayload.fibreFunctor F _ over A ⋙ PayloadLift.action U (𝟭 B) (𝟭 B) A := by
  apply EvalPayload.cancelInclusion
  refine (EvalPayload.fibrePaste A _ _ _ _).trans ?_
  exact (congrArg (Functor.Fiber.fiberInclusion ⋙ ·) comm).trans (EvalPayload.fibrePaste A _ _ _ _).symm
noncomputable def inner {A D : B} (a : A ⟶ D) :
    Mix.Map (fibres T (𝟭 B) (𝟭 B) baseChoice a) (fibres U (𝟭 B) (𝟭 B) baseChoice a) :=
  faceMap (NativeCube.payload T _ _ baseChoice a) (face a _ _ F' over' pres')
    (face a _ _ F over pres) (NativeCube.payload U _ _ baseChoice a)
    (fibreComm T U F F' over over' comm A) (fibreComm T U F F' over over' comm D)
theorem innerLaw {A D : B} (a : A ⟶ D) : Mix.Law (inner T U F F' over over' pres pres' comm a) :=
  faceLaw _ _ _ _ _ _ (NativeCube.Face.law _ _ _ _ comm _ _)
noncomputable def decoded {A D : B} (a : A ⟶ D) :
    Mix.Map (values T a) (values U a) :=
  let Q := Mix.join (Mix.join (encode T a) (inner T U F F' over over' pres pres' comm a)) (decode U a)
  { Q with s := (ContextadTotal.valueSquare _ _ F over pres a).hom
           t := (ContextadTotal.valueSquare _ _ F' over' pres' a).hom }
theorem decodedLaw {A D : B} (a : A ⟶ D) : Mix.Law (decoded T U F F' over over' pres pres' comm a) := by
  apply Mix.replaceLaw
  · intro x; simp [Mix.join,encode,inner,faceMap,face,decode,ContextadTotal.valueSquare]
  · intro x; simp [Mix.join,encode,inner,faceMap,face,decode,ContextadTotal.valueSquare]
  · exact Mix.joinLaw _ _ (Mix.joinLaw _ _ (encodeLaw T a) (innerLaw T U F F' over over' pres pres' comm a)) (decodeLaw U a)
theorem mixTransport {X W : Mix.Grid} (F : Mix.Map X W)
    (g : X.D ⥤ W.D) (h : X.A ⥤ W.A) (g' : X.D' ⥤ W.D') (h' : X.A' ⥤ W.A')
    (eg : g = F.g) (eh : h = F.f) (eg' : g' = F.g') (eh' : h' = F.f')
    (i : X.b ⋙ F.f ≅ F.g ⋙ W.b) (j : X.b' ⋙ F.f' ≅ F.g' ⋙ W.b')
    (hi : i.hom = F.s) (hj : j.hom = F.t)
    (s : X.b ⋙ h ≅ g ⋙ W.b) (t : X.b' ⋙ h' ≅ g' ⋙ W.b')
    (hs : s.hom = (ContextadCoherence.transportIso eh eg i).hom)
    (ht : t.hom = (ContextadCoherence.transportIso eh' eg' j).hom)
    (pa : X.p ⋙ h' = h ⋙ W.p) (pd : X.q ⋙ g' = g ⋙ W.q)
    (law : Mix.Law F) :
    Mix.Law ⟨h,g,h',g',s.hom,t.hom,pa,pd⟩ := by
  subst g; subst h; subst g'; subst h'
  have ss : s.hom = F.s := by simpa [ContextadCoherence.transportIso,hi] using hs
  have tt : t.hom = F.t := by simpa [ContextadCoherence.transportIso,hj] using ht
  exact Mix.replaceLaw F s.hom t.hom pa pd
    (fun x => NatTrans.congr_app ss.symm x) (fun x => NatTrans.congr_app tt.symm x) law
include comm in
/-- Transport before instantiating the (large) power charts. -/
theorem decodedTransport {A D : B} (a : A ⟶ D)
    (f : G.obj (op A) ⥤ H.obj (op A)) (g : G.obj (op D) ⥤ H.obj (op D))
    (f' : G'.obj (op A) ⥤ H'.obj (op A)) (g' : G'.obj (op D) ⥤ H'.obj (op D))
    (ef : f = localValue G H F over A) (eg : g = localValue G H F over D)
    (ef' : f' = localValue G' H' F' over' A) (eg' : g' = localValue G' H' F' over' D)
    (pa : (T.app (op A)).toFunctor ⋙ f' = f ⋙ (U.app (op A)).toFunctor)
    (pd : (T.app (op D)).toFunctor ⋙ g' = g ⋙ (U.app (op D)).toFunctor) :
    Mix.Law (X := values T a) (Y := values U a)
      ⟨f,g,f',g',(ContextadCoherence.transportIso ef eg (ContextadTotal.valueSquare G H F over pres a)).hom,
        (ContextadCoherence.transportIso ef' eg' (ContextadTotal.valueSquare G' H' F' over' pres' a)).hom,pa,pd⟩ :=
  mixTransport (decoded T U F F' over over' pres pres' comm a) g f g' f' eg ef eg' ef'
    (ContextadTotal.valueSquare G H F over pres a) (ContextadTotal.valueSquare G' H' F' over' pres' a) rfl rfl
    _ _ rfl rfl pa pd (decodedLaw T U F F' over over' pres pres' comm a)
end Generic
section Actual
open SpanApex NativeBlocks BlockEvaluation
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (m : ContextadTotal.Native S) {Y Z : PackedCuts.Psh.{u,max u v,u,v} B} (T : Y ⟶ Z)
abbrev upstream := ChainPayload.layerMap T S 2
abbrev downstream := ChainPayload.layerMap T S 1
theorem conjugated
    {A B C D AA BB CC DD : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* AA] [Category* BB] [Category* CC] [Category* DD]
    (L : A ⥤ C) (R : B ⥤ D) (V : A ⥤ B)
    (L' : AA ⥤ CC) (R' : BB ⥤ DD) (V' : AA ⥤ BB)
    (p : A ⥤ AA) (q : B ⥤ BB) (y : C ⥤ CC) (z : D ⥤ DD)
    (h : p ⋙ L' = L ⋙ y) (k : q ⋙ R' = R ⋙ z) (b : p ⋙ V' = V ⋙ q)
    [L.IsIso] [L'.IsIso] :
    y ⋙ (L'.strictInv ⋙ V' ⋙ R') = (L.strictInv ⋙ V ⋙ R) ⋙ z := by
  apply L.asIsomorphism.functor_comp_injective
  calc
    _ = (p ⋙ L') ⋙ (L'.strictInv ⋙ V' ⋙ R') := congrArg (· ⋙ _) h.symm
    _ = p ⋙ V' ⋙ R' := by
      change p ⋙ (L' ⋙ L'.strictInv) ⋙ (V' ⋙ R') = _
      exact congrArg (fun k => p ⋙ k ⋙ (V' ⋙ R')) (show L' ⋙ L'.strictInv = 𝟭 _ from L'.asIsomorphism.unit_eq.symm)
    _ = (V ⋙ q) ⋙ R' := congrArg (· ⋙ R') b
    _ = V ⋙ R ⋙ z := congrArg (V ⋙ ·) k
    _ = _ := by
      change _ = (L ⋙ L.strictInv) ⋙ (V ⋙ R ⋙ z)
      exact (congrArg (fun k => k ⋙ (V ⋙ R ⋙ z)) (show L ⋙ L.strictInv = 𝟭 _ from L.asIsomorphism.unit_eq.symm)).symm
theorem totalComm :
    ChainPayload.fibreMap (upstream (S := S) T) (𝟭 B) ⋙ total m Z =
      total m Y ⋙ ChainPayload.fibreMap (downstream (S := S) T) (𝟭 B) :=
  conjugated (global S Y 2) (global S Y 1) (action m Y)
    (global S Z 2) (global S Z 1) (action m Z)
    (ChainPayload.fibreMap T (power S 2).dest) (ChainPayload.fibreMap T (power S 1).dest)
    (ChainPayload.fibreMap (upstream (S := S) T) (𝟭 B)) (ChainPayload.fibreMap (downstream (S := S) T) (𝟭 B))
    (EvalPayload.nativeSquare T S 1) (EvalPayload.nativeSquare T S 0) (ChainPayload.base_square T _ _ m.grade m.delta).symm
open ContextadCoherence
noncomputable abbrev totalMix {A D : B} (a : A ⟶ D) :=
  decoded (upstream (S := S) T) (downstream (S := S) T) (total m Y) (total m Z)
    (totalOver m Y) (totalOver m Z) (totalCart m Y) (totalCart m Z) (totalComm m T) a
noncomputable def actualMix {A D : B} (a : A ⟶ D) :
    Mix.Map (values (upstream (S := S) T) a) (values (downstream (S := S) T) a) where
  f := actual m Y A
  g := actual m Y D
  f' := actual m Z A
  g' := actual m Z D
  s := (ContextadCoherence.exterior m Y a).hom
  t := (ContextadCoherence.exterior m Z a).hom
  pa := (ContextadTensor.binary_natural _ Y T A).symm
  pd := (ContextadTensor.binary_natural _ Y T D).symm
theorem actualLaw {A D : B} (a : A ⟶ D) : Mix.Law (actualMix m T a) :=
  decodedTransport (upstream (S := S) T) (downstream (S := S) T)
    (total m Y) (total m Z) (totalOver m Y) (totalOver m Z) (totalCart m Y) (totalCart m Z) (totalComm m T) a
    (actual m Y A) (actual m Y D) (actual m Z A) (actual m Z D)
    (ContextadFinal.identify m _ Y A (ContextadSpecialize.agrees m A))
    (ContextadFinal.identify m _ Y D (ContextadSpecialize.agrees m D))
    (ContextadFinal.identify m _ Z A (ContextadSpecialize.agrees m A))
    (ContextadFinal.identify m _ Z D (ContextadSpecialize.agrees m D))
    (ContextadTensor.binary_natural _ Y T A).symm (ContextadTensor.binary_natural _ Y T D).symm
theorem actualDiagram {A D : B} (a : A ⟶ D) : Mix.Diagram (actualMix m T a) :=
  Mix.equation _ (actualLaw m T a)
end Actual
end ContextualComposition.GrothendieckStep.ContextadMixed
