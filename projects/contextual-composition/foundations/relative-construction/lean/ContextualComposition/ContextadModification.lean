module
public import ContextualComposition.ContextadNativeLaws
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadModification
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue ContextadLawTransport TelescopeSquares
set_option backward.isDefEq.respectTransparency false
universe u v
section Fibre
variable {K L B : Type*} [Category* K] [Category* L] [Category* B]
variable {p : K ⥤ B} {q : L ⥤ B} (F G : K ⥤ L) (h : F ⋙ q = p) (k : G ⋙ q = p)
variable (i : F ≅ G) (v : ∀ x, Pure (q.map (i.hom.app x)))
theorem fibreAligned (A : B) (x : p.Fiber A) :
    Aligned (((onFiber F G h k i v A).hom.app x).val) (i.hom.app x.val) := by
  let left := Functor.congr_obj (SpanPayload.fibre_diagram F q h A) x
  let right := Functor.congr_obj (SpanPayload.fibre_diagram G q k A) x
  refine ⟨left,right,?_⟩
  simp [onFiber,vertical,eqToHom_app]
  rfl
variable (presF : ∀ {x y} (f : x ⟶ y), Cartesian p f → Cartesian q (F.map f))
variable (presG : ∀ {x y} (f : x ⟶ y), Cartesian p f → Cartesian q (G.map f))
theorem fibreMod {A D : B} {a : A ⟶ D} (R : Route p a) (Q : Route q a) (x : p.Fiber D) :
    (Change.square F h R Q presF).hom.app x ≫ Q.act.map ((onFiber F G h k i v D).hom.app x) =
      (onFiber F G h k i v A).hom.app (R.act.obj x) ≫ (Change.square G k R Q presG).hom.app x := by
  apply DecoderCube.CommonLift.compare Q _ _ _ _ _ _ rfl rfl
  exact (((NativeCube.changeFac F h R Q presF x).comp (fibreAligned F G h k i v D x)).trans
    ((NativeCube.ofEq (i.hom.naturality (R.lift x))).trans
    ((fibreAligned F G h k i v A (R.act.obj x)).comp (NativeCube.changeFac G k R Q presG x)).symm)).eq
end Fibre
end ContextualComposition.GrothendieckStep.ContextadModification

namespace ContextualComposition.GrothendieckStep.ContextadModification
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
universe u v
theorem grid {C D : Type*} [Category* C] [Category* D] (V : C ⥤ D)
    {x y z x' y' z' : C} {t t' : D}
    (u : x ⟶ y) (w : y ⟶ z) (u' : x' ⟶ y') (w' : y' ⟶ z')
    (p : x ⟶ x') (q : y ⟶ y') (r : z ⟶ z')
    (l : V.obj z ⟶ t) (l' : V.obj z' ⟶ t') (a : t ⟶ t')
    (e : u ≫ q = p ≫ u') (f : w ≫ r = q ≫ w') (g : V.map r ≫ l' = l ≫ a) :
    (V.map u ≫ V.map w ≫ l) ≫ a = V.map p ≫ V.map u' ≫ V.map w' ≫ l' := by
  simp only [Category.assoc]
  rw [← g, ← Category.assoc (V.map w), ← V.map_comp, f, V.map_comp, Category.assoc,
    ← Category.assoc (V.map u), ← V.map_comp, e, V.map_comp, Category.assoc]
variable {B : Type*} [Category* B] (Y Z : Bᵒᵖ ⥤ Cat.{v,u})
variable (F G : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)) (f : F ⋙ proj Z = proj Y) (g : G ⋙ proj Z = proj Y)
variable (i : F ≅ G) (v : ∀ x, Pure ((proj Z).map (i.hom.app x)))
noncomputable abbrev component (A : B) :=
  isoWhiskerLeft (embed Y A) (isoWhiskerRight (onFiber F G f g i v A) (value Z A))
variable (pf : ∀ {x y} (a : x ⟶ y), Cartesian (proj Y) a → Cartesian (proj Z) (F.map a))
variable (pg : ∀ {x y} (a : x ⟶ y), Cartesian (proj Y) a → Cartesian (proj Z) (G.map a))
theorem decodedMod {A D : B} (a : A ⟶ D) (x : Y.obj (op D)) :
    (ContextadTotal.valueSquare Y Z F f pf a).hom.app x ≫
      (Z.map a.op).toFunctor.map ((component Y Z F G f g i v D).hom.app x) =
    (component Y Z F G f g i v A).hom.app ((Y.map a.op).toFunctor.obj x) ≫
      (ContextadTotal.valueSquare Y Z G g pg a).hom.app x := by
  let R := Route.ofChoice (choice Y) a
  let Q := Route.ofChoice (choice Z) a
  let E := (embed Y D).obj x
  let w := (square Y a).hom.app x
  let M := fun A => (onFiber F G f g i v A).hom
  have s := (valueSquare Z a).hom.naturality ((M D).app E)
  have n := (M A).naturality w
  have b := fibreMod F G f g i v pf pg R Q E
  let V := value Z A
  exact grid V _ _ _ _ _ _ _ _ _ _ n b s
end ContextualComposition.GrothendieckStep.ContextadModification

namespace ContextualComposition.GrothendieckStep.ContextadModification
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type*} [Category* B] (Y Z : Bᵒᵖ ⥤ Cat.{v,u})
variable (F G : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)) (f : F ⋙ proj Z = proj Y) (g : G ⋙ proj Z = proj Y)
variable (i : F ≅ G) (v : ∀ x, Pure ((proj Z).map (i.hom.app x)))
variable (pf : ∀ {x y} (a : x ⟶ y), Cartesian (proj Y) a → Cartesian (proj Z) (F.map a))
variable (pg : ∀ {x y} (a : x ⟶ y), Cartesian (proj Y) a → Cartesian (proj Z) (G.map a))
noncomputable abbrev decodedStrong (p : ∀ {x y} (a : x ⟶ y), Cartesian (proj Y) a → Cartesian (proj Z) (F.map a)) :=
  ContextadStrong.assemble (G := Y) (H := Z) (ContextadTotal.localValue Y Z F f)
    (fun a => ContextadTotal.valueSquare Y Z F f p a) (ContextadCoherence.decodedUnit Y Z F f p)
    (fun a b => ContextadCoherence.decodedComp Y Z F f p a b)
noncomputable def modification :
    Pseudofunctor.StrongTrans.Modification (decodedStrong Y Z F f pf) (decodedStrong Y Z G g pg) where
  app A := (component Y Z F G f g i v A.as.unop).hom.toCatHom₂
  naturality {A D} a := by
    apply Cat.Hom₂.ext
    ext x : 2
    exact (decodedMod Y Z F G f g i v pf pg a.as.unop x).symm
end ContextualComposition.GrothendieckStep.ContextadModification

namespace ContextualComposition.GrothendieckStep.ContextadModification
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue SpanApex NativeBlocks ContextadRoutes ContextadLawTransport ContextadNativeLaws
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u v
section Base
variable {C D B : Type*} [Category* C] [Category* D] [Category* B] {p : C ⥤ B} {q : D ⥤ B}
abbrev Pres (F : C ⥤ D) (p : C ⥤ B) (q : D ⥤ B) := ∀ {x y : C} (f : x ⟶ y), Cartesian p f → Cartesian q (F.map f)
theorem presIso {F G : C ⥤ D} (i : F ≅ G) (h : Pres G p q) : Pres F p q := by
  intro x y f hf
  have e : F.map f = i.hom.app x ≫ G.map f ≫ i.inv.app y := by rw [← reassoc_of% i.hom.naturality, i.hom_inv_id_app,Category.comp_id]
  rw [e]
  exact pasteCart (ContextadCartesian.vertical_cart _) (pasteCart (h f hf) (ContextadCartesian.vertical_cart _))
end Base
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
abbrev gradeCart {i j} (r : Map S i j) := Pres r.grade (power S i).source (power S j).source
def nativeChoice : (i : Nat) → Cleavage (power S i).source
  | 0 => baseChoice
  | i+1 => powerChoice S i
theorem globalPres (Y : PackedCuts.Psh.{u,max u v,u,v} B) {i j} (r : Map S i j) (p : gradeCart r) :
    Pres (global Y r) (proj (PackedFree.pow S Y i)) (proj (PackedFree.pow S Y j)) := by
  intro x y a ha
  apply (BlockCartesian.cartesian_iff (BlockEvaluation.global S Y j) (BlockCartesian.isoIncoming _) _ _).mp
  rw [BlockEvaluation.globalOver]
  apply ContextadCartesian.weightedCartesian Y _ _ r.grade r.leg (nativeChoice (S := S) i) p
  apply (BlockCartesian.cartesian_iff (BlockEvaluation.global S Y i).strictInv (BlockCartesian.isoIncoming _) _ _).mp
  rwa [BoundaryPaste.invOver _ _ _ (BlockEvaluation.globalOver S Y i)]
noncomputable def nativeStrong (Y : PackedCuts.Psh.{u,max u v,u,v} B) {i j} (r : Map S i j) (p : gradeCart r) :=
  decodedStrong _ _ (global Y r) (over Y r) (globalPres Y r p)
noncomputable def nativeModification (Y : PackedCuts.Psh.{u,max u v,u,v} B) {i j} {r t : Map S i j}
    (c : Cell r t) (p : gradeCart r) (q : gradeCart t) :
    Pseudofunctor.StrongTrans.Modification (nativeStrong Y r p) (nativeStrong Y t q) :=
  modification _ _ _ _ _ _ (globalCell Y c) (globalVertical Y c) (globalPres Y r p) (globalPres Y t q)
theorem appendCart {U V : Span (B := B)} (r : Operation U V) (c : Cleavage U.source) (p : Pres r.grade U.source V.source) :
    Pres (appendMap (S := S) r).grade (append P S U).source (append P S V).source :=
  fun _ h => ContextadCartesian.weightedCartesian P.grades _ _ r.grade r.leg c p _ h
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
theorem firstCart : gradeCart (firstTwo m) :=
  appendCart (tensor m) (nativeChoice 2) m.cart
theorem assocCart : gradeCart (comp (firstTwo m) (tensor m)) := fun a h => m.cart _ (firstCart m a h)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
noncomputable def leftMod := nativeModification Y c.left (presIso c.left.grade (fun _ h => h)) (fun _ h => h)
noncomputable def rightMod := nativeModification Y c.right (presIso c.right.grade (fun _ h => h)) (fun _ h => h)
noncomputable def assocMod := nativeModification Y c.assoc (assocCart m) (presIso c.assoc.grade.symm (assocCart m))
end ContextualComposition.GrothendieckStep.ContextadModification
