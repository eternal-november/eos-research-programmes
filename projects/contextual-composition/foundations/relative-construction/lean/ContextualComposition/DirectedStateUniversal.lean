module

public import ContextualComposition.DirectedStateBalance
public import Mathlib.CategoryTheory.IsoCat

/-! Functor- and transformation-level universal property for directed state balance, natural under postcomposition in its target. -/

@[expose] public section
namespace ContextualComposition.DirectedStateBalance

open CategoryTheory Opposite
universe u v w d uD vD
variable {S : Type u} [Category.{v} S] {F : Diagram.{v,u,w,d} S} {D : Type uD} [Category.{vD} D]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure Cocone (F : Diagram.{v,u,w,d} S) (D : Type uD) [Category.{vD} D] where
  fiber : ∀ i : S, atPair F i i ⥤ D
  bal {i j : S} (h : i ⟶ j) : action F h (𝟙 i) ⋙ fiber i ⟶ action F (𝟙 j) h ⋙ fiber j
  unit {i : S} (x : atPair F i i) : (bal (𝟙 i)).app x = 𝟙 _
  comp {i j k : S} (h : i ⟶ j) (g : j ⟶ k) (x : atPair F k i) :
    (bal (h ≫ g)).app x =
      (fiber i).map ((preComp F h g).hom.app x) ≫ (bal h).app ((action F g (𝟙 i)).obj x) ≫
      (fiber j).map ((middle F h g).hom.app x) ≫ (bal g).app ((action F (𝟙 k) h).obj x) ≫
      (fiber k).map ((postComp F h g).inv.app x)

def restrict (H : Balance F ⥤ D) : Cocone F D where
  fiber i := insertion F i ⋙ H
  bal h := {
    app := fun x => H.map ((slide F h).app x)
    naturality := fun _ _ a => ((H.map_comp _ _).symm.trans
      ((congrArg H.map ((slide F h).naturality a)).trans (H.map_comp _ _))) }
  unit x := by
    change H.map ((Q F).map (slidePath F _ x)) = _
    rw [CategoryTheory.Quotient.sound _ (Relation.unit x),Functor.map_id,Functor.map_id]
    rfl
  comp h g x := by
    have eq := congrArg H.map (CategoryTheory.Quotient.sound _ (Relation.comp h g x))
    simp only [Functor.map_comp] at eq
    exact eq

namespace Cocone

variable (T : Cocone F D)

def graph : Vertex F ⥤q D where
  obj x := (T.fiber x.state).obj x.val
  map t := match t with
    | .native a => (T.fiber _).map a
    | .slide h x => (T.bal h).app x

theorem map_generator {x y : Vertex F} (t : Edge F x y) :
    (Paths.lift T.graph).map (generator F t) = T.graph.map t := Paths.lift_toPath _ (show x ⟶ y from t)

theorem respects {x y : PathCat F} {p q : x ⟶ y} (r : Relation F p q) :
    (Paths.lift T.graph).map p = (Paths.lift T.graph).map q := by
  cases r with
  | nativeId x => rw [map_generator,Functor.map_id]; exact (T.fiber _).map_id x
  | nativeComp a b => rw [Functor.map_comp,map_generator,map_generator,map_generator]; exact ((T.fiber _).map_comp a b).symm
  | natural h a => simp only [Functor.map_comp,nativePath,slidePath,map_generator]; exact (T.bal h).naturality a
  | unit x => rw [map_generator,Functor.map_id]; exact T.unit x
  | comp h g x => simp only [Functor.map_comp,nativePath,slidePath,map_generator]; exact T.comp h g x

def descend : Balance F ⥤ D :=
  CategoryTheory.Quotient.lift _ (Paths.lift T.graph) (fun _ _ _ _ r => T.respects r)

theorem descend_generator {x y : Vertex F} (e : Edge F x y) :
    T.descend.map ((Q F).map (generator F e)) = T.graph.map e := T.map_generator e

end Cocone

theorem descend_restrict (H : Balance F ⥤ D) : (restrict H).descend = H := by
  apply CategoryTheory.Quotient.lift_unique'
  unfold Cocone.descend
  rw [CategoryTheory.Quotient.lift_spec]
  symm; apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro x; rfl
  · intro x y f; cases f <;> rfl

theorem Cocone.ext {a b : Cocone F D} (e : a.fiber = b.fiber)
    (eq : ∀ {i j : S} (h : i ⟶ j) x, (a.bal h).app x ≍ (b.bal h).app x) : a = b := by
  cases a with | mk fa ba ua ca =>
    cases b with | mk fb bb ub cb =>
      cases e
      have eb : @ba = @bb := by funext i j h; apply NatTrans.ext; funext x; exact eq_of_heq (eq h x)
      cases eb
      rfl

theorem restrict_descend (a : Cocone F D) : restrict a.descend = a := by
  apply Cocone.ext
  · funext i; fapply Functor.ext
    · intro x; rfl
    · intro x y f
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
      exact a.descend_generator (Edge.native f)
  · intro i j h x; exact heq_of_eq (a.descend_generator (Edge.slide h x))

@[ext] structure Map (T U : Cocone F D) where
  fiber : ∀ i, T.fiber i ⟶ U.fiber i
  slide {i j} (h : i ⟶ j) (x : atPair F j i) :
    (T.bal h).app x ≫ (fiber j).app ((action F (𝟙 j) h).obj x) =
    (fiber i).app ((action F h (𝟙 i)).obj x) ≫ (U.bal h).app x

instance : Category (Cocone F D) where
  Hom := Map
  id _ := ⟨fun _ => 𝟙 _,by intros; simp⟩
  comp a b := ⟨fun i => a.fiber i ≫ b.fiber i,by
    intro i j h x; simp only [NatTrans.comp_app,← Category.assoc,a.slide]; simp only [Category.assoc,b.slide]⟩
  id_comp a := Map.ext (funext fun _ => Category.id_comp _)
  comp_id a := Map.ext (funext fun _ => Category.comp_id _)
  assoc a b c := Map.ext (funext fun _ => Category.assoc _ _ _)

theorem Map.edge {a b : Cocone F D} (f : Map a b) {x y : Vertex F} (t : Edge F x y) :
    a.graph.map t ≫ (f.fiber y.state).app y.val = (f.fiber x.state).app x.val ≫ b.graph.map t := by
  cases t with
  | native g => exact (f.fiber _).naturality g
  | slide h z => exact f.slide h z

def Map.descend {a b : Cocone F D} (f : Map a b) : a.descend ⟶ b.descend :=
  CategoryTheory.Quotient.natTransLift _ {
    app := fun x => (f.fiber x.state).app x.val
    naturality := by
      intro x y p
      change (Paths.lift a.graph).map p ≫ _ = _ ≫ (Paths.lift b.graph).map p
      induction p with
      | nil => exact (Category.id_comp _).trans (Category.comp_id _).symm
      | cons p t ih =>
        rw [Paths.lift_cons, Paths.lift_cons,Category.assoc,f.edge,← Category.assoc,ih,Category.assoc] }

def restrictFunctor : (Balance F ⥤ D) ⥤ Cocone F D where
  obj := restrict
  map f := ⟨fun i => Functor.whiskerLeft (insertion F i) f,fun h x => f.naturality ((slide F h).app x)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def descendFunctor : Cocone F D ⥤ (Balance F ⥤ D) where
  obj := Cocone.descend
  map := Map.descend
  map_id _ := rfl
  map_comp _ _ := rfl

def liftTransformation {H K : Balance F ⥤ D} (a : Map (restrict H) (restrict K)) : H ⟶ K :=
  eqToHom (descend_restrict H).symm ≫ a.descend ≫ eqToHom (descend_restrict K)

theorem liftTransformation_app {H K : Balance F ⥤ D} (a : Map (restrict H) (restrict K)) (i : S) (x : atPair F i i) :
    (liftTransformation a).app ((insertion F i).obj x) = (a.fiber i).app x := by
  simp only [liftTransformation,NatTrans.comp_app,eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

instance : (restrictFunctor (F := F) (D := D)).IsIso where
  faithful := ⟨by
    intro H K a b e
    apply NatTrans.ext; funext x
    obtain ⟨⟨i,x⟩⟩ := x
    exact congrArg (fun s : Map (restrict H) (restrict K) => (s.fiber i).app x) e⟩
  full := ⟨by
    intro H K a
    refine ⟨liftTransformation a,?_⟩
    apply Map.ext; funext i; apply NatTrans.ext; funext x
    exact liftTransformation_app a i x⟩
  bijective_obj := ⟨fun _ _ e => (descend_restrict _).symm.trans ((congrArg Cocone.descend e).trans (descend_restrict _)),
    fun a => ⟨a.descend,restrict_descend a⟩⟩

/-- The category-valued directed-dinatural universal property uses ordinary arrows for the slides. -/
noncomputable def universalProperty : IsoCat (Balance F ⥤ D) (Cocone F D) := restrictFunctor.asIsomorphism

variable {E : Type*} [Category* E]

def post (a : Cocone F D) (K : D ⥤ E) : Cocone F E where
  fiber i := a.fiber i ⋙ K
  bal h := {
    app := fun x => K.map ((a.bal h).app x)
    naturality := fun _ _ g => (K.map_comp _ _).symm.trans ((congrArg K.map ((a.bal h).naturality g)).trans (K.map_comp _ _)) }
  unit x := (congrArg K.map (a.unit x)).trans (K.map_id _)
  comp h g x := by
    have e := congrArg K.map (a.comp h g x)
    simp only [Functor.map_comp] at e
    exact e

def postFunctor (K : D ⥤ E) : Cocone F D ⥤ Cocone F E where
  obj a := post a K
  map a := ⟨fun i => Functor.whiskerRight (a.fiber i) K,fun h x =>
    (K.map_comp _ _).symm.trans ((congrArg K.map (a.slide h x)).trans (K.map_comp _ _))⟩
  map_id a := by apply Map.ext; funext i; apply NatTrans.ext; funext x; exact K.map_id _
  map_comp a b := by apply Map.ext; funext i; apply NatTrans.ext; funext x; exact K.map_comp _ _

theorem natural_in_target (K : D ⥤ E) :
    (Functor.whiskeringRight (Balance F) D E).obj K ⋙ restrictFunctor = restrictFunctor ⋙ postFunctor K := by
  rfl

end ContextualComposition.DirectedStateBalance
