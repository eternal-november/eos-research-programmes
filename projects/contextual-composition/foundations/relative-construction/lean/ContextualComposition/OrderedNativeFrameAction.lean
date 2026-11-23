module
public import ContextualComposition.OrderedNativeFraming

/-! The actual Set-frame functors on native hom-categories and their
invertible comparisons over common endpoints. Noninvertible frame
parameters act by reindexing; the native comparison is an isomorphism. -/

@[expose] public section
namespace ContextualComposition.OrderedNativeFrameAction
open CategoryTheory NativeFinitePush ConstantCollectionFraming OrderedNativeFraming
universe u v
set_option backward.isDefEq.respectTransparency false
variable {V : Type u} {K : Coeff.{u,v} V} {P : Push K} {I : V}
variable {A B A' B' C X Y Z : Type u}

instance : Category (Operation P I A B) where
  Hom F G := Square (F := F) (G := G) id id
  id := idSquare
  comp := vert
  id_comp s := Square.ext (funext fun a => AugHom.ident_comp (s.context a)) (Category.id_comp _)
  comp_id s := Square.ext (funext fun a => AugHom.comp_ident (s.context a)) (Category.comp_id _)
  assoc s t r := Square.ext (funext fun a => AugHom.comp_assoc (s.context a) (t.context a) (r.context a)) (Category.assoc ..)

def action (X : Type u) : Operation P I A B ⥤ Operation P I (X × A) (X × B) where
  obj := frameOp X
  map := frameSquare X
  map_id _ := rfl
  map_comp _ _ := rfl

def reindex (f : A' → A) : Operation P I A B ⥤ Operation P I A' B where
  obj := pre f
  map t := ⟨fun a => t.context (f a),t.shape,fun a p => t.body (f a) p⟩

def relabel (f : B → B') : Operation P I A B ⥤ Operation P I A B' where
  obj F := post F f
  map t := ⟨t.context,t.shape,fun a p =>
    congrArg (fun z => (extF _).map (TypeCat.ofHom f) z) (t.body a p)⟩

def parameter (q : X → Y) :
    action (P := P) (I := I) (A := A) (B := B) X ⋙ relabel (Prod.map q id) ≅
      action Y ⋙ reindex (Prod.map q id) :=
  NatIso.ofComponents (fun F => eqToIso (parameter_exact q F)) (by
    intro F G s; change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def unit (A B : Type u) :
    action (P := P) (I := I) (A := A) (B := B) PUnit.{u+1} ⋙ relabel Prod.snd ≅ reindex Prod.snd :=
  NatIso.ofComponents (fun F => eqToIso (unit_exact F)) (by
    intro F G s; change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def associate (X Y A B : Type u) :
    (action (P := P) (I := I) (A := A) (B := B) Y ⋙ action X) ⋙
      relabel (fun (p : X × Y × B) => ((p.1,p.2.1),p.2.2)) ≅
    action (X × Y) ⋙ reindex (fun (p : X × Y × A) => ((p.1,p.2.1),p.2.2)) :=
  NatIso.ofComponents (fun F => eqToIso (assoc_exact X Y F)) (by
    intro F G s; change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

def serialComparison (O : ContextOps P I) (X : Type u) (F : Operation P I A B) (G : Operation P I B C) :
    compose O (frameOp X F) (frameOp X G) ≅ frameOp X (compose O F G) := eqToIso (serial_exact O X F G)

theorem serial_naturality (O : ContextOps P I) (M : MapOps O) (X : Type u)
    {F F' : Operation P I A B} {G G' : Operation P I B C} (s : F ⟶ F') (t : G ⟶ G') :
    horizontal O M ((action X).map s) ((action X).map t) ≫ (serialComparison O X F' G').hom =
      (serialComparison O X F G).hom ≫ (action X).map (horizontal O M s t) := by
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  exact (Category.comp_id _).trans ((frame_horizontal O M X s t).symm.trans
    (Category.id_comp ((action X).map (horizontal O M s t))).symm)

end ContextualComposition.OrderedNativeFrameAction
