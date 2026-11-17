module
public import ContextualComposition.MixedEffects
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
@[expose] public section
namespace ContextualComposition.TerminalComma
open CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C]

/-- Literal comma category for terminal context and content grade fibres. -/
abbrev Presentation (X Y : C) :=
  Comma ((Functor.const (Discrete PUnit.{1})).obj X) ((Functor.const (Discrete PUnit.{1})).obj Y)

variable {X Y : C}

theorem hom_eq {f g : Presentation X Y} (a : f ⟶ g) : f.hom = g.hom := by
  simpa using a.w.symm

instance homSubsingleton (f g : Presentation X Y) : Subsingleton (f ⟶ g) where
  allEq a b := Comma.hom_ext a b (Subsingleton.elim _ _) (Subsingleton.elim _ _)

def pack (f : X ⟶ Y) : Presentation X Y := ⟨⟨PUnit.unit⟩, ⟨PUnit.unit⟩, f⟩

theorem pack_hom (f : X ⟶ Y) : (pack f).hom = f := rfl

theorem unpack_pack (f : Presentation X Y) : pack f.hom = f := by
  rcases f with ⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩
  rfl

def decode (X Y : C) : Presentation X Y ⥤ Discrete (X ⟶ Y) where
  obj f := ⟨f.hom⟩
  map a := Discrete.eqToHom (hom_eq a)

def encode (X Y : C) : Discrete (X ⟶ Y) ⥤ Presentation X Y where
  obj f := pack f.as
  map a := eqToHom (congrArg pack (Discrete.eq_of_hom a))

def equivalence (X Y : C) : Presentation X Y ≌ Discrete (X ⟶ Y) where
  functor := decode X Y
  inverse := encode X Y
  unitIso := NatIso.ofComponents (fun f => eqToIso (unpack_pack f).symm)
  counitIso := NatIso.ofComponents (fun f => Iso.refl f)

def transport {X' Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y') :
    Presentation X Y ⥤ Presentation X' Y' where
  obj f := pack (a ≫ f.hom ≫ b)
  map h := eqToHom (congrArg (fun f => pack (a ≫ f ≫ b)) (hom_eq h))

theorem transport_body {X' Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y')
    (f : Presentation X Y) : (transport a b |>.obj f).hom = a ≫ f.hom ≫ b := rfl

theorem transport_id (f : Presentation X Y) :
    (transport (𝟙 X) (𝟙 Y)).obj f = f := by simp [transport, unpack_pack]

theorem transport_comp {X' Y' X'' Y'' : C} (a : X' ⟶ X) (b : Y ⟶ Y')
    (a' : X'' ⟶ X') (b' : Y' ⟶ Y'') (f : Presentation X Y) :
    (transport a' b').obj ((transport a b).obj f) =
      (transport (a' ≫ a) (b ≫ b')).obj f := by simp [transport, pack, Category.assoc]

def transportIdentityIso (X Y : C) : transport (𝟙 X) (𝟙 Y) ≅ 𝟭 (Presentation X Y) :=
  NatIso.ofComponents (fun f => eqToIso (transport_id f))

def transportCompositionIso {X' Y' X'' Y'' : C}
    (a : X' ⟶ X) (b : Y ⟶ Y') (a' : X'' ⟶ X') (b' : Y' ⟶ Y'') :
    transport a b ⋙ transport a' b' ≅ transport (a' ≫ a) (b ≫ b') :=
  NatIso.ofComponents (fun f => eqToIso (transport_comp a b a' b' f))

/-- No distinct body arrows are identified by terminal-grade normalization. -/
abbrev body (f : Presentation X Y) : X ⟶ Y := f.hom

theorem body_injective : Function.Injective (body (X:=X) (Y:=Y)) := by
  intro f g h
  dsimp [body] at h
  rw [← unpack_pack f, ← unpack_pack g, h]

theorem cell_iff_body (f g : Presentation X Y) : Nonempty (f ⟶ g) ↔ f.hom = g.hom := by
  constructor
  · rintro ⟨s⟩; exact hom_eq s
  · intro h; exact ⟨eqToHom (body_injective h)⟩

/-- Every pair of parallel natural transformations into a terminal-fibre
comma category is equal. This derives uniqueness of its coherence cells. -/
theorem coherence {D : Type*} [Category D] {F H : D ⥤ Presentation X Y}
    (a b : F ⟶ H) : a = b := by
  apply NatTrans.ext
  funext d
  exact Subsingleton.elim _ _

namespace Mixed
variable {G : Comonad C} {T : Monad C} (L : MixedRecovery.Law G T)

/-- The ordinary realization of the terminal-grade comma hom categories.
Its homs are comma objects, not a quotient or a chosen scalar observation. -/
structure Realization (L : MixedRecovery.Law G T) where
  obj : C

instance category : Category (Realization L) where
  Hom A B := Presentation (G.obj A.obj) (T.obj B.obj)
  id A := pack (MixedRecovery.pure (𝟙 A.obj))
  comp f g := pack (MixedRecovery.comp L f.hom g.hom)
  id_comp f := by simpa only [pack_hom, MixedRecovery.left_unit] using unpack_pack f
  comp_id f := by simpa only [pack_hom, MixedRecovery.right_unit] using unpack_pack f
  assoc f g h := congrArg pack (MixedRecovery.assoc L f.hom g.hom h.hom)

def toMixed : Realization L ⥤ MixedRecovery.Mixed L where
  obj A := ⟨A.obj⟩
  map f := f.hom

def fromMixed : MixedRecovery.Mixed L ⥤ Realization L where
  obj A := ⟨A.obj⟩
  map f := pack f

def realizationEquivalence : Realization L ≌ MixedRecovery.Mixed L where
  functor := toMixed L
  inverse := fromMixed L
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    simp [toMixed, fromMixed, unpack_pack])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    simp [toMixed, fromMixed, pack_hom])
  functor_unitIso_comp A := by
    simp [toMixed, fromMixed, category, MixedRecovery.category]

def pureFunctor : C ⥤ Realization L where
  obj A := ⟨A⟩
  map a := pack (MixedRecovery.pure a)
  map_comp a b := congrArg pack (MixedRecovery.pure_comp_pure L a b).symm

theorem decode_comp {A B D : Realization L} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).hom = MixedRecovery.comp L f.hom g.hom := rfl

theorem decode_pure {A B : C} (a : A ⟶ B) :
    ((pureFunctor L).map a).hom = MixedRecovery.pure (G:=G) (T:=T) a := rfl

theorem pure_middle_balance {A B B' D : C}
    (f : Presentation (G.obj A) (T.obj B)) (u : B ⟶ B')
    (g : Presentation (G.obj B') (T.obj D)) :
    MixedRecovery.comp L (f.hom ≫ T.map u) g.hom =
      MixedRecovery.comp L f.hom (G.map u ≫ g.hom) := by
  rw [← MixedRecovery.comp_pure L, ← MixedRecovery.pure_comp L]
  exact MixedRecovery.assoc L _ _ _

/-- The literal terminal-fibre endpoint square retains its two grade arrows.
Its comma equation has identity extension maps, but its actual body remains. -/
abbrev NativeSquare {A B A' B' : C}
    (f : Presentation (G.obj A) (T.obj B))
    (g : Presentation (G.obj A') (T.obj B')) (a : A ⟶ A') (b : B ⟶ B') :=
  (⟨f.left, f.right, f.hom ≫ T.map b⟩ : Presentation (G.obj A) (T.obj B')) ⟶
    (⟨g.left, g.right, G.map a ≫ g.hom⟩ : Presentation (G.obj A) (T.obj B'))

def squareEquiv {A B A' B' : C}
    (f : Presentation (G.obj A) (T.obj B))
    (g : Presentation (G.obj A') (T.obj B')) (a : A ⟶ A') (b : B ⟶ B') :
    NativeSquare f g a b ≃ PLift (MixedRecovery.Square f.hom g.hom a b) where
  toFun s := ⟨hom_eq s⟩
  invFun h :=
    { left := eqToHom (Subsingleton.elim _ _)
      right := eqToHom (Subsingleton.elim _ _)
      w := by simpa using h.down.symm }
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def vertical {A B A' B' A'' B'' : C}
    {f : Presentation (G.obj A) (T.obj B)}
    {g : Presentation (G.obj A') (T.obj B')}
    {h : Presentation (G.obj A'') (T.obj B'')}
    {a : A ⟶ A'} {b : B ⟶ B'} {a' : A' ⟶ A''} {b' : B' ⟶ B''}
    (s : NativeSquare f g a b) (t : NativeSquare g h a' b') :
    NativeSquare f h (a ≫ a') (b ≫ b') :=
  (squareEquiv f h _ _).symm ⟨MixedRecovery.vertical
    ((squareEquiv f g _ _) s).down ((squareEquiv g h _ _) t).down⟩

def horizontal {A B D A' B' D' : C}
    {f : Presentation (G.obj A) (T.obj B)} {g : Presentation (G.obj B) (T.obj D)}
    {f' : Presentation (G.obj A') (T.obj B')} {g' : Presentation (G.obj B') (T.obj D')}
    {a : A ⟶ A'} {b : B ⟶ B'} {d : D ⟶ D'}
    (s : NativeSquare f f' a b) (t : NativeSquare g g' b d) :
    NativeSquare (pack (MixedRecovery.comp L f.hom g.hom))
      (pack (MixedRecovery.comp L f'.hom g'.hom)) a d :=
  (squareEquiv _ _ _ _).symm ⟨MixedRecovery.horizontal L
    ((squareEquiv f f' _ _) s).down ((squareEquiv g g' _ _) t).down⟩

def mixedPureFunctor : C ⥤ MixedRecovery.Mixed L where
  obj A := ⟨A⟩
  map a := MixedRecovery.pure a
  map_comp a b := (MixedRecovery.pure_comp_pure L a b).symm

theorem pure_comparison : pureFunctor L ⋙ toMixed L = mixedPureFunctor L := rfl

theorem square_iff_quintet {A B A' B' : C}
    (f : Presentation (G.obj A) (T.obj B))
    (g : Presentation (G.obj A') (T.obj B')) (a : A ⟶ A') (b : B ⟶ B') :
    Nonempty (NativeSquare f g a b) ↔
      MixedRecovery.comp L f.hom (MixedRecovery.pure b) =
        MixedRecovery.comp L (MixedRecovery.pure a) g.hom := by
  rw [← MixedRecovery.square_iff_quintet L]
  constructor
  · rintro ⟨s⟩; exact ((squareEquiv f g a b) s).down
  · intro h; exact ⟨(squareEquiv f g a b).symm ⟨h⟩⟩

def multiplication (A B D : C) :
    Presentation (G.obj A) (T.obj B) × Presentation (G.obj B) (T.obj D) ⥤
      Presentation (G.obj A) (T.obj D) where
  obj f := pack (MixedRecovery.comp L f.1.hom f.2.hom)
  map s := eqToHom (congrArg pack (congrArg₂ (MixedRecovery.comp L)
    (hom_eq s.1) (hom_eq s.2)))

theorem interchange {A B D A' B' D' A'' B'' D'' : C}
    {f : Presentation (G.obj A) (T.obj B)} {g : Presentation (G.obj B) (T.obj D)}
    {f' : Presentation (G.obj A') (T.obj B')} {g' : Presentation (G.obj B') (T.obj D')}
    {f'' : Presentation (G.obj A'') (T.obj B'')} {g'' : Presentation (G.obj B'') (T.obj D'')}
    {a : A ⟶ A'} {b : B ⟶ B'} {d : D ⟶ D'}
    {a' : A' ⟶ A''} {b' : B' ⟶ B''} {d' : D' ⟶ D''}
    (s : NativeSquare f f' a b) (t : NativeSquare g g' b d)
    (s' : NativeSquare f' f'' a' b') (t' : NativeSquare g' g'' b' d') :
    vertical (horizontal L s t) (horizontal L s' t') =
      horizontal L (vertical s s') (vertical t t') := Subsingleton.elim _ _

end Mixed
end ContextualComposition.TerminalComma
