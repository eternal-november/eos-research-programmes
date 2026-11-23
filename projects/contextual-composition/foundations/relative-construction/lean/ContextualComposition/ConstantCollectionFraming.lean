module
public import ContextualComposition.CanonicalSetStrength
public import ContextualComposition.OrderedArityReflection
public import Mathlib.Algebra.BigOperators.Fin

/-! Explicit shape, ordered-address and strength data for constant ordered
polynomial content in the external framing theorem. -/

@[expose] public section
namespace ContextualComposition.ConstantCollectionFraming
open CategoryTheory OrderedArityReflection CanonicalSetStrength
universe u

structure Point (C : Collection.{u}) (B : Type u) where
  arity : Nat
  shape : C.shape arity
  label : Fin arity → B

def presentation (C : Collection.{u}) (B : Type u) : Value C B ≃ Point C B :=
  (positions C B).trans
    ⟨fun ⟨n,c,f⟩ => ⟨n,c,f⟩,fun ⟨n,c,f⟩ => ⟨n,c,f⟩,fun ⟨_,_,_⟩ => rfl,fun _ => rfl⟩

abbrev extF (C : Collection.{u}) : Type u ⥤ Type u where
  obj B := Point C B
  map f := TypeCat.ofHom fun z => ⟨z.arity,z.shape,fun i => f (z.label i)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def change {C D : Collection.{u}} (f : C ⟶ D) : extF C ⟶ extF D where
  app _ := TypeCat.ofHom fun z => ⟨z.arity,f _ z.shape,z.label⟩
  naturality _ _ _ := rfl

structure TreeShape (C D : Collection.{u}) (n : Nat) where
  outer : Nat
  length : Fin outer → Nat
  root : C.shape outer
  child : ∀ i, D.shape (length i)
  total : ∑ i, length i = n

def sub (C D : Collection.{u}) : Collection.{u} := ⟨TreeShape C D⟩

abbrev Decorations (C D : Collection.{u}) (n : Nat) (v : Σ k, Fin k → Nat) :=
  {_s : C.shape v.1 × (∀ i, D.shape (v.2 i)) // ∑ i, v.2 i = n}

def treeCode (C D : Collection.{u}) (n : Nat) : TreeShape C D n ≃ Σ v, Decorations C D n v where
  toFun t := ⟨⟨t.outer,t.length⟩,⟨t.root,t.child⟩,t.total⟩
  invFun := fun ⟨⟨k,l⟩,⟨⟨s,t⟩,h⟩⟩ => ⟨k,l,s,t,h⟩
  left_inv _ := rfl
  right_inv := fun ⟨⟨_,_⟩,⟨⟨_,_⟩,_⟩⟩ => rfl

theorem sum_positions (l : List Nat) : (∑ i, l.get i) = l.sum := by
  rw [← List.sum_ofFn,List.ofFn_get]

def cutCode (C D : Collection.{u}) (n : Nat) :
    SubShape C D n ≃ Σ l : List Nat, Decorations C D n (List.equivSigmaTuple l) where
  toFun t := ⟨t.lengths,⟨t.outerShape,t.innerShape⟩,(sum_positions _).trans t.sum_eq⟩
  invFun := fun ⟨l,⟨⟨s,t⟩,h⟩⟩ => ⟨l,s,t,(sum_positions l).symm.trans h⟩
  left_inv _ := rfl
  right_inv := fun ⟨_,⟨⟨_,_⟩,_⟩⟩ => rfl

/-- The vector-of-addresses presentation and the ordered-cut presentation
used by the local arity reflection encode exactly the same shapes. -/
def cutEquiv (C D : Collection.{u}) (n : Nat) : TreeShape C D n ≃ SubShape C D n :=
  (treeCode C D n).trans ((Equiv.sigmaCongrLeft (β := Decorations C D n) List.equivSigmaTuple).symm.trans
    (cutCode C D n).symm)

def subMap {C C' D D' : Collection.{u}} (f : C ⟶ C') (g : D ⟶ D') : sub C D ⟶ sub C' D' :=
  fun _ s => ⟨s.outer,s.length,f _ s.root,fun i => g _ (s.child i),s.total⟩

def pack {C D : Collection.{u}} {B : Type u} (z : Point C (Point D B)) : Point (sub C D) B :=
  let l := fun i => (z.label i).arity
  ⟨∑ i, l i,⟨z.arity,l,z.shape,fun i => (z.label i).shape,rfl⟩,
    fun j => let i := (finSigmaFinEquiv (n := l)).symm j; (z.label i.1).label i.2⟩

def unpack {C D : Collection.{u}} {B : Type u} (z : Point (sub C D) B) : Point C (Point D B) :=
  ⟨z.shape.outer,z.shape.root,fun i =>
    ⟨z.shape.length i,z.shape.child i,fun j => z.label (Fin.cast z.shape.total (finSigmaFinEquiv ⟨i,j⟩))⟩⟩

theorem unpack_pack {C D : Collection.{u}} {B : Type u} (z : Point C (Point D B)) : unpack (pack z) = z := by
  cases z with
  | mk n c x =>
    dsimp only [pack,unpack]
    congr 1
    funext i
    let e := finSigmaFinEquiv (n := fun i => (x i).arity)
    let lab (z : Σ i, Fin (x i).arity) := (x z.1).label z.2
    have h : (fun j => lab (e.symm (e ⟨i,j⟩))) = (x i).label :=
      funext fun j => congrArg lab (e.symm_apply_apply ⟨i,j⟩)
    exact congrArg (Point.mk (x i).arity (x i).shape) h

theorem pack_unpack {C D : Collection.{u}} {B : Type u} (z : Point (sub C D) B) : pack (unpack z) = z := by
  obtain ⟨n,⟨m,l,c,d,rfl⟩,b⟩ := z
  change Point.mk _ _ (fun j => b (Fin.cast _ (finSigmaFinEquiv ((finSigmaFinEquiv (n := l)).symm j)))) = _
  simp [unpack]
  rfl

/-- The substitution isomorphism includes the entire outer and inner
shape and is natural on every ordered tuple, including empty blocks. -/
def substitutionIso (C D : Collection.{u}) : extF D ⋙ extF C ≅ extF (sub C D) :=
  NatIso.ofComponents (fun _ => (show Point C (Point D _) ≃ Point (sub C D) _ from
    ⟨pack,unpack,unpack_pack,pack_unpack⟩).toIso) (by intros; rfl)

theorem read_address {C D : Collection.{u}} {B : Type u} (z : Point C (Point D B))
    (i : Fin z.arity) (j : Fin (z.label i).arity) :
    (pack z).label (finSigmaFinEquiv ⟨i,j⟩) = (z.label i).label j :=
  congrArg (fun q : Σ h, Fin (z.label h).arity => (z.label q.1).label q.2)
    ((finSigmaFinEquiv (n := fun k => (z.label k).arity)).symm_apply_apply ⟨i,j⟩)

/-- Changes of bracketing on bodies are the actual iterated substitution
isomorphisms. Their middle chart is the unchanged three-level polynomial
value, including the shape of every node. -/
def reassociate (C D E : Collection.{u}) :
    extF (sub (sub C D) E) ≅ extF (sub C (sub D E)) :=
  (substitutionIso (sub C D) E).symm ≪≫ Functor.isoWhiskerLeft (extF E) (substitutionIso C D).symm ≪≫
    (Functor.associator (extF E) (extF D) (extF C)).symm ≪≫
    Functor.isoWhiskerRight (substitutionIso D E) (extF C) ≪≫ substitutionIso C (sub D E)

theorem reassociate_frame (C D E : Collection.{u}) (X B : Type u) :
    (frame X).map ((reassociate C D E).hom.app B) ≫ (strength (extF (sub C (sub D E))) X).app B =
      (strength (extF (sub (sub C D) E)) X).app B ≫ (reassociate C D E).hom.app (X × B) :=
  respects _ _ _ _ _

theorem pack_shape_naturality {C C' D D' : Collection.{u}} (f : C ⟶ C') (g : D ⟶ D') {B : Type u}
    (z : Point C (Point D B)) :
    (change (subMap f g)).app B (pack z) =
      pack ((change f).app _ ((extF C).map ((change g).app B) z)) := rfl

def listBody {C : Collection.{u}} {B : Type u} (p : Point C B) := List.ofFn p.label

theorem strength_formula (C : Collection.{u}) {X B : Type u} (x : X) (p : Point C B) :
    (strength (extF C) X).app B (x,p) = ⟨p.arity,p.shape,fun i => (x,p.label i)⟩ := rfl

theorem parameter_square (C : Collection.{u}) {X Y : Type u} (h : X → Y) (A : Type u) :
    (reparam h).app ((extF C).obj A) ≫ (strength (extF C) Y).app A =
      (strength (extF C) X).app A ≫ (extF C).map ((reparam h).app A) := parameter _ h A

theorem shape_square {C C' : Collection.{u}} (f : C ⟶ C') (X B : Type u) :
    (frame X).map ((change f).app B) ≫ (strength (extF C') X).app B =
      (strength (extF C) X).app B ≫ (change f).app (X × B) := respects _ _ _ _ _

theorem strength_compose (C D : Collection.{u}) (X B : Type u) :
    (frame X).map ((substitutionIso C D).hom.app B) ≫ (strength (extF (sub C D)) X).app B =
      (strength (extF C) X).app ((extF D).obj B) ≫
      (extF C).map ((strength (extF D) X).app B) ≫ (substitutionIso C D).hom.app (X × B) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨x,z⟩
  rfl

theorem framed_leaves (C : Collection.{u}) {X B : Type u} (x : X) (p : Point C B) :
    listBody ((strength (extF C) X).app B (x,p)) = (listBody p).map (Prod.mk x) := by
  change List.ofFn (fun i => (x,p.label i)) = (List.ofFn p.label).map _
  rw [List.map_ofFn]
  rfl

def unary {B : Type u} (b : B) : Point OrderedArityReflection.identity B := ⟨1,⟨⟨rfl⟩⟩,fun _ => b⟩

def readUnary {B : Type u} (z : Point OrderedArityReflection.identity B) : B :=
  z.label (Fin.cast z.shape.down.down.symm 0)

theorem unary_read {B : Type u} (z : Point OrderedArityReflection.identity B) : unary (readUnary z) = z := by
  obtain ⟨n,⟨⟨hn⟩⟩,f⟩ := z
  subst n
  refine congrArg (Point.mk 1 _) (funext fun i => congrArg f (Subsingleton.elim (0 : Fin 1) i))

def unaryIso : (𝟭 (Type u)) ≅ extF OrderedArityReflection.identity :=
  NatIso.ofComponents (fun _ => (show _ ≃ _ from ⟨unary,readUnary,fun _ => rfl,unary_read⟩).toIso) (by intros; rfl)

theorem framed_unary {B X : Type u} (x : X) (b : B) :
    (strength (extF OrderedArityReflection.identity) X).app B (x,unary b) = unary (x,b) := rfl

/-- The framed crossing is only claimed over this strength. A two-leaf
point with different colours cannot come from a single external frame. -/
theorem mixed_colours_outside :
    let z : Point terminal (Bool × Unit) := ⟨2,PUnit.unit,fun i => (decide (i.val = 1),())⟩
    ¬ ∃ x : Bool, ∃ p : Point terminal Unit, (strength (extF terminal) Bool).app Unit (x,p) = z := by
  rintro z ⟨x,p,e⟩
  have h := congrArg listBody e
  rw [framed_leaves] at h
  have h₀ : (false,()) ∈ (listBody p).map (Prod.mk x) := h ▸ (by decide : (false,()) ∈ listBody z)
  have h₁ : (true,()) ∈ (listBody p).map (Prod.mk x) := h ▸ (by decide : (true,()) ∈ listBody z)
  obtain ⟨_,_,h₀⟩ := List.mem_map.mp h₀
  obtain ⟨_,_,h₁⟩ := List.mem_map.mp h₁
  exact Bool.noConfusion ((congrArg Prod.fst h₀).symm.trans (congrArg Prod.fst h₁))

theorem nullary_forgets_frame :
    let z : Point terminal Unit := ⟨0,PUnit.unit,Fin.elim0⟩
    (strength (extF terminal) Bool).app Unit (false,z) = (strength (extF terminal) Bool).app Unit (true,z) := by
  dsimp only
  apply congrArg (Point.mk (C := terminal) (B := Bool × Unit) 0 PUnit.unit)
  exact funext fun i => i.elim0

end ContextualComposition.ConstantCollectionFraming
