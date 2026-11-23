module

public import ContextualComposition.DependentConeInterchange

/-! Local-to-global assembly for heterogeneous operation cones. First-stage body equations identify the actual component continuation input before the second-stage witness is transported. -/

@[expose] public section
namespace ContextualComposition.NativeOperationAssembly

open CategoryTheory CouplingPullbacks AllCouplings CouplingChains ConeWiring DependentConeInterchange
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable (T : CategoryTheory.Monad (Type u)) {A B C A' B' C' A'' B'' C'' : Type u}

structure Operation (A B : Type u) where
  context : Ctx T A
  body : Total T context → B

structure Square (P : Operation T A B) (Q : Operation T A' B') (f : A → A') (g : B → B') where
  witness : P.context ⟶ Q.context ∘ f
  body : ∀ (a : A) (w : (P.context a).carrier), g (P.body ⟨a,w⟩) = Q.body ⟨f a,(witness a).run w⟩

variable {T}

@[ext] theorem Square.ext {P : Operation T A B} {Q : Operation T A' B'} {f g} {s t : Square T P Q f g}
    (e : ∀ a x, (s.witness a).run x = (t.witness a).run x) : s = t := by
  have eq : s.witness = t.witness := by
    funext a
    have ext {X Y : Effect T.toFunctor} (k l : StateMap T.toFunctor X Y) (h : k.run = l.run) : k=l := by
      cases k; cases l; cases h; rfl
    exact ext _ _ (funext (e a))
  cases s; cases t; cases eq; rfl

def Square.idSq (P : Operation T A B) : Square T P P id id :=
  ⟨𝟙 P.context,fun _ _ => rfl⟩

def Square.vertical {P : Operation T A B} {Q : Operation T A' B'} {R : Operation T A'' B''}
    {f g f' g'} (s : Square T P Q f g) (t : Square T Q R f' g') : Square T P R (f' ∘ f) (g' ∘ g) :=
  ⟨fun a => (s.witness a) ≫ (t.witness (f a)),fun a w => (congrArg g' (s.body a w)).trans (t.body _ _)⟩

variable (T)

def serial (P : Operation T A B) (Q : Operation T B C) : Operation T A C where
  context := star T P.context (Q.context ∘ P.body)
  body x := Q.body ⟨P.body ⟨x.1,x.2.1⟩,x.2.2⟩

def castMap (P : Ctx T B) {b b' : B} (e : b = b') : P b ⟶ P b' := eqToHom (congrArg P e)

theorem cast_body (P : Operation T B C) {b b' : B} (e : b = b') (x : (P.context b).carrier) :
    P.body ⟨b',(castMap T P.context e).run x⟩ = P.body ⟨b,x⟩ := by subst b'; rfl

variable {T} {P : Operation T A B} {Q : Operation T A' B'} {R : Operation T B C} {S : Operation T B' C'}
  {f : A → A'} {g : B → B'} {k : C → C'}

def conditional (s : Square T P Q f g) (t : Square T R S g k) :
    Conditional T s.witness (R.context ∘ P.body) (fun z => S.context (Q.body ⟨f z.1,z.2⟩)) :=
  fun z => (t.witness (P.body z)) ≫ castMap T S.context (s.body z.1 z.2)

def Square.horizontal (s : Square T P Q f g) (t : Square T R S g k) : Square T (serial T P R) (serial T Q S) f k where
  witness := assemble T s.witness (conditional s t)
  body a w := (t.body (P.body ⟨a,w.1⟩) w.2).trans (cast_body T S (s.body a w.1) _).symm

/-- Retained root operation and all native component projections over specified pure endpoint maps. -/
structure OperationCone {I : Type v} {A B : Type u} {X Y : I → Type u}
    (a : ∀ i, A → X i) (b : ∀ i, B → Y i) (component : ∀ i, Operation T (X i) (Y i)) where
  root : Operation T A B
  proj : ∀ i, Square T root (component i) (a i) (b i)

variable {I : Type v} {X Y Z : I → Type u} {a : ∀ i, A → X i} {b : ∀ i, B → Y i} {c : ∀ i, C → Z i}
  {U : ∀ i, Operation T (X i) (Y i)} {V : ∀ i, Operation T (Y i) (Z i)}

def jointSerial (u : OperationCone a b U) (v : OperationCone b c V) : OperationCone a c (fun i => serial T (U i) (V i)) :=
  ⟨serial T u.root v.root,fun i => (u.proj i).horizontal (v.proj i)⟩

/-- A cell retains the joint effect, the entire root body, and every component projection. -/
structure ConeCell (u u' : OperationCone a b U) where
  root : Square T u.root u'.root id id
  fixes : ∀ i a w, ((u'.proj i).witness a).run ((root.witness a).run w) = ((u.proj i).witness a).run w

theorem cast_heq {X : Type u} (W : Ctx T X) {x y : X} (h : x=y) (v : (W x).carrier) : (castMap T W h).run v ≍ v := by
  subst y; rfl

private theorem witness_heq {f g} (s : Square T P Q f g) {i j : A} (e : i = j)
    {x : (P.context i).carrier} {y : (P.context j).carrier} (h : x ≍ y) :
    (s.witness i).run x ≍ (s.witness j).run y := by subst j; cases eq_of_heq h; rfl

theorem horizontal_second (s : Square T P Q f g) (t : Square T R S g k) (a : A) (x : ((serial T P R).context a).carrier) :
    (((s.horizontal t).witness a).run x).2 ≍ (t.witness (P.body ⟨a,x.1⟩)).run x.2 := cast_heq _ _ _

theorem horizontal_vertical {Q' : Operation T A'' B''} {S' : Operation T B'' C''} {f' g' k'}
    (s : Square T P Q f g) (t : Square T R S g k) (s' : Square T Q Q' f' g') (t' : Square T S S' g' k') :
    (s.horizontal t).vertical (s'.horizontal t') = (s.vertical s').horizontal (t.vertical t') := by
  apply Square.ext
  intro a w
  refine @Sigma.ext _ (fun z : (Q'.context (f' (f a))).carrier => (S'.context (Q'.body ⟨_,z⟩)).carrier)
    ((((s.horizontal t).vertical (s'.horizontal t')).witness a).run w)
    ((((s.vertical s').horizontal (t.vertical t')).witness a).run w) rfl ?_
  exact (horizontal_second s' t' (f a) (((s.horizontal t).witness a).run w)).trans
    ((witness_heq t' (s.body a w.1).symm (horizontal_second s t a w)).trans
      (horizontal_second (s.vertical s') (t.vertical t') a w).symm)

theorem Square.horizontal_id : (Square.idSq P).horizontal (Square.idSq R) = Square.idSq (serial T P R) := rfl

@[ext] theorem ConeCell.ext {d e : OperationCone a b U} {v w : ConeCell d e} (h : v.root = w.root) : v=w := by
  cases v; cases w; cases h; rfl

def ConeCell.idCell (d : OperationCone a b U) : ConeCell d d := ⟨Square.idSq _,fun _ _ _ => rfl⟩

def ConeCell.compCell {d e f : OperationCone a b U} (v : ConeCell d e) (w : ConeCell e f) : ConeCell d f :=
  ⟨v.root.vertical w.root,fun i a z => (w.fixes i a _).trans (v.fixes i a z)⟩

instance : Category (OperationCone a b U) where
  Hom := ConeCell
  id := ConeCell.idCell
  comp := ConeCell.compCell

theorem ConeCell.leg {d e : OperationCone a b U} (v : ConeCell d e) (i : I) :
    v.root.vertical (e.proj i) = d.proj i := Square.ext (v.fixes i)

def serialCell {d d' : OperationCone a b U} {e e' : OperationCone b c V} (v : ConeCell d d') (w : ConeCell e e') :
    ConeCell (jointSerial d e) (jointSerial d' e') where
  root := v.root.horizontal w.root
  fixes i x z := congrArg (fun s : Square T (serial T d.root e.root) (serial T (U i) (V i)) (a i) (c i) => (s.witness x).run z)
    ((horizontal_vertical v.root w.root (d'.proj i) (e'.proj i)).trans (congrArg₂ Square.horizontal (v.leg i) (w.leg i)))

theorem serialCell_comp {d d' d'' : OperationCone a b U} {e e' e'' : OperationCone b c V}
    (v : ConeCell d d') (w : ConeCell e e') (v' : ConeCell d' d'') (w' : ConeCell e' e'') :
    (serialCell v w).compCell (serialCell v' w') = serialCell (v.compCell v') (w.compCell w') :=
  ConeCell.ext (horizontal_vertical _ _ _ _)

theorem serialCell_id (d : OperationCone a b U) (e : OperationCone b c V) :
    serialCell (ConeCell.idCell d) (ConeCell.idCell e) = ConeCell.idCell (jointSerial d e) := ConeCell.ext Square.horizontal_id

variable (T)

def identity (A : Type u) : Operation T A A := ⟨unit T A,Sigma.fst⟩

def leftUnitor (P : Operation T A B) : Square T (serial T (identity T A) P) P id id :=
  ⟨fun a => (leftUnit T P.context a).forward T.toFunctor,fun _ _ => rfl⟩
def rightUnitor (P : Operation T A B) : Square T (serial T P (identity T B)) P id id :=
  ⟨fun a => (rightUnit T P.context a).forward T.toFunctor,fun _ _ => rfl⟩

def leftUnitorInv (P : Operation T A B) : Square T P (serial T (identity T A) P) id id :=
  ⟨fun a => (leftUnit T P.context a).backward T.toFunctor,fun _ _ => rfl⟩
def rightUnitorInv (P : Operation T A B) : Square T P (serial T P (identity T B)) id id :=
  ⟨fun a => (rightUnit T P.context a).backward T.toFunctor,fun _ _ => rfl⟩

theorem unitor_inverse (P : Operation T A B) :
    (leftUnitor T P).vertical (leftUnitorInv T P) = Square.idSq _ ∧
    (leftUnitorInv T P).vertical (leftUnitor T P) = Square.idSq _ ∧
    (rightUnitor T P).vertical (rightUnitorInv T P) = Square.idSq _ ∧
    (rightUnitorInv T P).vertical (rightUnitor T P) = Square.idSq _ :=
  ⟨rfl,rfl,rfl,rfl⟩

def associateOps {D : Type u} (P : Operation T A B) (Q : Operation T B C) (R : Operation T C D) :
    Square T (serial T (serial T P Q) R) (serial T P (serial T Q R)) id id :=
  ⟨assocMap T P.context (Q.context ∘ P.body) (R.context ∘ (serial T P Q).body),fun _ _ => rfl⟩

def unassociateOps {D : Type u} (P : Operation T A B) (Q : Operation T B C) (R : Operation T C D) :
    Square T (serial T P (serial T Q R)) (serial T (serial T P Q) R) id id :=
  ⟨fun a => (associate T P.context (Q.context ∘ P.body) (R.context ∘ (serial T P Q).body) a).backward T.toFunctor,fun _ _ => rfl⟩

theorem associate_inverse {D : Type u} (P : Operation T A B) (Q : Operation T B C) (R : Operation T C D) :
    (associateOps T P Q R).vertical (unassociateOps T P Q R) = Square.idSq _ ∧
    (unassociateOps T P Q R).vertical (associateOps T P Q R) = Square.idSq _ := ⟨rfl,rfl⟩

private theorem pair_heq {D : Type u} (P : Operation T A B) (R : Operation T B D) {a b : A} (hi : a=b)
    (x : ((serial T P R).context a).carrier) (y : ((serial T P R).context b).carrier)
    (h₁ : x.1 ≍ y.1) (h₂ : x.2 ≍ y.2) : x ≍ y := by
  subst b
  exact heq_of_eq (Sigma.ext (eq_of_heq h₁) h₂)

/-- Reassociation commutes with the complete native projections, including the dependent payload at the actual intermediate body state. -/
theorem associate_horizontal {D D' : Type u} {U : Operation T C D} {H : Operation T C' D'} {l}
    (s : Square T P Q f g) (t : Square T R S g k) (w : Square T U H k l) :
    ((s.horizontal t).horizontal w).vertical (associateOps T Q S H) =
      (associateOps T P R U).vertical (s.horizontal (t.horizontal w)) := by
  apply Square.ext
  rintro a ⟨⟨x,y⟩,z⟩
  refine @Sigma.ext _ (fun first : (Q.context (f a)).carrier => ((serial T S H).context (Q.body ⟨f a,first⟩)).carrier)
    (((((s.horizontal t).horizontal w).vertical (associateOps T Q S H)).witness a).run ⟨⟨x,y⟩,z⟩)
    ((((associateOps T P R U).vertical (s.horizontal (t.horizontal w))).witness a).run ⟨⟨x,y⟩,z⟩) rfl ?_
  refine (pair_heq T S H (s.body a x).symm _ ((t.horizontal w).witness (P.body ⟨a,x⟩) |>.run ⟨y,z⟩)
    (horizontal_second s t a ⟨x,y⟩) ?_).trans (horizontal_second s (t.horizontal w) a ⟨x,⟨y,z⟩⟩).symm
  exact (horizontal_second (s.horizontal t) w a ⟨⟨x,y⟩,z⟩).trans (horizontal_second t w (P.body ⟨a,x⟩) ⟨y,z⟩).symm

theorem triangle (P : Operation T A B) (Q : Operation T B C) :
    (associateOps T P (identity T B) Q).vertical ((Square.idSq P).horizontal (leftUnitor T Q)) =
      (rightUnitor T P).horizontal (Square.idSq Q) := rfl

theorem pentagon {D E : Type u} (P : Operation T A B) (Q : Operation T B C)
    (R : Operation T C D) (S : Operation T D E) :
    (((associateOps T P Q R).horizontal (Square.idSq S)).vertical (associateOps T P (serial T Q R) S)).vertical
      ((Square.idSq P).horizontal (associateOps T Q R S)) =
    (associateOps T (serial T P Q) R S).vertical (associateOps T P Q (serial T R S)) := rfl

/-- A finite sequence can change both the joint interface and each projected interface at every step. -/
structure Interface (I : Type v) where
  joint : Type u
  part : I → Type u
  project : ∀ i, joint → part i

structure Link {I : Type v} (A B : Interface.{u} I) where
  component : ∀ i, Operation T (A.part i) (B.part i)
  chosen : OperationCone A.project B.project component

variable {L M N : Interface.{u} I}

def identityLink (L : Interface.{u} I) : Link T L L where
  component i := identity T (L.part i)
  chosen := ⟨identity T L.joint,fun _ => ⟨fun _ => ⟨id,push_id _ _⟩,fun _ _ => rfl⟩⟩

def compLink (a : Link T L M) (b : Link T M N) : Link T L N :=
  ⟨fun i => serial T (a.component i) (b.component i),jointSerial a.chosen b.chosen⟩

inductive Sequence (T : CategoryTheory.Monad (Type u)) {I : Type v} (L : Interface.{u} I) : Interface.{u} I → Type (max (u+1) v) where
  | nil : Sequence T L L
  | snoc {M N : Interface.{u} I} (earlier : Sequence T L M) (last : Link T M N) : Sequence T L N

def evaluate {L : Interface.{u} I} : {M : Interface.{u} I} → Sequence T L M → Link T L M
  | _, .nil => identityLink T L
  | _, .snoc q r => compLink T (evaluate q) r

/-- Every finite assembly of specified local cones has both the complete joint effect equation and the raw joint-body equation at each component. -/
theorem finite_assembly (s : Sequence T L M) (i : I) (a : L.joint) :
    let d := evaluate T s
    let w := (d.chosen.proj i).witness a
    push T.toFunctor w.run (d.chosen.root.context a).law = ((d.component i).context (L.project i a)).law ∧
    ∀ z, M.project i (d.chosen.root.body ⟨a,z⟩) = (d.component i).body ⟨L.project i a,w.run z⟩ :=
  ⟨((evaluate T s).chosen.proj i).witness a |>.preserves, ((evaluate T s).chosen.proj i).body a⟩

end ContextualComposition.NativeOperationAssembly
