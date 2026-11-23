module
public import ContextualComposition.NativeTensorPathNormal
@[expose] public section

/-! A tag belongs to a leaf occurrence of the tensor tree, not to its
coefficient or even to the dependent input data at that leaf. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I : C} {Tag : Type w}

inductive Tagging (Tag : Type w) : DependentFubiniTree I → Type (max (u+1) v w) where
  | unit : Tagging Tag .unit
  | leaf (data : OrderedDependentAugData I) (tag : Tag) : Tagging Tag (.leaf data)
  | fork {a b : DependentFubiniTree I} : Tagging Tag a → Tagging Tag b → Tagging Tag (.fork a b)

def Tagging.expr : {a : DependentFubiniTree I} → Tagging Tag a → SumTree Tag
  | _, .unit => .zero
  | _, .leaf _ x => .atom x
  | _, .fork a b => .plus (expr a) (expr b)

/-- A transported tagging together with the actual scalar syntax for
its raw structural path. No evaluated equality is a field. -/
structure TaggingTransport {a : DependentFubiniTree I} (s : Tagging Tag a) (b : DependentFubiniTree I) where
  target : Tagging Tag b
  circuit : TensorCircuit Tag s.expr target.expr
  read : a.Address ≃ b.Address

def TaggingTransport.comp {a b c : DependentFubiniTree I} {s : Tagging Tag a}
    (p : TaggingTransport s b) (q : TaggingTransport p.target c) : TaggingTransport s c :=
  ⟨q.target,.seq p.circuit q.circuit,p.read.trans q.read⟩

def TaggingTransport.tensor {a b c d : DependentFubiniTree I} {s : Tagging Tag a} {t : Tagging Tag b}
    (p : TaggingTransport s c) (q : TaggingTransport t d) : TaggingTransport (.fork s t) (.fork c d) :=
  ⟨.fork p.target q.target, .tensor p.circuit q.circuit,p.read.prodCongr q.read⟩

def TaggingTransport.ident {a : DependentFubiniTree I} (s : Tagging Tag a) : TaggingTransport s a :=
  ⟨s,.ident s.expr,Equiv.refl _⟩

def AssocMove.tagForward {a b : DependentFubiniTree I} (p : AssocMove a b) (s : Tagging Tag a) :
    TaggingTransport s b :=
  match p,s with
  | .root _ _ _, .fork (.fork a b) c => ⟨.fork a (.fork b c), .assoc a.expr b.expr c.expr,tripleRetag⟩
  | .left p _, .fork a c => (tagForward p a).tensor (.ident c)
  | .right _ p, .fork c a => (TaggingTransport.ident c).tensor (tagForward p a)

def AssocMove.tagBackward {a b : DependentFubiniTree I} (p : AssocMove a b) (s : Tagging Tag b) :
    TaggingTransport s a :=
  match p,s with
  | .root _ _ _, .fork a (.fork b c) => ⟨.fork (.fork a b) c, .reverse (.assoc a.expr b.expr c.expr),tripleRetag.symm⟩
  | .left p _, .fork a c => (tagBackward p a).tensor (.ident c)
  | .right _ p, .fork c a => (TaggingTransport.ident c).tensor (tagBackward p a)

def StructuralMove.tagForward {a b : DependentFubiniTree I} (p : StructuralMove a b) (s : Tagging Tag a) :
    TaggingTransport s b :=
  match p,s with
  | .assoc p, s => p.tagForward s
  | .swap _ _, .fork a b => ⟨.fork b a, .swap a.expr b.expr,Equiv.prodComm _ _⟩
  | .eraseRight _, .fork a .unit => ⟨a, .runit a.expr,singletonRightRead _⟩
  | .left p _, .fork a c => (tagForward p a).tensor (.ident c)
  | .right _ p, .fork c a => (TaggingTransport.ident c).tensor (tagForward p a)

def StructuralMove.tagBackward {a b : DependentFubiniTree I} (p : StructuralMove a b) (s : Tagging Tag b) :
    TaggingTransport s a :=
  match p,s with
  | .assoc p, s => p.tagBackward s
  | .swap _ _, .fork b a => ⟨.fork a b, .reverse (.swap a.expr b.expr),Equiv.prodComm _ _⟩
  | .eraseRight _, s => ⟨.fork s .unit, .reverse (.runit s.expr),(singletonRightRead _).symm⟩
  | .left p _, .fork a c => (tagBackward p a).tensor (.ident c)
  | .right _ p, .fork c a => (TaggingTransport.ident c).tensor (tagBackward p a)

def StructuralPath.tagTransport {a b : DependentFubiniTree I} (p : StructuralPath a b) (s : Tagging Tag a) :
    TaggingTransport s b :=
  match p with
  | .ident _ => .ident s
  | .next f g =>
    let x := f.tagForward s
    x.comp (tagTransport g x.target)
  | .prev f g =>
    let x := f.tagBackward s
    x.comp (tagTransport g x.target)

theorem TaggingTransport.nodup {a b : DependentFubiniTree I} {s : Tagging Tag a}
    (p : TaggingTransport s b) (h : s.expr.leaves.Nodup) : p.target.expr.leaves.Nodup :=
  p.circuit.order.perm.nodup h

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
