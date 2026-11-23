module
public import ContextualComposition.StrictTelCells

/-! Extension of invertible unit and binary comparisons to all native
dependent telescope combs. The comparisons are cellular over both span
legs; no equation identifying the compared functors is required. -/

@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrongTelCombs

open CategoryTheory CategoryTheory.Limits SpanApex NativeBlocks StrictTelCells
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictTelOperations StrictTelMapLaws StrictTelNested StrictTelCartesian

universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000

variable {B : Type b} [Category.{max b w} B]
variable {U V W U' V' : Span (B := B)}

structure IsoCell (F G : Over U V) where
  hom : Cell F G
  inv : Cell G F
  hom_inv : hom.nat ≫ inv.nat = 𝟙 _
  inv_hom : inv.nat ≫ hom.nat = 𝟙 _

variable {F G : Over U V}

def IsoCell.ofEq (e : F = G) : IsoCell F G := by
  subst G; exact ⟨identity _,identity _,Category.id_comp _,Category.id_comp _⟩

def IsoCell.trans {H : Over U V} (s : IsoCell F G) (t : IsoCell G H) : IsoCell F H where
  hom := vcomp s.hom t.hom
  inv := vcomp t.inv s.inv
  hom_inv := by change (_ ≫ _) ≫ _ ≫ _ = _; rw [Category.assoc,← Category.assoc t.hom.nat,t.hom_inv,Category.id_comp,s.hom_inv]
  inv_hom := by change (_ ≫ _) ≫ _ ≫ _ = _; rw [Category.assoc,← Category.assoc s.inv.nat,s.inv_hom,Category.id_comp,t.inv_hom]

def IsoCell.pre (J : Over W U) (s : IsoCell F G) : IsoCell (comp J F) (comp J G) where
  hom := beforeCell J s.hom
  inv := beforeCell J s.inv
  hom_inv := by ext x; exact NatTrans.congr_app s.hom_inv (J.functor.obj x)
  inv_hom := by ext x; exact NatTrans.congr_app s.inv_hom (J.functor.obj x)

def IsoCell.post (s : IsoCell F G) (J : Over V W) : IsoCell (comp F J) (comp G J) where
  hom := afterCell s.hom J
  inv := afterCell s.inv J
  hom_inv := by
    ext x
    exact (J.functor.map_comp _ _).symm.trans ((congrArg J.functor.map (NatTrans.congr_app s.hom_inv x)).trans (J.functor.map_id _))
  inv_hom := by
    ext x
    exact (J.functor.map_comp _ _).symm.trans ((congrArg J.functor.map (NatTrans.congr_app s.inv_hom x)).trans (J.functor.map_id _))

def IsoCell.pair {F' G' : Over U' V'} (s : IsoCell F G) (t : IsoCell F' G') :
    IsoCell (both F F') (both G G') where
  hom := bothCell s.hom t.hom
  inv := bothCell s.inv t.inv
  hom_inv := by
    ext x
    exact InducedCategory.hom_ext (CategoricalPullback.hom_ext
      (NatTrans.congr_app s.hom_inv x.fst) (NatTrans.congr_app t.hom_inv x.snd))
  inv_hom := by
    ext x
    exact InducedCategory.hom_ext (CategoricalPullback.hom_ext
      (NatTrans.congr_app s.inv_hom x.fst) (NatTrans.congr_app t.inv_hom x.snd))

variable {P Q : Endpoints.{b,max b w,b,max b w} B}
variable (S : P.Split) (T : Q.Split)
variable (F : Over (power S 1) (power T 1)) (M : Ops (power S 1)) (N : Ops (power T 1))

structure Comparisons where
  unit : IsoCell (comp M.unit F) N.unit
  tensor : IsoCell (comp M.tensor F) (comp (both F F) N.tensor)

theorem idLeft {U V : Span (B := B)} (f : Over U V) : comp (StrictSpanAlgebra.id _) f = f :=
  overExt (Functor.id_comp _)
theorem idRight {U V : Span (B := B)} (f : Over U V) : comp f (StrictSpanAlgebra.id _) = f :=
  overExt (Functor.comp_id _)

variable (cmp : Comparisons S T F M N)

theorem snoc_target (k : Nat) :
    comp (StrictTelMap.powerMap S T F (k+2)) (StrictTelFold.comb T N (k+2)) =
      comp (comp (cutLast S (k+1)) (both
        (comp (StrictTelMap.powerMap S T F (k+1)) (StrictTelFold.comb T N (k+1))) F)) N.tensor := by
  change comp _ (StrictTelFold.snoc T N (StrictTelFold.comb T N (k+1))) = _
  rw [snocFactor]
  apply overExt
  let L := (cutLast S (k+1)).functor
  let R := (StrictTelMap.powerMap S T F (k+1))
  let D := StrictTelFold.comb T N (k+1)
  change L ⋙ (both R F).functor ⋙ ((concatenate T (k+1) 1).functor ⋙ (cutLast T (k+1)).functor) ⋙
    (both D (StrictSpanAlgebra.id _)).functor ⋙ N.tensor.functor =
    L ⋙ (both (comp R D) F).functor ⋙ N.tensor.functor
  rw [StrictTelMap.glue_cut]
  change L ⋙ ((both R F).functor ⋙ (both D (StrictSpanAlgebra.id _)).functor) ⋙ _ = _
  have h := congrArg Over.functor (StrictTelCategories.bothComp R F D (StrictSpanAlgebra.id _))
  change (both (comp R D) (comp F (StrictSpanAlgebra.id _))).functor =
    (both R F).functor ⋙ (both D (StrictSpanAlgebra.id _)).functor at h
  rw [← h, idRight]

theorem snoc_mid (k : Nat) :
    comp (comp (cutLast S (k+1)) (both (StrictTelFold.comb S M (k+1)) (StrictSpanAlgebra.id _)))
      (comp (both F F) N.tensor) =
    comp (comp (cutLast S (k+1)) (both (comp (StrictTelFold.comb S M (k+1)) F) F)) N.tensor := by
  apply overExt
  have h := congrArg Over.functor (StrictTelCategories.bothComp (StrictTelFold.comb S M (k+1)) (StrictSpanAlgebra.id _) F F)
  change (both (comp (StrictTelFold.comb S M (k+1)) F) (comp (StrictSpanAlgebra.id _) F)).functor =
    (both (StrictTelFold.comb S M (k+1)) (StrictSpanAlgebra.id _)).functor ⋙ (both F F).functor at h
  change _ ⋙ ((both _ _).functor ⋙ (both F F).functor) ⋙ _ = _
  rw [← h,idLeft]
  rfl

/-- The comparison on each actual native chain, including length zero.
The construction requires no coherence assumptions; additional equations
on the resulting comparisons express compatibility with all substitutions. -/
noncomputable def comb : (n : Nat) →
    IsoCell (comp (StrictTelFold.comb S M n) F) (comp (StrictTelMap.powerMap S T F n) (StrictTelFold.comb T N n))
  | 0 => cmp.unit.trans (.ofEq (idLeft _).symm)
  | 1 => .ofEq ((idLeft F).trans (idRight F).symm)
  | k+2 => by
    let A := StrictTelFold.comb S M (k+1)
    let L := cutLast S (k+1)
    let h := StrictTelCartesian.snocFactor S (k+1) M A
    let first := IsoCell.pre (comp L (both A (StrictSpanAlgebra.id _))) cmp.tensor
    let step := IsoCell.post (IsoCell.pre L (IsoCell.pair (comb (k+1)) (IsoCell.ofEq (rfl : F = F)))) N.tensor
    refine (IsoCell.ofEq (congrArg (fun l => comp l F) h)).trans ?_
    exact first.trans ((IsoCell.ofEq (snoc_mid S T F M N k)).trans (step.trans (IsoCell.ofEq (snoc_target S T F N k).symm)))

/-- The components on all arities form one invertible transformation on
the original tagged telescope, natural on actual native arrows. -/
noncomputable def telescope :
    IsoCell (comp (StrictTelFold.eval S M) F) (comp (StrictTelMap.map S T F) (StrictTelFold.eval T N)) where
  hom := {
    nat := {
      app := fun ⟨n,x⟩ => (comb S T F M N cmp n).hom.nat.app x
      naturality := by
        rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
        exact (comb S T F M N cmp n).hom.nat.naturality f }
    src := fun ⟨n,x⟩ => (comb S T F M N cmp n).hom.src x
    dst := fun ⟨n,x⟩ => (comb S T F M N cmp n).hom.dst x }
  inv := {
    nat := {
      app := fun ⟨n,x⟩ => (comb S T F M N cmp n).inv.nat.app x
      naturality := by
        rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
        exact (comb S T F M N cmp n).inv.nat.naturality f }
    src := fun ⟨n,x⟩ => (comb S T F M N cmp n).inv.src x
    dst := fun ⟨n,x⟩ => (comb S T F M N cmp n).inv.dst x }
  hom_inv := by
    apply NatTrans.ext
    funext x
    obtain ⟨n,x⟩ := x
    exact NatTrans.congr_app (comb S T F M N cmp n).hom_inv x
  inv_hom := by
    apply NatTrans.ext
    funext x
    obtain ⟨n,x⟩ := x
    exact NatTrans.congr_app (comb S T F M N cmp n).inv_hom x

end ContextualComposition.GrothendieckStep.StrongTelCombs
