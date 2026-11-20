module
public import ContextualComposition.AmbientBicategory
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientIteratedFunctor
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientWhiskering AmbientBlockIteration AmbientBicategory AmbientCellTrace WordTrace
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
section General
variable {C D : Type*} [Bicategory C] [Bicategory D]
theorem strictExt (F G : StrictPseudofunctor C D) (o : F.obj = G.obj)
    (m : ∀ {X Y : C} (f : X ⟶ Y), HEq (F.map f) (G.map f))
    (t : ∀ {X Y : C} {f g : X ⟶ Y} (q : f ⟶ g), HEq (F.map₂ q) (G.map₂ q)) : F = G := by
  obtain ⟨⟨⟨⟨⟨⟨Fo,Fm⟩,Ft⟩,_,_⟩,Fi,Fc,_,_,_,_,_⟩,Fid,Fie⟩,Fcomp,Fce⟩ := F
  obtain ⟨⟨⟨⟨⟨⟨Go,Gm⟩,Gt⟩,_,_⟩,Gi,Gc,_,_,_,_,_⟩,Gid,Gie⟩,Gcomp,Gce⟩ := G
  change Fo = Go at o; subst Go
  have e : @Fm = @Gm := by funext X Y f; exact eq_of_heq (m f)
  cases e
  have e' : @Ft = @Gt := by funext X Y f g a; exact eq_of_heq (t a)
  cases e'
  have hi : Fi = Gi := funext fun X => (Fie X).trans (Gie X).symm
  cases hi
  have hc : @Fc = @Gc := by funext X Y Z f g; exact (Fce f g).trans (Gce f g).symm
  cases hc; rfl
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {X Y : Obj.{u,v} B}
theorem heqVia {C : Type*} [Category* C] {u v u' v' : C} (p : u = u') (q : v = v') (f : u ⟶ v) (g : u' ⟶ v')
    (c : f = eqToHom p ≫ g ≫ eqToHom q.symm) : HEq f g := by subst u'; subst v'; simpa using heq_of_eq c
theorem wrap {f g f' g' : X ⟶ Y} (p : f = f') (q : g = g') (i : f ⟶ g) (j : f' ⟶ g')
    (h : ∀ x, ev i.hom x = ev j.hom x) : HEq i j := by
  subst f'; subst g'; apply heq_of_eq; apply Bicategory.InducedBicategory.hom₂_ext; apply StrongTrans.Hom.ext; exact cellExt h
theorem zero : action S 0 = StrictPseudofunctor.id (Obj.{u,v} B) := by
  apply strictExt (action S 0) (StrictPseudofunctor.id (Obj.{u,v} B)) rfl
  · intro X Y f; apply heq_of_eq; exact Bicategory.InducedBicategory.hom_ext (blockZero S f.hom)
  · intro X Y f g t
    apply wrap (Bicategory.InducedBicategory.hom_ext (blockZero S f.hom)) (Bicategory.InducedBicategory.hom_ext (blockZero S g.hom))
    intro x
    have h := evMap S 0 t.hom x
    exact congrArg Prod.snd h
theorem oneId (Q : PackedCuts.Psh.{u,max u v,u,v} B) (x : Total (PackedFree.pow S Q 1) (𝟭 B)) :
    (one S Q (idEdge x)).2 = idEdge ((one S Q (idEdge x)).2.src) := by
  let U := BlockEvaluation.global S Q 1
  let w := U.strictInv.obj x
  have idw : Edge.map U (idEdge w) = idEdge x := (same (NativeCube.ofEq (U.map_id w))).trans (congrArg idEdge (Functor.congr_obj U.asIsomorphism.counit_eq x))
  have h := NativeTrace.read_global S Q 1 (idEdge w)
  rw [idw] at h
  have e := congrArg Prod.snd h
  change (one S Q (idEdge x)).2 = Edge.map (NativeTrace.leaf Q _) (idEdge w) at e
  rw [e]
  exact same (NativeCube.ofEq ((NativeTrace.leaf Q _).map_id w))
set_option maxHeartbeats 1200000 in
theorem succ (n : Nat) : (action S n).comp (action S 1) = action S (n+1) := by
  refine strictExt ((action S n).comp (action S 1)) (action S (n+1)) ?_ ?_ ?_
  · funext Q; change obj S 1 (obj S n Q) = obj S (n+1) Q; rfl
  · intro X Y f; apply heq_of_eq; exact Bicategory.InducedBicategory.hom_ext (blockSucc S f.hom n)
  · intro X Y f g t
    apply wrap (Bicategory.InducedBicategory.hom_ext (blockSucc S f.hom n)) (Bicategory.InducedBicategory.hom_ext (blockSucc S g.hom n))
    intro x
    change ev (mapCell S 1 (mapCell S n t.hom)) x = ev (mapCell S (n+1) t.hom) x
    apply read_injective S _ (n+1)
    rw [evMap]
    have h := evMap S 1 (mapCell S n t.hom) x
    let a := ev (mapCell S 1 (mapCell S n t.hom)) x
    let w := one S (PackedFree.pow S (underlying Y) n) a
    have h₁ := (List.cons.inj (congrArg Prod.fst h)).1
    have h₂ := congrArg Prod.snd h
    change (w.1 :: (WordTrace.read S (underlying Y) n w.2).1,(WordTrace.read S (underlying Y) n w.2).2) = _
    change w.1 = _ at h₁
    change w.2 = _ at h₂
    rw [h₁,h₂,evMap]
    let z := one S (PackedFree.pow S (underlying X) n) (idEdge x)
    let R := WordTrace.read S (underlying X) n
    change (z.1 :: (R (idEdge z.2.src)).1,ev t.hom (R (idEdge z.2.src)).2.src) = (z.1 :: (R z.2).1,ev t.hom (R z.2).2.src)
    exact congrArg (fun w => (z.1 :: (R w).1,ev t.hom (R w).2.src)) (oneId S _ x).symm
end ContextualComposition.GrothendieckStep.AmbientIteratedFunctor
