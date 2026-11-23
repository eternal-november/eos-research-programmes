module

public import ContextualComposition.StagedStateLocalization

/-! Recover the late-marked iterated presentation from the actually inner-localized diagram. The outer slide descends on inner inverses by the natural-transformation universal property of localization. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.StagedStateLocalization

open CategoryTheory Opposite DirectedStateBalance DirectedStateDiagramMap DirectedStateNativeFaithfulness DirectedStateIntertwiners
open DirectedStateIterates DirectedStateMarkedExchange SelectiveStateContraction
universe u
variable {S T : Type u} [Category.{u} S] [Category.{u} T]
variable (Q : MorphismProperty S) (A : Index T ⥤ Index S ⥤ Cat.{u,u}) (P : MorphismProperty T)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev late := (marks A P Q).Q
abbrev innerQ (i j : T) := (sel Q (A.obj (op i,j))).Q
abbrev outerQ := (sel P (outerLocalized Q A)).Q

def rowBack (t : T) : (sel Q (A.obj (op t,t))).Localization ⥤ Result A P Q :=
  Localization.Construction.lift (outerInsert A t ⋙ late Q A P)
    ((inverts_iff _ _ _).mpr (fun h hq x => (marks A P Q).Q_inverts _ (Marked.inner (A:=A) (P:=P) (Q:=Q) t h hq x)))

theorem rowBack_fac (t : T) : innerQ Q A t t ⋙ rowBack Q A P t = outerInsert A t ⋙ late Q A P :=
  Localization.Construction.fac _ _

theorem back_pre {i j : T} (h : i ⟶ j) :
    innerQ Q A j i ⋙ (action (strict (outerLocalized Q A)) h (𝟙 i) ⋙ rowBack Q A P i) =
    (action (strict (outer A)) h (𝟙 i) ⋙ outerInsert A i) ⋙ late Q A P :=
  (congrArg (· ⋙ rowBack Q A P i) (local_fac Q (A.map (pairMap h (𝟙 i))))).trans
    (congrArg (map (A.map (pairMap h (𝟙 i))) ⋙ ·) (rowBack_fac Q A P i))

theorem back_post {i j : T} (h : i ⟶ j) :
    innerQ Q A j i ⋙ (action (strict (outerLocalized Q A)) (𝟙 j) h ⋙ rowBack Q A P j) =
    (action (strict (outer A)) (𝟙 j) h ⋙ outerInsert A j) ⋙ late Q A P :=
  (congrArg (· ⋙ rowBack Q A P j) (local_fac Q (A.map (pairMap (𝟙 j) h)))).trans
    (congrArg (map (A.map (pairMap (𝟙 j) h)) ⋙ ·) (rowBack_fac Q A P j))

def backSlide {i j : T} (h : i ⟶ j) :
    action (strict (outerLocalized Q A)) h (𝟙 i) ⋙ rowBack Q A P i ⟶
    action (strict (outerLocalized Q A)) (𝟙 j) h ⋙ rowBack Q A P j :=
  Localization.Construction.natTransExtension
    (eqToHom (back_pre Q A P h) ≫ Functor.whiskerRight (slide (strict (outer A)) h) (late Q A P) ≫ eqToHom (back_post Q A P h).symm)

theorem back_on {i j : T} (h : i ⟶ j) (z : Balance (strict (A.obj (op j,i)))) :
    Conjugate ((backSlide Q A P h).app ((innerQ Q A j i).obj z)) ((late Q A P).map ((slide (strict (outer A)) h).app z)) := by
  let τ := eqToHom (back_pre Q A P h) ≫ Functor.whiskerRight (slide (strict (outer A)) h) (late Q A P) ≫ eqToHom (back_post Q A P h).symm
  have e := congrArg (fun t => NatTrans.app t z) (Localization.Construction.whiskerLeft_natTransExtension τ)
  refine (conjugate_eq e).trans ?_
  dsimp only [τ,NatTrans.comp_app]
  simp only [eqToHom_app]
  exact (Conjugate.trimLeft _ ⟨_,rfl⟩).trans (Conjugate.trimRight _ ⟨_,rfl⟩)

private theorem cast_id {C : Type*} [Category* C] {a b : C} {f : a ⟶ a} (h : Conjugate f (𝟙 b)) : f=𝟙 a := by
  obtain ⟨rfl,_,e⟩ := h; simpa only [eqToHom_refl,Category.id_comp,Category.comp_id] using e

def backData : DirectedStateBalance.Cocone (strict (outerLocalized Q A)) (Result A P Q) where
  fiber := rowBack Q A P
  bal := backSlide Q A P
  unit {i} x := by
    obtain ⟨z,rfl⟩ := (Localization.Construction.objEquiv (sel Q (A.obj (op i,i)))).surjective x
    have e : (slide (strict (outer A)) (𝟙 i)).app z = 𝟙 _ := (restrict (𝟭 (Iterated A))).unit z
    have h := back_on Q A P (𝟙 i) z
    rw [e,Functor.map_id] at h; exact cast_id h
  comp {i j k} h g x := by
    obtain ⟨z,rfl⟩ := (Localization.Construction.objEquiv (sel Q (A.obj (op k,i)))).surjective x
    let n := (innerQ Q A k i).obj z
    let L := late Q A P
    let hact := A.map (pairMap g (𝟙 i))
    let gact := A.map (pairMap (𝟙 k) h)
    have e := congrArg L.map ((restrict (𝟭 (Iterated A))).comp h g z)
    simp only [Functor.map_comp] at e
    obtain ⟨v,src⟩ := trim ((structural_pre (outerLocalized Q A) h g n).map (rowBack Q A P i))
      ((structural_middle (outerLocalized Q A) h g n).map (rowBack Q A P j))
      ((structural_post (outerLocalized Q A) h g n).map (rowBack Q A P k))
      ((backSlide Q A P h).app ((localMap Q hact).obj n)) ((backSlide Q A P g).app ((localMap Q gact).obj n))
    obtain ⟨v',dst⟩ := trim (((structural_pre (outer A) h g z).map (outerInsert A i)).map L)
      (((structural_middle (outer A) h g z).map (outerInsert A j)).map L)
      (((structural_post (outer A) h g z).map (outerInsert A k)).map L)
      (L.map ((slide (strict (outer A)) h).app ((map hact).obj z))) (L.map ((slide (strict (outer A)) g).app ((map gact).obj z)))
    have eh := equal_args (backSlide Q A P h) (Functor.congr_obj (local_fac Q hact) z)
    have eg := equal_args (backSlide Q A P g) (Functor.congr_obj (local_fac Q gact) z)
    have l := eh.trans (back_on Q A P h ((map hact).obj z))
    have r := eg.trans (back_on Q A P g ((map gact).obj z))
    exact ((back_on Q A P (h ≫ g) z).trans ((e ▸ dst).trans ((middle_splice l r v v').symm.trans src.symm))).eq

def fromStaged : Staged Q A P ⥤ Result A P Q :=
  SelectiveStateContraction.extend _ P (backData Q A P) (by
    intro i j h hp x
    obtain ⟨z,rfl⟩ := (Localization.Construction.objEquiv (sel Q (A.obj (op j,i)))).surjective x
    exact iso_of_conjugate (back_on Q A P h z) ((marks A P Q).Q_inverts _ (Marked.outer (A:=A) (P:=P) (Q:=Q) h hp z)))

theorem fromStaged_fac : outerQ Q A P ⋙ fromStaged Q A P = (backData Q A P).descend :=
  Localization.Construction.fac _ _

end ContextualComposition.StagedStateLocalization
