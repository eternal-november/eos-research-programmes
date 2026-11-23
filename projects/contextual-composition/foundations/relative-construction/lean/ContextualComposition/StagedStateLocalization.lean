module

public import ContextualComposition.DirectedStateMarkedExchange

/-! Localizing the chosen inner coordinate produces a functor of strict state diagrams, so a second contraction really can be applied to the localized categories. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.StagedStateLocalization

open CategoryTheory Opposite DirectedStateBalance DirectedStateDiagramMap DirectedStateNativeFaithfulness DirectedStateIntertwiners
open DirectedStateIterates DirectedStateMarkedExchange SelectiveStateContraction
universe u
variable {S T : Type u} [Category.{u} S] [Category.{u} T]
variable (Q : MorphismProperty S) {G H K : Index S ⥤ Cat.{u,u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev sel (G : Index S ⥤ Cat.{u,u}) := selected (strict G) Q

def localMap (n : G ⟶ H) : (sel Q G).Localization ⥤ (sel Q H).Localization :=
  Localization.Construction.lift (map n ⋙ (sel Q H).Q) ((inverts_iff _ _ _).mpr (fun h hp x => by
    have eq := map_slide n h x
    exact iso_of_conjugate (map_conjugate (sel Q H).Q ((conjugate_eq eq).trans (move_conjugate n h x)))
      ((sel Q H).Q_inverts _ (.slide h hp _))))

theorem local_fac (n : G ⟶ H) : (sel Q G).Q ⋙ localMap Q n = map n ⋙ (sel Q H).Q :=
  Localization.Construction.fac _ _

theorem local_id (G : Index S ⥤ Cat.{u,u}) : localMap Q (𝟙 G) = 𝟭 _ := by
  apply Localization.Construction.uniq
  exact (local_fac Q (𝟙 G)).trans (congrArg (· ⋙ (sel Q G).Q) (map_id G))

theorem local_comp (n : G ⟶ H) (m : H ⟶ K) : localMap Q (n ≫ m) = localMap Q n ⋙ localMap Q m := by
  apply Localization.Construction.uniq
  calc
    _ = map (n ≫ m) ⋙ (sel Q K).Q := local_fac Q _
    _ = map n ⋙ (map m ⋙ (sel Q K).Q) := congrArg (· ⋙ (sel Q K).Q) (map_comp n m)
    _ = (map n ⋙ (sel Q H).Q) ⋙ localMap Q m := congrArg (map n ⋙ ·) (local_fac Q m).symm
    _ = _ := congrArg (· ⋙ localMap Q m) (local_fac Q n).symm

def selectedFunctor : (Index S ⥤ Cat.{u,u}) ⥤ Cat.{u,u} where
  obj G := Cat.of (sel Q G).Localization
  map n := (localMap Q n).toCatHom
  map_id G := congrArg Functor.toCatHom (local_id Q G)
  map_comp n m := congrArg Functor.toCatHom (local_comp Q n m)

def selectInner : contraction ⟶ selectedFunctor Q where
  app G := (sel Q G).Q.toCatHom
  naturality _ _ n := congrArg Functor.toCatHom (local_fac Q n).symm

variable (A : Index T ⥤ Index S ⥤ Cat.{u,u}) (P : MorphismProperty T)
abbrev outerLocalized := A ⋙ selectedFunctor Q
abbrev Staged := (sel P (outerLocalized Q A)).Localization

def install : outer A ⟶ outerLocalized Q A := Functor.whiskerLeft A (selectInner Q)
abbrev preview := map (install Q A) ⋙ (sel P (outerLocalized Q A)).Q

def toStaged : Result A P Q ⥤ Staged Q A P := by
  apply Localization.Construction.lift (preview Q A P)
  intro i j f hf
  cases hf with
  | outer h hp z =>
    have e := (conjugate_eq (map_slide (install Q A) h z)).trans (move_conjugate (install Q A) h z)
    exact iso_of_conjugate (map_conjugate (sel P (outerLocalized Q A)).Q e) ((sel P _).Q_inverts _ (.slide h hp _))
  | inner t h hq x =>
    let u := (slide (strict (A.obj (op t,t))) h).app x
    have i : IsIso ((sel Q (A.obj (op t,t))).Q.map u) := (sel Q _).Q_inverts _
      (SelectiveStateContraction.Marked.slide (F:=strict (A.obj (op t,t))) (P:=Q) h hq x)
    have e := map_native (install Q A) u
    have d := (insertion (strict (outerLocalized Q A)) t).map_isIso ((sel Q (A.obj (op t,t))).Q.map u)
    have e' : IsIso ((map (install Q A)).map ((outerInsert A t).map u)) := e.symm ▸ d
    exact (sel P (outerLocalized Q A)).Q.map_isIso _

theorem toStaged_fac : (marks A P Q).Q ⋙ toStaged Q A P = preview Q A P := Localization.Construction.fac _ _

end ContextualComposition.StagedStateLocalization
