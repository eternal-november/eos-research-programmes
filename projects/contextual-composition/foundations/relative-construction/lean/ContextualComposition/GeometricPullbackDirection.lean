module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! Local-to-global pullback comparison under a bifunctor. The reverse display map follows from exactness at the specific square. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.GeometricPullbackDirection

open CategoryTheory CategoryTheory.Limits
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {A B Z P : C} {A' B' Z' P' : D} {f : A ⟶ Z} {g : B ⟶ Z} {f' : A' ⟶ Z'} {g' : B' ⟶ Z'}
  {l : P ⟶ A} {r : P ⟶ B} {l' : P' ⟶ A'} {r' : P' ⟶ B'}

def pairMap {X Y : C} {X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y') : (X,X') ⟶ (Y,Y') := ⟨f,g⟩

variable (p : IsPullback l r f g) (q : IsPullback l' r' f' g')

include p q in
theorem pairSquare : IsPullback (pairMap l l') (pairMap r r') (pairMap f f') (pairMap g g') := by
  have comm : pairMap l l' ≫ pairMap f f' = pairMap r r' ≫ pairMap g g' := Prod.ext p.w q.w
  apply IsPullback.of_isLimit (c := PullbackCone.mk (pairMap l l') (pairMap r r') comm)
  refine PullbackCone.IsLimit.mk comm (fun s => pairMap
    (p.lift s.fst.1 s.snd.1 (congrArg Prod.fst s.condition))
    (q.lift s.fst.2 s.snd.2 (congrArg Prod.snd s.condition))) ?_ ?_ ?_
  · intro s; exact Prod.ext (p.lift_fst _ _ _) (q.lift_fst _ _ _)
  · intro s; exact Prod.ext (p.lift_snd _ _ _) (q.lift_snd _ _ _)
  · intro s m eq₁ eq₂
    exact Prod.ext (p.hom_ext ((congrArg Prod.fst eq₁).trans (p.lift_fst _ _ _).symm)
      ((congrArg Prod.fst eq₂).trans (p.lift_snd _ _ _).symm))
      (q.hom_ext ((congrArg Prod.snd eq₁).trans (q.lift_fst _ _ _).symm)
        ((congrArg Prod.snd eq₂).trans (q.lift_snd _ _ _).symm))

variable (T : C × D ⥤ E) [HasPullback (T.map (pairMap f f')) (T.map (pairMap g g'))]
abbrev Global := pullback (T.map (pairMap f f')) (T.map (pairMap g g'))

def forward : T.obj (P,P') ⟶ Global T (f:=f) (f':=f') (g:=g) (g':=g') :=
  pullback.lift (T.map (pairMap l l')) (T.map (pairMap r r'))
    ((T.map_comp _ _).symm.trans ((congrArg T.map (pairSquare p q).w).trans (T.map_comp _ _)))

theorem reverse_iff_section (h : Global T (f:=f) (f':=f') (g:=g) (g':=g') ⟶ T.obj (P,P')) :
    (h ≫ T.map (pairMap l l') = pullback.fst _ _ ∧ h ≫ T.map (pairMap r r') = pullback.snd _ _) ↔ h ≫ forward p q T = 𝟙 _ := by
  constructor
  · rintro ⟨hl,hr⟩; apply pullback.hom_ext <;> simp [forward,hl,hr]
  · intro e
    constructor
    · have k := congrArg (· ≫ pullback.fst _ _) e
      simpa [forward] using k
    · have k := congrArg (· ≫ pullback.snd _ _) e
      simpa [forward] using k

variable [PreservesLimit (cospan (pairMap f f') (pairMap g g')) T]

def exactIso : T.obj (P,P') ≅ Global T (f:=f) (f':=f') (g:=g) (g':=g') :=
  ((pairSquare p q).map T).isoPullback

theorem forward_exact : forward p q T = (exactIso p q T).hom := by
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (((pairSquare p q).map T).isoPullback_hom_fst).symm
  · exact (pullback.lift_snd _ _ _).trans (((pairSquare p q).map T).isoPullback_hom_snd).symm

theorem reverse_exact :
    (exactIso p q T).inv ≫ T.map (pairMap l l') = pullback.fst _ _ ∧
    (exactIso p q T).inv ≫ T.map (pairMap r r') = pullback.snd _ _ := by
  apply (reverse_iff_section p q T _).mpr
  rw [forward_exact,Iso.inv_hom_id]

end ContextualComposition.GeometricPullbackDirection
