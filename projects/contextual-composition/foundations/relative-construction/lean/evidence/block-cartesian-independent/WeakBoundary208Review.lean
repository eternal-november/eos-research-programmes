import ContextualComposition.BlockCartesian
open CategoryTheory CategoryTheory.Limits Opposite ContextualComposition.GrothendieckStep NativeBlocks
open Families NativeCleavage
open SpanApex
namespace PositiveGlue207
abbrev S := splitEndpoints
abbrev E := power S 1
def atom (A : Type) (F : A → Type) : E.apex := pair presheaf (𝟭 (Type)) A F
def l := atom Unit (fun _ => Bool)
abbrev C := Σ _ : Unit, Bool
def H (z : C) := if z.2 then Unit else Empty
def r := atom C H
def flip (z : C) : C := ⟨(),!z.2⟩
def swap : C ≅ C where
  hom := ↾flip
  inv := ↾flip
  hom_inv_id := by ext ⟨_,b⟩; cases b <;> rfl
  inv_hom_id := by ext ⟨_,b⟩; cases b <;> rfl
def c : CategoricalPullback E.dest E.source := ⟨l,r,swap⟩
def pull := powerChoice S 0 C r swap.hom
-- Normalizing this glue at a positive right block changes its actual grade.
example : (payload presheaf (𝟭 _) r) ⟨(),false⟩ = Empty := rfl
example : (payload presheaf (𝟭 _) pull.obj) ⟨(),false⟩ = Unit := rfl
example : (payload presheaf (𝟭 _) pull.obj) ⟨(),true⟩ = Empty := rfl
example : ∃ x, Nonempty ((equipment S 1 1).functor.obj x ≅ c) :=
  ⟨_,⟨(equipment S 1 1).functor.objObjPreimageIso c⟩⟩
theorem notliteral (z : Strict.Match E.dest E.source) : (Strict.inclusion E.dest E.source).obj z ≠ c := by
  rcases z with ⟨f,g,h⟩
  intro e
  have ef : f = l := congrArg CategoricalPullback.fst e
  have eg : g = r := congrArg CategoricalPullback.snd e
  subst f; subst g
  have he : HEq ((Strict.inclusion E.dest E.source).obj ⟨l,r,h⟩).iso.hom c.iso.hom := by rw [e]
  change HEq (𝟙 C) swap.hom at he
  have hfalse := congrArg (fun k : C ⟶ C => (k ⟨(),false⟩).2) (eq_of_heq he)
  exact Bool.noConfusion hfalse
example (z : (power S 2).apex) : (equipment S 1 1).functor.obj z ≠ c :=
  notliteral ((blocks S 1 1).cutFunctor.obj z)
-- An equivalence of categories need not preserve strict incoming bijections:
-- this actual positive-arity native equipment equivalence does not.
theorem notUniqueIncoming : ¬ BlockCartesian.UniqueIncoming (equipment S 1 1).functor := by
  intro h
  let F := (equipment S 1 1).functor
  let x := F.objPreimage c
  let t : c ⟶ F.obj x := (F.objObjPreimageIso c).inv
  obtain ⟨⟨z,f⟩,e⟩ := (h x).surjective ⟨c,t⟩
  exact notliteral ((blocks S 1 1).cutFunctor.obj z) (congrArg Sigma.fst e)
end PositiveGlue207
