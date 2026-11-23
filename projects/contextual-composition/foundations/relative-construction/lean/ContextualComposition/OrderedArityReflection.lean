module

public import ContextualComposition.OneSidedCommaRecovery
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Data.List.OfFn

/-! Ordered polynomial collections and their reflection onto fixed List
histories in the external framing manuscript, `prop:arity-reflection`. -/

@[expose] public section
namespace ContextualComposition.OrderedArityReflection
open CategoryTheory
universe u v w

structure Collection where
  shape : Nat → Type u

instance : Category Collection.{u} where
  Hom C D := ∀ n, C.shape n → D.shape n
  id _ := fun _ x => x
  comp f g := fun n x => g n (f n x)

abbrev terminal : Collection.{u} := ⟨fun _ => PUnit⟩
def forgetShape (C : Collection.{u}) : C ⟶ terminal := fun _ _ => PUnit.unit
instance (C : Collection.{u}) : Subsingleton (C ⟶ terminal) :=
  ⟨fun f g => funext₂ fun n s => Subsingleton.elim (f n s) (g n s)⟩

/-- An ordered polynomial value retains its shape and its entire ordered
list of labels. The equivalence below gives the usual position-tuple presentation. -/
abbrev Value (C : Collection.{u}) (B : Type u) := Σ xs : List B, C.shape xs.length
def erase {C : Collection.{u}} {B : Type u} (x : Value C B) := x.1

private theorem shapeTupleHEq (C : Collection.{u}) (B : Type u) {n m : Nat} (e : n = m)
    {s : C.shape n} {s' : C.shape m} {v : Fin n → B} {v' : Fin m → B} (hs : HEq s s') (hv : HEq v v') :
    HEq (s,v) (s',v') := by subst m; cases eq_of_heq hs; cases eq_of_heq hv; rfl

def positions (C : Collection.{u}) (B : Type u) :
    Value C B ≃ Σ n, C.shape n × (Fin n → B) where
  toFun x := ⟨x.1.length,x.2,x.1.get⟩
  invFun x := ⟨List.ofFn x.2.2,(List.length_ofFn (f := x.2.2)).symm ▸ x.2.1⟩
  left_inv := by
    rintro ⟨xs,c⟩
    apply Sigma.ext (List.ofFn_get xs)
    exact (eqRec_heq _ _)
  right_inv := by
    rintro ⟨n,c,v⟩
    apply Sigma.ext (List.length_ofFn (f := v))
    have h := (List.equivSigmaTuple (α := B)).apply_symm_apply ⟨n,v⟩
    have hv := (Sigma.ext_iff.mp h).2
    have hc : HEq ((List.length_ofFn (f := v)).symm ▸ c) c := by apply eqRec_heq
    exact shapeTupleHEq C B (List.length_ofFn (f := v)) hc hv

abbrev polynomial (B : Type u) : Collection.{u} ⥤ Type u where
  obj C := Value C B
  map f := TypeCat.ofHom fun x => ⟨x.1,f _ x.2⟩

def listSection (B : Type u) : List B ⟶ (polynomial B).obj terminal :=
  TypeCat.ofHom fun xs => ⟨xs,PUnit.unit⟩

theorem section_injective (B : Type u) : Function.Injective (listSection B) :=
  fun _ _ eq => congrArg Sigma.fst eq

variable {K : Type v} [Category.{w} K] (e : K ⥤ Type u) (B : Type u)

abbrev Mixed := Comma e (polynomial B)
abbrev History := CostructuredArrow e (List B)

abbrev eval : Mixed e B ⥤ History e B where
  obj x := CostructuredArrow.mk (x.hom ≫ TypeCat.ofHom erase)
  map f := CostructuredArrow.homMk f.left (by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg Sigma.fst (ConcreteCategory.congr_hom f.w p))

abbrev sectionFunctor : History e B ⥤ Mixed e B :=
  OneSidedCommaRecovery.context e (polynomial B) terminal (listSection B)

theorem counit_obj (x : History e B) : (eval e B).obj ((sectionFunctor e B).obj x) = x := by
  refine CostructuredArrow.obj_ext _ _ rfl ?_
  rw [eqToHom_refl,e.map_id,Category.id_comp]
  rfl

def homEquiv (x : Mixed e B) (y : History e B) :
    ((eval e B).obj x ⟶ y) ≃ (x ⟶ (sectionFunctor e B).obj y) where
  toFun f := ⟨f.left,forgetShape x.right,by
    apply ConcreteCategory.hom_ext
    intro p
    have h := ConcreteCategory.congr_hom (CostructuredArrow.w f) p
    apply Sigma.ext h
    exact heq_of_eq (Subsingleton.elim (α := PUnit) _ _)⟩
  invFun f := CostructuredArrow.homMk f.left (by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg Sigma.fst (ConcreteCategory.congr_hom f.w p))
  left_inv _ := CostructuredArrow.hom_ext _ _ rfl
  right_inv f := Comma.hom_ext _ _ rfl (Subsingleton.elim (forgetShape _) _)

def reflection : eval e B ⊣ sectionFunctor e B :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv e B
    homEquiv_naturality_left_symm := fun _ _ => CostructuredArrow.hom_ext _ _ rfl
    homEquiv_naturality_right := fun _ _ => Comma.hom_ext _ _ rfl (Subsingleton.elim (forgetShape _) _) }

theorem unit_components (x : Mixed e B) :
    ((reflection e B).unit.app x).left = 𝟙 _ ∧ ((reflection e B).unit.app x).right = forgetShape _ :=
  ⟨rfl,rfl⟩

theorem counit_component (y : History e B) : ((reflection e B).counit.app y).left = 𝟙 _ := rfl

instance section_full : (sectionFunctor e B).Full := by
  have : Mono (listSection B) := (mono_iff_injective _).mpr (section_injective B)
  exact OneSidedCommaRecovery.contextFull e _ _ _

instance section_faithful : (sectionFunctor e B).Faithful :=
  OneSidedCommaRecovery.contextFaithful e _ _ _

theorem section_eval : sectionFunctor e B ⋙ eval e B = 𝟭 _ := by
  apply Functor.hext (counit_obj e B)
  intro x y f
  obtain ⟨x,⟨⟨⟩⟩,fx⟩ := x
  obtain ⟨y,⟨⟨⟩⟩,fy⟩ := y
  exact heq_of_eq (CostructuredArrow.hom_ext _ _ rfl)

def relabel {C : Collection.{u}} {B B' : Type u} (v : B → B') (x : Value C B) : Value C B' :=
  ⟨x.1.map v,(List.length_map (f := v)).symm ▸ x.2⟩

theorem erase_relabel {C : Collection.{u}} {B B' : Type u} (v : B → B') (x : Value C B) :
    erase (relabel v x) = (erase x).map v := rfl

theorem section_relabel {B B' : Type u} (v : B → B') (xs : List B) :
    relabel v (listSection B xs) = listSection B' (xs.map v) := by apply Sigma.ext rfl; rfl

/-- Endpoint version of the reflection. The projection on labels can
be any function. The context arrow goes into the reindexed target,
and the resulting grade map into the terminal collection is forced. -/
def endpointHomEquiv {K' : Type v} [Category.{w} K'] (e' : K' ⥤ Type u) {B' : Type u} (pull : K' ⥤ K)
    (x : Mixed e B) (y : History e' B') (v : B → B') (uExt : e.obj (pull.obj y.left) ⟶ e'.obj y.left) :
    {α : x.left ⟶ pull.obj y.left //
      e.map α ≫ uExt ≫ y.hom = x.hom ≫ TypeCat.ofHom erase ≫ TypeCat.ofHom (List.map v)} ≃
    OneSidedCommaRecovery.EndpointSquare e (polynomial B) e' (polynomial B') pull (𝟭 _)
      x ((sectionFunctor e' B').obj y) uExt (TypeCat.ofHom (relabel v)) where
  toFun α := ⟨α.val,forgetShape _,by
    apply ConcreteCategory.hom_ext
    intro p
    apply Sigma.ext (ConcreteCategory.congr_hom α.property p)
    exact heq_of_eq (Subsingleton.elim (α := PUnit) _ _)⟩
  invFun s := ⟨s.left,by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg Sigma.fst (ConcreteCategory.congr_hom s.comm p)⟩
  left_inv _ := rfl
  right_inv s := by
    obtain ⟨l,r,h⟩ := s
    have eq : r = forgetShape x.right := Subsingleton.elim _ _
    cases eq; rfl

/-- A shape of the ordered substitution uses one outer shape and one
inner shape at every position, retaining the whole ordered cut. -/
structure SubShape (C D : Collection.{u}) (n : Nat) where
  lengths : List Nat
  outerShape : C.shape lengths.length
  innerShape : ∀ i : Fin lengths.length, D.shape (lengths.get i)
  sum_eq : lengths.sum = n

abbrev substitution (C D : Collection.{u}) : Collection.{u} := ⟨SubShape C D⟩
def identity : Collection.{u} := ⟨fun n => ULift.{u} (PLift (n = 1))⟩
def unitComparison : identity.{u} ⟶ terminal := forgetShape _
def mulComparison : substitution terminal.{u} terminal ⟶ terminal := forgetShape _

def unitValue {B : Type u} (b : B) : Value identity B := ⟨[b],⟨⟨rfl⟩⟩⟩

theorem unit_body {B : Type u} (b : B) :
    (polynomial B).map unitComparison (unitValue b) = listSection B [b] := rfl

private def cut (xs : List Nat) : (substitution terminal.{0} terminal).shape xs.sum :=
  ⟨xs,PUnit.unit,fun _ => PUnit.unit,rfl⟩

theorem unit_not_iso : ¬ IsIso (unitComparison.{0}) := by
  intro h
  exact Nat.zero_ne_one ((CategoryTheory.inv unitComparison) 0 PUnit.unit).down.down

theorem mul_not_iso : ¬ IsIso (mulComparison.{0}) := by
  intro h
  let i := CategoryTheory.inv mulComparison
  let f : (substitution terminal.{0} terminal).shape 2 := cut [1,1]
  let g : (substitution terminal.{0} terminal).shape 2 := cut [2]
  have hfg : f = g := by
    calc f = (mulComparison ≫ i) 2 f := (congrArg (fun (k : substitution terminal terminal ⟶ substitution terminal terminal) => k 2 f)
      (IsIso.hom_inv_id mulComparison)).symm
         _ = (mulComparison ≫ i) 2 g := rfl
         _ = g := congrArg (fun (k : substitution terminal terminal ⟶ substitution terminal terminal) => k 2 g) (IsIso.hom_inv_id mulComparison)
  have eq : [1,1] = [2] := congrArg SubShape.lengths hfg
  contradiction

/-- The substitution body flattens ordered leaves but puts the actual
ordered cut and component shapes in its resulting grade. -/
def flattenValue {C D : Collection.{u}} {B : Type u} (x : Value C (Value D B)) :
    Value (substitution C D) B := by
  let leaves := (x.1.map Sigma.fst).flatten
  let lengths := x.1.map fun z => z.1.length
  refine ⟨leaves,⟨lengths,?_,?_,?_⟩⟩
  · simpa [lengths] using x.2
  · intro i
    let j : Fin x.1.length := ⟨i.val,by simpa [lengths] using i.isLt⟩
    simpa [lengths,List.get_eq_getElem,j] using (x.1.get j).2
  · simp [lengths,leaves,List.length_flatten,List.map_map,Function.comp_def]

theorem multiplication_body (B : Type u) (x : Value terminal (Value terminal B)) :
    (polynomial B).map mulComparison (flattenValue x) = listSection B ((x.1.map erase).flatten) := rfl

theorem ordered_triple (B : Type u) (x : List (List (List B))) :
    x.flatten.flatten = (x.map List.flatten).flatten := by induction x <;> simp_all

theorem leaf_framing {C : Collection.{u}} {X B : Type u} (x : X) (f : Value C B) :
    erase (relabel (fun b => (x,b)) f) = (erase f).map (fun b => (x,b)) := rfl

/-- At an empty source, a real nonidentity endomorphism of the shape
collection vanishes under evaluation while the context map stays fixed. -/
theorem shape_loss :
    let src := (Functor.const (Discrete Unit)).obj (PEmpty : Type)
    ¬ (eval src Unit).Faithful := by
  intro src h
  let C : Collection := ⟨fun _ => Bool⟩
  let X : Mixed src Unit := ⟨⟨()⟩,C,TypeCat.ofHom PEmpty.elim⟩
  let f : X ⟶ X := ⟨𝟙 _,fun _ => Bool.not,by apply ConcreteCategory.hom_ext; intro p; exact p.elim⟩
  have same : (eval src Unit).map f = (eval src Unit).map (𝟙 X) := CostructuredArrow.hom_ext _ _ rfl
  have neq := congrArg (fun m : X ⟶ X => m.right 0 false) (h.map_injective same)
  exact Bool.noConfusion neq

end ContextualComposition.OrderedArityReflection
