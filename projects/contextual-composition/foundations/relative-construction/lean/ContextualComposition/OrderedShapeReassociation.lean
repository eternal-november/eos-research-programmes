module
public import ContextualComposition.OrderedLeafReadout

/-! Label-preserving natural transformations between ordered polynomial
functors are precisely componentwise maps of shape collections. In
particular the substitution reassociator is an actual invertible grade map. -/

@[expose] public section
namespace ContextualComposition.OrderedShapeReassociation
open CategoryTheory OrderedArityReflection ConstantCollectionFraming OrderedLeafReadout
universe u
variable {C D E : Collection.{u}}

def PreservesLeaves (t : extF C ⟶ extF D) := ∀ (B : Type u) (p : Point C B),
  listBody (t.app B p) = listBody p

theorem preserves_arity (t : extF C ⟶ extF D) (lt : PreservesLeaves t) (B : Type u) (p : Point C B) :
    (t.app B p).arity = p.arity := by simpa [listBody] using congrArg List.length (lt B p)

def sample (n : Nat) (c : C.shape n) : Point C PUnit.{u+1} := ⟨n,c,fun _ => PUnit.unit⟩

def decode (t : extF C ⟶ extF D) (lt : PreservesLeaves t) : C ⟶ D :=
  fun n c => cast (congrArg D.shape (preserves_arity t lt _ (sample n c))) (t.app _ (sample n c)).shape

private theorem point_eq {X : Type u} {x y : Point D X}
    (n : x.arity = y.arity) (s : HEq x.shape y.shape) (v : listBody x = listBody y) : x = y := by
  cases x with
  | mk k c f =>
    cases y with
    | mk j d g =>
      change k = j at n; subst j
      obtain rfl := eq_of_heq s
      apply congrArg (Point.mk k c)
      exact List.ofFn_injective (show List.ofFn f = List.ofFn g from v)

theorem decode_action (t : extF C ⟶ extF D) (lt : PreservesLeaves t) :
    change (decode t lt) = t := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro p
  let kill : B ⟶ PUnit.{u+1} := TypeCat.ofHom (fun _ => PUnit.unit)
  have y : (extF C).map kill p = sample p.arity p.shape := rfl
  have hi := ConcreteCategory.congr_hom (t.naturality kill) p
  change t.app _ ((extF C).map kill p) = (extF D).map kill (t.app B p) at hi
  rw [y] at hi
  have shape_congr {x y : Point D PUnit.{u+1}} (eq : x = y) : HEq x.shape y.shape := by cases eq; rfl
  have shape : HEq (t.app _ (sample p.arity p.shape)).shape (t.app B p).shape :=
    shape_congr hi
  apply point_eq (preserves_arity t lt B p).symm
  · exact (cast_heq _ _).trans shape
  · exact (lt B p).symm

theorem change_injective : Function.Injective (change (C := C) (D := D)) := by
  intro f g h
  funext n c
  have e := congrArg (fun t : extF C ⟶ extF D => t.app _ (sample n c)) h
  injection e with _ s _

def gradeIso (t : extF C ≅ extF D) (lt : PreservesLeaves t.hom) : C ≅ D := by
  have li : PreservesLeaves t.inv := by
    intro B p
    have ig : t.hom.app B (t.inv.app B p) = p := (t.app B).toEquiv.apply_symm_apply p
    exact (lt B (t.inv.app B p)).symm.trans (congrArg listBody ig)
  refine ⟨decode t.hom lt,decode t.inv li,?_,?_⟩
  · apply change_injective
    change change (decode t.hom lt) ≫ change (decode t.inv li) = 𝟙 _
    rw [decode_action,decode_action,t.hom_inv_id]
  · apply change_injective
    change change (decode t.inv li) ≫ change (decode t.hom lt) = 𝟙 _
    rw [decode_action,decode_action,t.inv_hom_id]

theorem gradeIso_hom (t : extF C ≅ extF D) (lt : PreservesLeaves t.hom) :
    change (gradeIso t lt).hom = t.hom := decode_action t.hom lt

private theorem triple_lists {X Y Z : Type*} (xs : List X) (g : X → List Y) (h : Y → List Z) :
    (((xs.map g).flatten).map h).flatten = (xs.map (fun x => ((g x).map h).flatten)).flatten := by
  induction xs <;> simp_all

theorem reassociate_packed {B : Type u} (p : Point C (Point D (Point E B))) :
    (reassociate C D E).hom.app B (pack (pack p)) = pack ((extF C).map (TypeCat.ofHom pack) p) := by
  change pack ((extF C).map (TypeCat.ofHom pack) (unpack (unpack (pack (pack p))))) = _
  rw [unpack_pack,unpack_pack]

theorem reassociate_leaves (C D E : Collection.{u}) : PreservesLeaves (reassociate C D E).hom := by
  intro B q
  let p := unpack (unpack q)
  have eq : pack (pack p) = q := (congrArg pack (pack_unpack (unpack q))).trans (pack_unpack q)
  rw [← eq,reassociate_packed,listBody_pack,listBody_pack,listBody_pack]
  have bodyMap {G : Collection.{u}} {U W : Type u} (f : U → W) (s : Point G U) :
      listBody ((extF G).map (TypeCat.ofHom f) s) = (listBody s).map f := by
    simp only [listBody,List.map_ofFn]; rfl
  rw [bodyMap,List.map_map]
  simpa only [Function.comp_def,listBody_pack] using (triple_lists (listBody p) listBody listBody).symm

def associator (C D E : Collection.{u}) : sub (sub C D) E ≅ sub C (sub D E) :=
  gradeIso (reassociate C D E) (reassociate_leaves C D E)

end ContextualComposition.OrderedShapeReassociation
