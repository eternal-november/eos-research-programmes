module
public import ContextualComposition.ConstantCollectionFraming

/-! The addressed polynomial substitution and ordinary list flattening
give exactly the same ordered output, including unequal and empty rows. -/

@[expose] public section
namespace ContextualComposition.OrderedLeafReadout
open ConstantCollectionFraming OrderedArityReflection
open scoped BigOperators

private theorem get_row {B : Type*} (rs : List (List B)) (i : Nat) (hi : i < rs.length)
    (j : Nat) (hj : j < rs[i].length) :
    rs.flatten[((rs.take i).map List.length).sum + j]? = some (rs[i][j]) := by
  induction rs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hj ⊢
      simp [List.getElem?_append_left,hj]
    | succ i =>
      have hi' : i < rs.length := by simpa using hi
      have hj' : j < rs[i].length := hj
      simp only [List.flatten_cons,List.take_succ_cons,List.map_cons,List.sum_cons,List.getElem_cons_succ]
      rw [List.getElem?_append_right (by omega)]
      simpa [Nat.add_assoc] using ih i hi' hj'

private theorem sum_prefix {n : Nat} (m : Fin n → Nat) (i : Fin n) :
    ((List.ofFn m).take i.val).sum = ∑ j : Fin i.val, m (Fin.castLE i.isLt.le j) := by
  rw [List.sum_take_ofFn]
  symm
  apply Finset.sum_bij (fun j _ => Fin.castLE i.isLt.le j)
  · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro a _ b _ h; exact Fin.ext (congrArg (fun z : Fin n => z.val) h)
  · intro j hj
    let k : Fin i.val := ⟨j.val,(Finset.mem_filter.mp hj).2⟩
    exact ⟨k,Finset.mem_univ _,Fin.ext rfl⟩
  · intros; rfl

theorem ragged {B : Type*} {n : Nat} (m : Fin n → Nat) (v : ∀ i, Fin (m i) → B) :
    List.ofFn (fun k : Fin (∑ i, m i) => let a := (finSigmaFinEquiv (n := m)).symm k; v a.1 a.2) =
      (List.ofFn (fun i => List.ofFn (v i))).flatten := by
  let rs := List.ofFn (fun i => List.ofFn (v i))
  have lens : rs.map List.length = List.ofFn m := by simp [rs,List.map_ofFn,Function.comp_def]
  have hl : rs.flatten.length = ∑ i, m i := by rw [List.length_flatten,lens,List.sum_ofFn]
  apply List.ext_getElem
  · simp [← hl,rs]
  · intro k hk hk'
    let t : Fin (∑ i, m i) := ⟨k,by simpa using hk⟩
    obtain ⟨a,ea⟩ := (finSigmaFinEquiv (n := m)).surjective t
    have ik : a.1.val < rs.length := by simp [rs]
    have jlen : rs[a.1.val].length = m a.1 := by simp [rs]
    have jk : a.2.val < rs[a.1.val].length := jlen.symm ▸ a.2.isLt
    have eq := get_row rs a.1.val ik a.2.val jk
    have offset : ((rs.take a.1.val).map List.length).sum + a.2.val = k := by
      rw [List.map_take,lens,sum_prefix,← finSigmaFinEquiv_apply a]
      exact congrArg Fin.val ea
    rw [offset,List.getElem?_eq_getElem hk'] at eq
    have right := Option.some.inj eq
    simp only [List.getElem_ofFn]
    change v ((finSigmaFinEquiv (n := m)).symm t).1 ((finSigmaFinEquiv (n := m)).symm t).2 = _
    rw [← ea,Equiv.symm_apply_apply]
    simpa [rs] using right.symm

theorem listBody_pack {C D : Collection} {B : Type*} (z : Point C (Point D B)) :
    listBody (pack z) = ((listBody z).map listBody).flatten := by
  simpa [listBody,pack,List.map_ofFn,Function.comp_def] using ragged (fun i => (z.label i).arity) (fun i => (z.label i).label)

end ContextualComposition.OrderedLeafReadout
