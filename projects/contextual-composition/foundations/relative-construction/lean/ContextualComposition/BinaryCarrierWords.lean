module
public import ContextualComposition.BinaryNativeVariation

@[expose] public section
/-! Exact raw words of the carrier-changing binary fibres. Both orders
retain their original source positions, including if a branch is empty. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u
variable {I A : Type u}
theorem GridExpr.leaves_over (g : A → GridExpr I) (xs : List A) :
    (GridExpr.over g xs).leaves = xs.flatMap (fun a => (g a).leaves) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [GridExpr.over, GridExpr.leaves, List.flatMap_cons, ih]

theorem flatMap_filter_if {A B : Type u} (xs : List A) (p : A → Bool) (g : A → List B) :
    (xs.filter p).flatMap g = xs.flatMap (fun x => if p x then g x else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [hx, ih]

theorem flatMap_nil' {A B : Type u} (l : List A) : l.flatMap (fun _ => ([] : List B)) = [] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.nil_append, ih]

section Quad
variable {X U Y W X' U' Y' W' : Type u}
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (f : X → X') (g : X → U → U') (h : Y → Y') (k : Y → W → W')
def quadCarrierMap (p : X × U × Y × W) : X' × U' × Y' × W' :=
  (f p.1,g p.1 p.2.1,h p.2.2.1,k p.2.2.1 p.2.2.2)

theorem leaves_fourOccurrence :
    (fourOccurrenceExpr xs ys us vs).leaves = xs.flatMap (fun x => (us x).flatMap
      (fun u => ys.flatMap (fun y => (vs y).map (fun v => (x,u,y,v))))) := by
  simp only [fourOccurrenceExpr, innerQuad, GridExpr.leaves_over, GridExpr.leaves]
  congr 1
  funext x
  congr 1
  funext u
  congr 1
  funext y
  induction vs y with
  | nil => rfl
  | cons v w ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]

theorem leaves_fourJoint :
    (fourJointExpr xs ys us vs).leaves = xs.flatMap (fun x => ys.flatMap
      (fun y => (us x).flatMap (fun u => (vs y).map (fun v => (x,u,y,v))))) := by
  simp only [fourJointExpr, innerQuad, GridExpr.leaves_over, GridExpr.leaves]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext u
  induction vs y with
  | nil => rfl
  | cons v w ih => simp only [List.flatMap_cons, List.map_cons, ih, List.singleton_append]

theorem mem_fourOccurrence (t : X × U × Y × W) :
    t ∈ (fourOccurrenceExpr xs ys us vs).leaves ↔
    t.1 ∈ xs ∧ t.2.1 ∈ us t.1 ∧ t.2.2.1 ∈ ys ∧ t.2.2.2 ∈ vs t.2.2.1 := by
  rcases t with ⟨x,u,y,v⟩
  rw [leaves_fourOccurrence]
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,rfl,rfl,rfl,rfl⟩
    exact ⟨ha,hb,hc,hd⟩
  · rintro ⟨hx,hu,hy,hv⟩
    exact ⟨x,hx,u,hu,y,hy,v,hv,rfl,rfl,rfl,rfl⟩

theorem mem_fourJoint (t : X × U × Y × W) :
    t ∈ (fourJointExpr xs ys us vs).leaves ↔
    t.1 ∈ xs ∧ t.2.1 ∈ us t.1 ∧ t.2.2.1 ∈ ys ∧ t.2.2.2 ∈ vs t.2.2.1 := by
  rcases t with ⟨x,u,y,v⟩
  rw [leaves_fourJoint]
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,c,hc,b,hb,d,hd,rfl,rfl,rfl,rfl⟩
    exact ⟨ha,hb,hc,hd⟩
  · rintro ⟨hx,hu,hy,hv⟩
    exact ⟨x,hx,y,hy,u,hu,v,hv,rfl,rfl,rfl,rfl⟩

variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
def parentFibreA (t : X') := xs.filter (fun x => decide (f x = t))
def parentFibreB (t : Y') := ys.filter (fun y => decide (h y = t))
def childFibreA (t : U') := fun x => (us x).filter (fun u => decide (g x u = t))
def childFibreB (t : W') := fun y => (vs y).filter (fun v => decide (k y v = t))

private theorem filter_quad_last (t : X' × U' × Y' × W') (x : X) (u : U) (y : Y) :
    ((vs y).map (fun v => (x,u,y,v))).filter (fun p => decide (quadCarrierMap f g h k p = t)) =
      if f x = t.1 ∧ g x u = t.2.1 ∧ h y = t.2.2.1 then
        (childFibreB vs k t.2.2.2 y).map (fun v => (x,u,y,v)) else [] := by
  rw [List.filter_map]
  by_cases h' : f x = t.1 ∧ g x u = t.2.1 ∧ h y = t.2.2.1
  · simp [h', childFibreB, quadCarrierMap, Function.comp_def, Prod.ext_iff]
  · have e (v : W) : ¬ (quadCarrierMap f g h k (x,u,y,v) = t) := by
      intro e
      exact h' ⟨congrArg Prod.fst e,congrArg (fun p => p.2.1) e,congrArg (fun p => p.2.2.1) e⟩
    simp [h', e, Function.comp_def]

theorem fibre_leaves_fourOccurrence (t : X' × U' × Y' × W') :
    ((fourOccurrenceExpr xs ys us vs).leaves).filter (fun p => decide (quadCarrierMap f g h k p = t)) =
    (fourOccurrenceExpr (parentFibreA xs f t.1) (parentFibreB ys h t.2.2.1)
      (childFibreA us g t.2.1) (childFibreB vs k t.2.2.2)).leaves := by
  simp only [leaves_fourOccurrence, List.filter_flatMap, filter_quad_last,
    parentFibreA, parentFibreB, childFibreA, flatMap_filter_if]
  congr 1
  funext x
  by_cases hx : f x = t.1
  · simp only [hx, decide_true, ite_true, true_and]
    congr 1
    funext u
    by_cases hu : g x u = t.2.1
    · simp only [hu, decide_true, ite_true, true_and, decide_eq_true_eq]
    · simp only [hu, decide_false, Bool.false_eq_true, ite_false, false_and, flatMap_nil']
  · simp only [hx, decide_false, Bool.false_eq_true, ite_false, false_and, flatMap_nil']

theorem fibre_leaves_fourJoint (t : X' × U' × Y' × W') :
    ((fourJointExpr xs ys us vs).leaves).filter (fun p => decide (quadCarrierMap f g h k p = t)) =
    (fourJointExpr (parentFibreA xs f t.1) (parentFibreB ys h t.2.2.1)
      (childFibreA us g t.2.1) (childFibreB vs k t.2.2.2)).leaves := by
  simp only [leaves_fourJoint, List.filter_flatMap, filter_quad_last,
    parentFibreA, parentFibreB, childFibreA, flatMap_filter_if]
  congr 1
  funext x
  by_cases hx : f x = t.1
  · simp only [hx, decide_true, ite_true, true_and]
    congr 1
    funext y
    by_cases hy : h y = t.2.2.1
    · simp only [hy, decide_true, ite_true, and_true, decide_eq_true_eq]
    · simp only [hy, decide_false, Bool.false_eq_true, ite_false, and_false, flatMap_nil']
  · simp only [hx, decide_false, Bool.false_eq_true, ite_false, false_and, flatMap_nil']


omit [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W'] in
theorem quadCarrier_support {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
    (hf : ∀ x ∈ xs, f x ∈ xs') (hg : ∀ x ∈ xs, ∀ u ∈ us x, g x u ∈ us' (f x))
    (hh : ∀ y ∈ ys, h y ∈ ys') (hk : ∀ y ∈ ys, ∀ v ∈ vs y, k y v ∈ vs' (h y))
    (p : X × U × Y × W) (hp : p ∈ (fourOccurrenceExpr xs ys us vs).leaves) :
    quadCarrierMap f g h k p ∈ (fourOccurrenceExpr xs' ys' us' vs').leaves := by
  obtain ⟨a,b,c,d⟩ := (mem_fourOccurrence xs ys us vs p).mp hp
  exact (mem_fourOccurrence xs' ys' us' vs' _).mpr
    ⟨hf _ a, hg _ a _ b, hh _ c, hk _ c _ d⟩

abbrev ParentSlice (xs : List X) (f : X → X') (t : X') := {x // x ∈ xs ∧ f x = t}

def sliceWord (t : X') : List (ParentSlice xs f t) :=
  (parentFibreA xs f t).pmap (fun x h => ⟨x,h⟩) (by
    intro x h
    simpa only [parentFibreA, List.mem_filter, decide_eq_true_eq] using h)

theorem sliceWord_map (t : X') : (sliceWord xs f t).map Subtype.val = parentFibreA xs f t := by
  unfold sliceWord
  rw [List.map_pmap, List.pmap_eq_map]
  exact List.map_id _

end Quad

section Relabel
variable {X Y X₀ Y₀ U W : Type u} (f : X₀ → X) (h : Y₀ → Y)
variable (xs : List X₀) (ys : List Y₀) (us : X → List U) (vs : Y → List W)
def quadOuterRelabel (p : X₀ × U × Y₀ × W) : X × U × Y × W := (f p.1,p.2.1,h p.2.2.1,p.2.2.2)

theorem leaves_occurrence_relabel :
    (fourOccurrenceExpr xs ys (us ∘ f) (vs ∘ h)).leaves.map (quadOuterRelabel f h) =
    (fourOccurrenceExpr (xs.map f) (ys.map h) us vs).leaves := by
  simp only [leaves_fourOccurrence, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, quadOuterRelabel]

theorem leaves_joint_relabel :
    (fourJointExpr xs ys (us ∘ f) (vs ∘ h)).leaves.map (quadOuterRelabel f h) =
    (fourJointExpr (xs.map f) (ys.map h) us vs).leaves := by
  simp only [leaves_fourJoint, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, quadOuterRelabel]
end Relabel

/-- Two different source tags survive a many-to-one arrow; a different
target tag has the genuinely empty word. -/
theorem quad_fibre_noninjective_empty :
    let xs : List (Fin 2) := [0,1]
    let ys : List (Fin 1) := [0]
    let us : Fin 2 → List (Fin 1) := fun _ => [0]
    let vs : Fin 1 → List (Fin 1) := fun _ => [0]
    let f : Fin 2 → Fin 2 := fun _ => 0
    let g : Fin 2 → Fin 1 → Fin 1 := fun _ _ => 0
    let h : Fin 1 → Fin 1 := fun _ => 0
    let k : Fin 1 → Fin 1 → Fin 1 := fun _ _ => 0
    let m := quadCarrierMap f g h k
    let s := (fourOccurrenceExpr xs ys us vs).leaves
    s.filter (fun p => decide (m p = (0,0,0,0))) = [(0,0,0,0),(1,0,0,0)] ∧
      s.filter (fun p => decide (m p = (1,0,0,0))) = [] := by
  decide

end ContextualComposition.NativeFinitePush.DependentFibre
