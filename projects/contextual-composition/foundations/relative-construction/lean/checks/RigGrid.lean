import ContextualComposition.RigGridMonoidal

namespace Issue92GridProbes

open CategoryTheory ContextualComposition.RigGrid

/- A presentation of the opposite of the category of small types.
The displayed probes use only finite types. Native arrows go in the
opposite direction; sums give products of this category. -/
structure OpTy where
  val : Type

instance : Category.{0} OpTy where
  Hom a b := b.val → a.val
  id _ := id
  comp f g := f ∘ g

set_option backward.isDefEq.respectTransparency false

def makeIso {a b : OpTy} (f : b.val → a.val) (g : a.val → b.val)
    (h : ∀ x, f (g x) = x) (k : ∀ y, g (f y) = y) : a ≅ b where
  hom := f
  inv := g
  hom_inv_id := funext h
  inv_hom_id := funext k

def sum : Binary (C := OpTy) where
  obj a b := ⟨a.val ⊕ b.val⟩
  map f g := Sum.map f g
  map_id _ _ := by funext y; cases y <;> rfl
  map_comp _ _ _ _ := by funext y; cases y <;> rfl

def prod : Binary (C := OpTy) where
  obj a b := ⟨a.val × b.val⟩
  map f g := fun x => (f x.1, g x.2)
  map_id _ _ := by funext y; cases y; rfl
  map_comp _ _ _ _ := rfl

def middle (a b c d : OpTy) :
    sum.obj (sum.obj a b) (sum.obj c d) ≅ sum.obj (sum.obj a c) (sum.obj b d) :=
  makeIso
    (fun
      | .inl (.inl x) => .inl (.inl x)
      | .inl (.inr x) => .inr (.inl x)
      | .inr (.inl x) => .inl (.inr x)
      | .inr (.inr x) => .inr (.inr x))
    (fun
      | .inl (.inl x) => .inl (.inl x)
      | .inl (.inr x) => .inr (.inl x)
      | .inr (.inl x) => .inl (.inr x)
      | .inr (.inr x) => .inr (.inr x))
    (by rintro ((x | x) | (x | x)) <;> rfl)
    (by rintro ((x | x) | (x | x)) <;> rfl)

def add : Additive (C := OpTy) where
  sum := sum
  zero := ⟨Empty⟩
  middle := middle
  middle_natural _ _ _ _ := by
    funext y
    rcases y with (y | y) | (y | y) <;> rfl
  mergeZero := makeIso Empty.elim (fun | .inl y => y | .inr y => y)
    (by rintro (y | y) <;> cases y) (fun y => y.elim)

def leftBin (a b c : OpTy) :
    prod.obj a (sum.obj b c) ≅ sum.obj (prod.obj a b) (prod.obj a c) :=
  makeIso
    (fun | .inl (x, y) => (x, .inl y) | .inr (x, z) => (x, .inr z))
    (fun | (x, .inl y) => .inl (x, y) | (x, .inr z) => .inr (x, z))
    (by rintro ⟨x, y | z⟩ <;> rfl)
    (by rintro (⟨x, y⟩ | ⟨x, z⟩) <;> rfl)

def left (a : OpTy) : Split add (prod.left a) where
  bin := leftBin a
  nil := makeIso Empty.elim Prod.snd
    (by rintro ⟨_, y⟩; cases y) (fun y => y.elim)

def rightBin (a b c : OpTy) :
    prod.obj (sum.obj a b) c ≅ sum.obj (prod.obj a c) (prod.obj b c) :=
  makeIso
    (fun | .inl (x, z) => (.inl x, z) | .inr (y, z) => (.inr y, z))
    (fun | (.inl x, z) => .inl (x, z) | (.inr y, z) => .inr (y, z))
    (by rintro ⟨x | y, z⟩ <;> rfl)
    (by rintro (⟨x, z⟩ | ⟨y, z⟩) <;> rfl)

def right (a b : OpTy) : prod.left (sum.obj a b) ≅ add.pointwise (prod.left a) (prod.left b) :=
  NatIso.ofComponents (rightBin a b) (by
    intro x y f
    funext z
    rcases z with ⟨z₁, z₂⟩ | ⟨z₁, z₂⟩ <;> rfl)

def absorb : prod.left add.zero ≅ add.zeroFunctor :=
  NatIso.ofComponents
    (fun _ => makeIso Empty.elim Prod.fst
      (by rintro ⟨z, _⟩; cases z) (fun z => z.elim))
    (by intro _ _ _; funext z; cases z)

def grid : GridData add where
  mul := prod
  leftSplit := left
  rightDist := right
  absorbLeft := absorb
  rightDist_preserves _ _ := {
    bin := by
      intro x y
      funext z
      rcases z with (⟨z₁, z₂⟩ | ⟨z₁, z₂⟩) | (⟨z₁, z₂⟩ | ⟨z₁, z₂⟩) <;> rfl
    nil := by funext z; cases z }
  absorbLeft_preserves := {
    bin := by intro x y; funext z; rcases z with z | z <;> cases z
    nil := by funext z; cases z }

theorem gridNatural : GridNatural grid where
  left := by intros; funext z; rcases z with ⟨z₁, z₂⟩ | ⟨z₁, z₂⟩ <;> rfl
  right := by intros; funext z; rcases z with ⟨z₁, z₂⟩ | ⟨z₁, z₂⟩ <;> rfl
  absorbRight := by intros; funext z; cases z

def b : OpTy := ⟨Bool⟩

-- Both column and row tags are retained even when all coefficients agree.
theorem transposeRepeated :
    (grid.transpose [b, b] [b, b]).hom (.inl (.inr (.inl (true, false)))) =
      .inr (.inl (.inl (true, false))) := rfl

-- Two real coefficient maps with identical endpoints and different entries.
def pick : sum.obj b b ⟶ b :=
  fun | true => .inl false | false => .inr true

def pick' : sum.obj b b ⟶ b :=
  fun | true => .inr false | false => .inl true

theorem differentTaggedMap : pick ≠ pick' := by
  intro h
  have h' := congrFun h true
  change Sum.inl false = (Sum.inr false : Bool ⊕ Bool) at h'
  cases h'

-- The aggregate arrow is used whole, without extracting source components.
theorem noZeroInjection : IsEmpty (add.zero ⟶ sum.obj b add.zero) :=
  ⟨fun f => (f (.inl true)).elim⟩

theorem opaqueMapNatural :
    prod.map ((Arrows.cons pick Arrows.nil).fold add) ((Arrows.cons pick' Arrows.nil).fold add) ≫
      grid.colExpand [b] [b] =
    grid.colExpand [sum.obj b b] [sum.obj b b] ≫
      (Arrows.cols add prod (Arrows.cons pick Arrows.nil)
        (Arrows.cons pick' Arrows.nil)).fold add :=
  gridNatural.cols (.cons pick .nil) (.cons pick' .nil)

theorem emptyRows : (grid.rowExpand ([] : List OpTy) [b, b]).hom ≫ (grid.transpose [] [b, b]).hom =
    grid.colExpand [] [b, b] := grid.interchange _ _

theorem emptyColumns : (grid.rowExpand [b, b] ([] : List OpTy)).hom ≫ (grid.transpose [b, b] []).hom =
    grid.colExpand [b, b] [] := grid.interchange _ _

def merged : add.fold [b, b] ⟶ b :=
  fun | true => .inl false | false => .inr (.inl true)

def continuation : b ⟶ b := not

-- The comparison acts on a merged coefficient arrow using the whole sum.
theorem nontrivialFibre :
    (((grid.rightSplit b).foldIso [b, b]).inv ≫ prod.map merged (𝟙 b)) ≫
        prod.map (𝟙 b) continuation =
      add.foldMap (fun x => prod.map (𝟙 x) continuation) [b, b] ≫
        ((grid.rightSplit b).foldIso [b, b]).inv ≫ prod.map merged (𝟙 b) :=
  grid.constantOnFibre [b, b] merged continuation

-- Check an actual entry behind the shared output cardinalities.
theorem fibreEntry :
    ((((grid.rightSplit b).foldIso [b, b]).inv ≫ prod.map merged (𝟙 b)) ≫
         prod.map (𝟙 b) continuation) (false, true) =
      .inr (.inl (true, false)) := rfl

theorem emptyFibre :
    (((grid.rightSplit b).foldIso []).inv ≫ prod.map (𝟙 add.zero) (𝟙 b)) ≫
        prod.map (𝟙 add.zero) continuation =
      add.foldMap (fun x => prod.map (𝟙 x) continuation) [] ≫
        ((grid.rightSplit b).foldIso []).inv ≫ prod.map (𝟙 add.zero) (𝟙 b) :=
  grid.constantOnFibre [] (𝟙 add.zero) continuation

#print axioms ContextualComposition.RigGrid.Additive.ofBraided
#print axioms ContextualComposition.RigGrid.PreservesSplit.fold
#print axioms ContextualComposition.RigGrid.GridData.constantOnFibre
#print axioms Issue92GridProbes.noZeroInjection
#print axioms Issue92GridProbes.nontrivialFibre
#print axioms ContextualComposition.RigGrid.GridData.interchange
#print axioms ContextualComposition.RigGrid.GridData.transpose_natural
#print axioms ContextualComposition.RigGrid.GridNatural.rows
#print axioms ContextualComposition.RigGrid.GridNatural.cols
#print axioms Issue92GridProbes.grid
#print axioms Issue92GridProbes.gridNatural
#print axioms Issue92GridProbes.differentTaggedMap
#print axioms Issue92GridProbes.opaqueMapNatural
#print axioms Issue92GridProbes.transposeRepeated
#print axioms Issue92GridProbes.emptyRows
#print axioms Issue92GridProbes.emptyColumns
#print axioms Issue92GridProbes.fibreEntry
#print axioms Issue92GridProbes.emptyFibre

end Issue92GridProbes
