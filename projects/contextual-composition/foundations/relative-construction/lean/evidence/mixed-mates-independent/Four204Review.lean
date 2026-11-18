import ContextualComposition.MixedMates
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
namespace Independent204
structure P where val : Int
instance : Category P where
  Hom _ _ := Int × Nat
  id _ := (0,0)
  comp f g := (f.1+g.1,f.2+g.2)
  id_comp := by intros; apply Prod.ext <;> simp
  comp_id := by intros; apply Prod.ext <;> simp
  assoc := by intros; apply Prod.ext <;> simp [Int.add_assoc,Nat.add_assoc]
def tr (k : Int) : P ⥤ P where
  obj x := ⟨x.val + k⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
def offset (A B : P) (k : Int) : A ≅ B where
  hom := (k,0)
  inv := (-k,0)
  hom_inv_id := Prod.ext (Int.add_right_neg k) rfl
  inv_hom_id := Prod.ext (Int.add_left_neg k) rfl
def cell (F G : P ⥤ P) (k : Int)
    (hF : ∀ {x y : P} (f : x ⟶ y), F.map f = f)
    (hG : ∀ {x y : P} (f : x ⟶ y), G.map f = f) : F ≅ G :=
  NatIso.ofComponents (fun x => offset _ _ k) (by
    intro x y h; rw [hF,hG]; exact Prod.ext (Int.add_comm h.1 k) (Nat.add_comm h.2 0))
def E (k u : Int) : P ≌ P where
  functor := tr k
  inverse := tr (-k)
  unitIso := cell _ _ u (fun _ => rfl) (fun _ => rfl)
  counitIso := cell _ _ (-u) (fun _ => rfl) (fun _ => rfl)
  functor_unitIso_comp := by intro x; exact @Prod.ext Int Nat (u + -u,0) (0,0) (Int.add_right_neg u) rfl
def grid (s : Int) : FinalCube.Mix.Grid where
  A := P; D := P; A' := P; D' := P; b := 𝟭 _; b' := 𝟭 _; p := 𝟭 _; q := 𝟭 _
  cell := { app := fun _ => (s,3), naturality := by
              intro x y h; exact Prod.ext (Int.add_comm h.1 s) (Nat.add_comm h.2 3) }
def z : P := ⟨0⟩
example (s : Int) : ¬ IsIso ((grid s).cell.app z) := by
  intro h; obtain ⟨f,h,_⟩ := h.out; have hh := congrArg Prod.snd h; change 3 + f.2 = 0 at hh; omega
open MixedMates TaggedMixed
def M : Frame (grid 14) (grid 6) where
  f := E 1 1; g := E 2 4; f' := E 3 12; g' := E 4 20
  s := cell _ _ 2 (fun _ => rfl) (fun _ => rfl)
  t := cell _ _ 9 (fun _ => rfl) (fun _ => rfl)
  l := cell _ _ 5 (fun _ => rfl) (fun _ => rfl)
  r := cell _ _ 6 (fun _ => rfl) (fun _ => rfl)
-- Both the underlying functors and their chosen unit/counit data differ.
example : (M.f.functor.obj z).val = 1 ∧ (M.g.functor.obj z).val = 2 ∧
    (M.f'.functor.obj z).val = 3 ∧ (M.g'.functor.obj z).val = 4 := ⟨rfl,rfl,rfl,rfl⟩
theorem h : Cube.Law M.forward := fun _ => rfl
example : Cube.Law M.reverse.forward := M.backLaw h
example : Cube.Law (M.reverse.compose M).forward := M.reverse.composeLaw M (M.backLaw h) h
example : M.reverse.forward.s.app z = (5,0) ∧ M.reverse.forward.t.app z = (17,0) ∧
    M.reverse.forward.l.app z = (-6,0) ∧ M.reverse.forward.r.app z = (-10,0) := ⟨rfl,rfl,rfl,rfl⟩
example : (M.reverse.forward.f'.map ((grid 6).cell.app z) ≫ M.reverse.forward.t.app z) ≫
    (grid 14).b'.map (M.reverse.forward.r.app z) = (13,3) := rfl
-- Ignoring the equivalence data at just this edge changes the paste.
example : ((M.reverse.forward.f'.map ((grid 6).cell.app z) ≫
      (show _ ⟶ _ from ((9:Int),(0:Nat)))) ≫ (grid 14).b'.map (M.reverse.forward.r.app z)) ≠
      (M.reverse.forward.l.app z ≫ (grid 14).p.map (M.reverse.forward.s.app z) ≫ (grid 14).cell.app _) := by
  change ((5:Int),(3:Nat)) ≠ (13,3)
  decide
end Independent204
