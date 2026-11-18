import ContextualComposition.PackedCuts
open CategoryTheory Opposite ContextualComposition.GrothendieckStep PackedCuts
namespace Mirror210
universe u v b w
variable (K : Nat → Cat.{max u v,u})
abbrev T := Σ i : Nat × Nat, (K (i.1 + i.2) : Type u)
abbrev O := Σ n : Nat, (K n : Type u)
def change {n k : Nat} (h : n = k) : K n ⥤ K k := (eqToHom (congrArg K h)).toFunctor
abbrev forgetCuts : T K ⥤ O K := Sigma.desc (fun i : Nat × Nat => Sigma.incl (C := fun n => (K n : Type u)) (i.1+i.2))
def swap : T K ⥤ T K := Sigma.desc (fun i : Nat × Nat => change K (Nat.add_comm i.1 i.2) ⋙ Sigma.incl (C := fun i : Nat × Nat => (K (i.1+i.2) : Type u)) (i.2,i.1))
theorem cast_incl {n k : Nat} (h : n = k) : change K h ⋙ (Sigma.incl (C := fun n => (K n : Type u)) k) = Sigma.incl (C := fun n => (K n : Type u)) n := by subst k; rfl
theorem forget_swap : swap K ⋙ forgetCuts K = forgetCuts K := PackedFree.sigma_ext (fun i => cast_incl K (Nat.add_comm i.1 i.2))
theorem back {n k : Nat} (h : n = k) (j : k = n) : change K h ⋙ change K j = 𝟭 _ := by subst k; rfl
theorem swap_swap : swap K ⋙ swap K = 𝟭 _ := by
  apply PackedFree.sigma_ext
  rintro ⟨n,m⟩
  exact congrArg (· ⋙ Sigma.incl (C := fun i : Nat × Nat => (K (i.1+i.2) : Type u)) (n,m)) (back K (Nat.add_comm n m) (Nat.add_comm m n))
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split) (Y : Psh.{b,w,u,v} B) (A : B)
abbrev layer (n : Nat) := (PackedFree.pow S Y n).obj (op A)
noncomputable def mirror := (rigid S Y A).inverse ⋙ swap (layer S Y A) ⋙ (rigid S Y A).functor
theorem undetected : mirror S Y A ⋙ mu S Y A = mu S Y A := by
  have h : (rigid S Y A).functor ⋙ mu S Y A = forgetCuts (layer S Y A) := cut_join S Y A
  exact (congrArg (fun F => (rigid S Y A).inverse ⋙ swap (layer S Y A) ⋙ F) h).trans
    ((congrArg ((rigid S Y A).inverse ⋙ ·) (forget_swap (layer S Y A))).trans (recover S Y A))
theorem detected (x : Iterates.Packed P S ((PackedFree.free S).obj Y) (op A)) :
    profile S Y A ((mirror S Y A).obj x) = (profile S Y A x).swap :=
  profile_at S Y A _ _
end Mirror210
