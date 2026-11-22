module
public import ContextualComposition.NativeDependentRowCollapse
@[expose] public section

/-! Compare two native coefficient programs via a common raw addressed
source. This avoids choosing defaults in an empty carrier or fibre. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z t
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
theorem wordChart_retag {X : Type w} {Y : Type z} {J : Type t}
    (A : Y → C) (B : J → C) (f : X → Y)
    (s : List X) (L : J → List X) (M : J → List Y) (js : List J) (h : ∀ j, (L j).map f = M j)
    (r : AddressOrder X s (js.flatMap L))
    (p : ∀ j, fold 𝒮 Zₐ A (M j) ⟶ B j) :
    let ds : (js.flatMap L).map f = js.flatMap M :=
      (List.map_flatMap (f:=f) (g:=L) (l:=js)).trans
        (congrArg (fun k => js.flatMap k) (funext h))
    let q := (r.relabel f).seq (castOrder ds)
    let F := fold 𝒮 Zₐ A
    let e := fun j => (std_fold_map A f (L j)).symm.trans (congrArg F (h j))
    AddressOrder.mapSum additiveStructure (A ∘ f) r ≫ rowsChart (A ∘ f) L js ≫
      act 𝒮 Zₐ (fun j => eqToHom (e j) ≫ p j) js =
      eqToHom (std_fold_map A f s).symm ≫ AddressOrder.mapSum additiveStructure A q ≫
        rowsChart A M js ≫ act 𝒮 Zₐ p js := by
  intro ds q F e
  let d := fun j => eqToHom (e j)
  let H := AddressOrder.mapSum additiveStructure (A ∘ f) r
  have x : act 𝒮 Zₐ (fun j => eqToHom (e j) ≫ p j) js =
      act 𝒮 Zₐ d js ≫ act 𝒮 Zₐ p js := (act_seq 𝒮 Zₐ d p js).symm
  have y : rowsChart (A ∘ f) L js ≫ act 𝒮 Zₐ d js =
      eqToHom ((std_fold_map A f (js.flatMap L)).symm.trans (congrArg F ds)) ≫ rowsChart A M js :=
    rowsChart_relabel_input_inv A f L h js
  have e' : AddressOrder.mapSum additiveStructure A q =
      AddressOrder.mapSum additiveStructure A (r.relabel f) ≫ eqToHom (congrArg F ds) := by
    unfold q
    change AddressOrder.mapSum additiveStructure A (r.relabel f) ≫
      AddressOrder.mapSum additiveStructure A (castOrder ds) = _
    rw [castOrder_map]
  have z := relabel_mapSum_inv A f r
  rw [x, reassoc_of% y, ← eqToHom_trans (std_fold_map A f (js.flatMap L)).symm (congrArg F ds)]
  simp only [Category.assoc]
  rw [e']
  simp only [Category.assoc]
  have Z := congrArg (fun k => k ≫ eqToHom (congrArg F ds) ≫ rowsChart A M js ≫ act 𝒮 Zₐ p js) z
  simp only [Category.assoc] at Z
  exact Z

set_option backward.isDefEq.respectTransparency false in
theorem wordChart_span {X : Type w} {Y : Type z} {Q : Type t} {J : Type*}
    (A : Q → C) (B : J → C) (f : X → Q) (g : Y → Q)
    (s : List X) (t : List Y) (L : J → List X) (K : J → List Y)
    (M : J → List Q) (js : List J) (hL : ∀ j, (L j).map f = M j) (hK : ∀ j, (K j).map g = M j)
    (hm : s.map f = t.map g) (hn : (s.map f).Nodup)
    (r : AddressOrder X s (js.flatMap L)) (q : AddressOrder Y t (js.flatMap K))
    (p : ∀ j, fold 𝒮 Zₐ A (M j) ⟶ B j) :
    let F := fold 𝒮 Zₐ A
    let pf := fun j => eqToHom ((std_fold_map A f (L j)).symm.trans (congrArg F (hL j))) ≫ p j
    let pg := fun j => eqToHom ((std_fold_map A g (K j)).symm.trans (congrArg F (hK j))) ≫ p j
    let e : fold 𝒮 Zₐ (A ∘ f) s = fold 𝒮 Zₐ (A ∘ g) t :=
      ((std_fold_map A f s).symm.trans (congrArg F hm)).trans (std_fold_map A g t)
    AddressOrder.mapSum additiveStructure (A ∘ f) r ≫ rowsChart (A ∘ f) L js ≫ act 𝒮 Zₐ pf js =
      eqToHom e ≫ AddressOrder.mapSum additiveStructure (A ∘ g) q ≫ rowsChart (A ∘ g) K js ≫ act 𝒮 Zₐ pg js := by
  intro F pf pg e
  let dx := (List.map_flatMap (f:=f) (g:=L) (l:=js)).trans
        (congrArg (fun k => js.flatMap k) (funext hL))
  let dy := (List.map_flatMap (f:=g) (g:=K) (l:=js)).trans
        (congrArg (fun k => js.flatMap k) (funext hK))
  let x := (r.relabel f).seq (castOrder dx)
  let y := (q.relabel g).seq (castOrder dy)
  let a := (std_fold_map A f s).symm
  let b := congrArg F hm
  let c := std_fold_map A g t
  have hx := wordChart_retag A B f s L M js hL r p
  have hy := wordChart_retag A B g t K M js hK q p
  dsimp only at hx hy
  rw [hx]
  have H := congrArg (fun a => eqToHom e ≫ a) hy
  refine Eq.trans ?_ H.symm
  have h : AddressOrder.mapSum additiveStructure A x =
      eqToHom b ≫ AddressOrder.mapSum additiveStructure A y := by
    have k := tagged_permutation_coherent A hn x ((castOrder hm).seq y)
    change AddressOrder.mapSum additiveStructure A x =
      AddressOrder.mapSum additiveStructure A (castOrder hm) ≫ AddressOrder.mapSum additiveStructure A y at k
    rw [castOrder_map] at k
    exact k
  change eqToHom a ≫ AddressOrder.mapSum additiveStructure A x ≫ rowsChart A M js ≫ act 𝒮 Zₐ p js =
    eqToHom e ≫ eqToHom c.symm ≫ AddressOrder.mapSum additiveStructure A y ≫ rowsChart A M js ≫ act 𝒮 Zₐ p js
  rw [reassoc_of% h, reassoc_of% eqToHom_trans e c.symm, reassoc_of% eqToHom_trans a b]

theorem finRange_cast_ord {n m : Nat} (e : n = m) :
    (List.finRange n).map (Fin.cast e) = List.finRange m := by
  subst m
  exact List.map_id _

theorem finiteOutputPin {n m : Nat} (e : n = m) (A : Fin n → C) (B : Fin m → C)
    (h : ∀ i, A i = B (Fin.cast e i)) :
    fold 𝒮 Zₐ A (List.finRange n) = fold 𝒮 Zₐ B (List.finRange m) :=
  (congrArg (fun k => fold 𝒮 Zₐ k (List.finRange n)) (funext h)).trans
    ((std_fold_map B (Fin.cast e) (List.finRange n)).symm.trans
      (congrArg (fold 𝒮 Zₐ B) (finRange_cast_ord e)))

set_option backward.isDefEq.respectTransparency false in
theorem finiteWordChart_span {X : Type w} {Y : Type z} {Q : Type t}
    (A : Q → C) (f : X → Q) (g : Y → Q) (s : List X) (t : List Y)
    {n m : Nat} (ec : n = m)
    (L : Fin n → List X) (K : Fin m → List Y) (B : Fin n → C) (D : Fin m → C)
    (H : ∀ i, (L i).map f = (K (Fin.cast ec i)).map g)
    (Hd : ∀ i, B i = D (Fin.cast ec i))
    (hm : s.map f = t.map g) (hn : (s.map f).Nodup)
    (r : AddressOrder X s ((List.finRange n).flatMap L))
    (q : AddressOrder Y t ((List.finRange m).flatMap K))
    (p : ∀ j, fold 𝒮 Zₐ (A ∘ g) (K j) ⟶ D j) :
    let F := fold 𝒮 Zₐ A
    let ef := fun i => ((std_fold_map A f (L i)).symm.trans (congrArg F (H i))).trans
      (std_fold_map A g (K (Fin.cast ec i)))
    let pf := fun i => eqToHom (ef i) ≫ p (Fin.cast ec i) ≫ eqToHom (Hd i).symm
    let e : fold 𝒮 Zₐ (A ∘ f) s = fold 𝒮 Zₐ (A ∘ g) t :=
      ((std_fold_map A f s).symm.trans (congrArg F hm)).trans (std_fold_map A g t)
    AddressOrder.mapSum additiveStructure (A ∘ f) r ≫ rowsChart (A ∘ f) L (List.finRange n) ≫
      act 𝒮 Zₐ pf (List.finRange n) ≫ eqToHom (finiteOutputPin ec B D Hd) =
      eqToHom e ≫ AddressOrder.mapSum additiveStructure (A ∘ g) q ≫
        rowsChart (A ∘ g) K (List.finRange m) ≫ act 𝒮 Zₐ p (List.finRange m) := by
  subst m
  have eb : B = D := funext Hd
  subst D
  intro F ef pf e
  let a := fun i => (std_fold_map A f (L i)).symm.trans (congrArg F (H i))
  let b := fun i => std_fold_map A g (K i)
  let p₀ := fun i => eqToHom (b i) ≫ p i
  let p' := fun i => eqToHom (a i) ≫ p₀ i
  let q' := fun i => eqToHom ((b i).symm.trans (congrArg F (rfl : (K i).map g = (K i).map g))) ≫ p₀ i
  let js := List.finRange n
  have h₀ : finiteOutputPin (rfl : n = n) B B Hd = rfl := Subsingleton.elim _ _
  rw [h₀, eqToHom_refl, Category.comp_id]
  have h₁ : pf = p' := by
    funext i
    change eqToHom ((a i).trans (b i)) ≫ p i ≫ 𝟙 _ = eqToHom (a i) ≫ eqToHom (b i) ≫ p i
    rw [Category.comp_id, reassoc_of% eqToHom_trans (a i) (b i)]
  have h₂ : q' = p := by
    funext i
    change eqToHom (b i).symm ≫ eqToHom (b i) ≫ p i = p i
    have e : eqToHom (b i).symm ≫ eqToHom (b i) = 𝟙 _ := by rw [eqToHom_trans]; rfl
    rw [reassoc_of% e]
  have H₀ := wordChart_span A B f g s t L K (fun i => (K i).map g) js H (fun _ => rfl) hm hn r q p₀
  dsimp only at H₀
  rw [h₁]
  change _ = eqToHom e ≫ AddressOrder.mapSum additiveStructure (A ∘ g) q ≫ rowsChart (A ∘ g) K js ≫ act 𝒮 Zₐ p js
  exact H₀.trans (congrArg (fun h => eqToHom e ≫ AddressOrder.mapSum additiveStructure (A ∘ g) q ≫
    rowsChart (A ∘ g) K js ≫ act 𝒮 Zₐ h js) h₂)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
