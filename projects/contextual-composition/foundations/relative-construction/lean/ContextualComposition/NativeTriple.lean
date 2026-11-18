module
public import ContextualComposition.NativeAssoc
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeAssoc
open CategoryTheory Opposite SpanApex NativeBlocks
namespace Rows
open NativeBlocks.Nested
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Y : Type*} [Category* Y]
abbrev Diagram (Y : Type*) [Category* Y] := Σ n, Y ⥤ (word S n).apex
abbrev src (p : Diagram S Y) := p.2 ⋙ (word S p.1).source
abbrev dst (p : Diagram S Y) := p.2 ⋙ (word S p.1).dest
noncomputable abbrev eval (p : Diagram S Y) := p.2 ⋙ (collapse S p.1).functor
theorem eval_src (p : Diagram S Y) : eval S p ⋙ leftLeg S = src S p := congrArg (p.2 ⋙ ·) (collapse S p.1).source
theorem eval_dst (p : Diagram S Y) : eval S p ⋙ rightLeg S = dst S p := congrArg (p.2 ⋙ ·) (collapse S p.1).dest
/-- Snoc of a single block of arbitrary inner length to a row. On the empty
row this returns the block itself, not an extra matching object. -/
def push : (p : Diagram S Y) → (H : Y ⥤ tel S) → dst S p = H ⋙ leftLeg S → Diagram S Y
  | ⟨0,_⟩,H,_ => ⟨1,H⟩
  | ⟨n+1,F⟩,H,h => ⟨n+2,Strict.lift _ _ F H h⟩
theorem push_src (p : Diagram S Y) (H : Y ⥤ tel S) (h : dst S p = H ⋙ leftLeg S) :
    src S (push S p H h) = src S p := by rcases p with ⟨(_|n),p⟩; exact h.symm; rfl
theorem push_dst (p : Diagram S Y) (H : Y ⥤ tel S) (h : dst S p = H ⋙ leftLeg S) :
    dst S (push S p H h) = H ⋙ rightLeg S := by rcases p with ⟨(_|n),p⟩ <;> rfl
theorem push_len (p : Diagram S Y) (H : Y ⥤ tel S) (h : dst S p = H ⋙ leftLeg S) :
    (push S p H h).1 = p.1+1 := by rcases p with ⟨(_|n),p⟩ <;> rfl
theorem eval_push (p : Diagram S Y) (H : Y ⥤ tel S) (h : dst S p = H ⋙ leftLeg S) :
    eval S (push S p H h) = mul S (eval S p) H ((eval_dst S p).trans h) := by
  rcases p with ⟨(_|n),F⟩
  · exact (Whole.mul_left S H).symm.trans (mul_congr S (congrArg (· ⋙ incl S 0) h.symm) rfl)
  · let K := Strict.lift (word S (n+1)).dest (leftLeg S) F H h
    let L := Strict.fst (word S (n+1)).dest (leftLeg S) ⋙ (collapse S (n+1)).functor
    let T := Strict.snd (word S (n+1)).dest (leftLeg S)
    have j : L ⋙ rightLeg S = T ⋙ leftLeg S := (congrArg (Strict.fst _ _ ⋙ ·) (collapse S (n+1)).dest).trans (Strict.commute _ _)
    exact mul_comp S K L T j

/-- Concatenate two fixed-shape diagrams of rows. The length can be zero on
either side; actual nested blocks and their matching squares are retained. -/
def cat (p : Diagram S Y) : (n : Nat) → (G : Y ⥤ (word S n).apex) → (h : dst S p = G ⋙ (word S n).source) →
    {t : Diagram S Y // src S t = src S p ∧ dst S t = G ⋙ (word S n).dest}
  | 0,_,h => ⟨p,rfl,h⟩
  | 1,G,h => ⟨push S p G h,push_src S p G h,push_dst S p G h⟩
  | n+2,G,h => by
    let f := G ⋙ Strict.fst (word S (n+1)).dest (leftLeg S)
    let g := G ⋙ Strict.snd (word S (n+1)).dest (leftLeg S)
    let t := cat p (n+1) f h
    have j : dst S t.1 = g ⋙ leftLeg S := t.2.2.trans (congrArg (G ⋙ ·) (Strict.commute _ _))
    exact ⟨push S t.1 g j,(push_src S t.1 g j).trans t.2.1,push_dst S t.1 g j⟩
theorem cat_len (p : Diagram S Y) : (n : Nat) → (G : Y ⥤ (word S n).apex) → (h : dst S p = G ⋙ (word S n).source) →
    (cat S p n G h).1.1 = p.1+n
  | 0,_,_ => rfl
  | 1,G,h => push_len S p G h
  | n+2,_G,h => (push_len S _ _ _).trans (congrArg (·+1) (cat_len p (n+1) _ h))
theorem snoc_eval (n : Nat) (G : Y ⥤ (word S (n+2)).apex) :
    eval S ⟨n+2,G⟩ = mul S (eval S ⟨n+1,G ⋙ Strict.fst _ _⟩) (G ⋙ Strict.snd _ _)
      ((eval_dst S ⟨n+1,G ⋙ Strict.fst _ _⟩).trans (congrArg (G ⋙ ·) (Strict.commute _ _))) :=
  mul_comp S G _ _ _
theorem eval_cat (p : Diagram S Y) : (n : Nat) → (G : Y ⥤ (word S n).apex) → (h : dst S p = G ⋙ (word S n).source) →
    eval S (cat S p n G h).1 = mul S (eval S p) (eval S ⟨n,G⟩) (((eval_dst S p).trans h).trans (eval_src S ⟨n,G⟩).symm)
  | 0,G,h => (Whole.mul_right S (eval S p)).symm.trans (mul_congr S rfl (congrArg (· ⋙ incl S 0) ((eval_dst S p).trans h)))
  | 1,G,h => eval_push S p G h
  | n+2,G,h => by
    let f := G ⋙ Strict.fst (word S (n+1)).dest (leftLeg S)
    let g := G ⋙ Strict.snd (word S (n+1)).dest (leftLeg S)
    let t := cat S p (n+1) f h
    have j : dst S t.1 = g ⋙ leftLeg S := t.2.2.trans (congrArg (G ⋙ ·) (Strict.commute _ _))
    have i : eval S p ⋙ rightLeg S = eval S ⟨n+1,f⟩ ⋙ leftLeg S := ((eval_dst S p).trans h).trans (eval_src S ⟨n+1,f⟩).symm
    have k : eval S ⟨n+1,f⟩ ⋙ rightLeg S = g ⋙ leftLeg S := (eval_dst S _).trans (congrArg (G ⋙ ·) (Strict.commute _ _))
    exact (eval_push S t.1 g j).trans ((mul_congr S (eval_cat p (n+1) f h) rfl).trans
      ((Whole.mul_assoc S _ _ _ i k).trans (mul_congr S rfl (snoc_eval S n G).symm)))
abbrev source := BlockCartesian.All.source S
abbrev dest := BlockCartesian.All.dest S
abbrev pairs := Strict.Match (dest S) (source S)
abbrev part (i : Nat × Nat) := Strict.Match (word S i.1).dest (word S i.2).source
def splitObj (x : pairs S) : Σ i, part S i := ⟨(x.fst.1,x.snd.1),x.fst.2,x.snd.2,x.glue⟩
def splitMap {x y : pairs S} (f : x ⟶ y) : splitObj S x ⟶ splitObj S y := by
  rcases x with ⟨⟨m,x₁⟩,⟨n,y₁⟩,hx⟩; rcases y with ⟨⟨m',x'⟩,⟨n',y'⟩,hy⟩
  rcases f with ⟨⟨a,b,h⟩⟩
  cases a with | mk a =>
    cases b with | mk b =>
      exact Sigma.SigmaHom.mk ⟨⟨a,b,h⟩⟩
def split : pairs S ⥤ Σ i, part S i where
  obj := splitObj S
  map := splitMap S
  map_id := by rintro ⟨⟨m,x⟩,⟨n,y⟩,h⟩; rfl
  map_comp := by
    rintro ⟨⟨m,x⟩,⟨n,y⟩,h⟩ ⟨⟨m',x'⟩,⟨n',y'⟩,h'⟩ ⟨⟨m'',x''⟩,⟨n'',y''⟩,h''⟩ ⟨⟨a,b,_⟩⟩ ⟨⟨c,d,_⟩⟩
    cases a; cases b; cases c; cases d; rfl
def tagPair (i : Nat × Nat) : part S i ⥤ pairs S := Strict.lift _ _
  (Strict.fst _ _ ⋙ outer S i.1) (Strict.snd _ _ ⋙ outer S i.2) (Strict.commute _ _)
theorem pair_ext {E : Type*} [Category* E] {F G : pairs S ⥤ E} (h : ∀ i, tagPair S i ⋙ F = tagPair S i ⋙ G) : F = G := by
  fapply Functor.ext
  · rintro ⟨⟨m,x⟩,⟨n,y⟩,e⟩
    exact Functor.congr_obj (h (m,n)) ⟨x,y,e⟩
  · rintro ⟨⟨m,x⟩,⟨n,y⟩,e⟩ ⟨⟨_,x'⟩,⟨_,y'⟩,e'⟩ ⟨⟨f,g,j⟩⟩
    cases f with | mk f =>
      rename_i xnew
      cases g with | mk g =>
        rename_i ynew
        exact Functor.congr_hom (h (m,n)) (show (⟨x,y,e⟩ : part S (m,n)) ⟶ ⟨xnew,ynew,e'⟩ from ⟨⟨f,g,j⟩⟩)
abbrev fst (i : Nat × Nat) : part S i ⥤ (word S i.1).apex := Strict.fst _ _
abbrev snd (i : Nat × Nat) : part S i ⥤ (word S i.2).apex := Strict.snd _ _
def glue (i : Nat × Nat) := cat S ⟨i.1,fst S i⟩ i.2 (snd S i) (Strict.commute _ _)
def packed (i : Nat × Nat) := (glue S i).1.2 ⋙ outer S (glue S i).1.1
def binary := split S ⋙ Sigma.desc (packed S)
theorem binary_at (i : Nat × Nat) : tagPair S i ⋙ binary S = packed S i := rfl
theorem binary_src : binary S ⋙ source S = Strict.fst _ _ ⋙ source S := pair_ext S fun i => (glue S i).2.1
theorem binary_dst : binary S ⋙ dest S = Strict.snd _ _ ⋙ dest S := pair_ext S fun i => (glue S i).2.2
noncomputable abbrev firstEval := Strict.fst (dest S) (source S) ⋙ flatten S
noncomputable abbrev secondEval := Strict.snd (dest S) (source S) ⋙ flatten S
theorem matchEval : firstEval S ⋙ rightLeg S = secondEval S ⋙ leftLeg S :=
  (congrArg (Strict.fst (dest S) (source S) ⋙ ·) (flatten_dest S)).trans
    ((Strict.commute _ _).trans (congrArg (Strict.snd (dest S) (source S) ⋙ ·) (flatten_source S)).symm)
theorem binary_flatten : binary S ⋙ flatten S = mul S (firstEval S) (secondEval S) (matchEval S) := by
  apply pair_ext S; intro i
  let p : Diagram S (part S i) := ⟨i.1,fst S i⟩
  exact (eval_cat S p i.2 (snd S i) (Strict.commute _ _)).trans
    (mul_comp S (tagPair S i) (firstEval S) (secondEval S) (matchEval S)).symm
end Rows
namespace Three
open NativeBlocks.Nested
universe u v i j
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
abbrev rows : Span (B := B) := ⟨Cat.of (strings S), Rows.source S, Rows.dest S⟩
/-- The third application uses the same zero/singleton/strict-matching
presentation as the second, with rows of blocks as its letters. -/
def level : Nat → Span (B := B)
  | 0 => power S 0
  | 1 => rows S
  | n+2 => product (level (n+1)) (rows S)
def mapProduct {U V W Z : Span (B := B)} (F : Over U V) (G : Over W Z) :
    Over (product U W) (product V Z) := by
  let A := Strict.fst U.dest W.source
  let D := Strict.snd U.dest W.source
  have h : (A ⋙ F.functor) ⋙ V.dest = (D ⋙ G.functor) ⋙ Z.source :=
    (congrArg (A ⋙ ·) F.dest).trans ((Strict.commute _ _).trans (congrArg (D ⋙ ·) G.source).symm)
  exact ⟨Strict.lift _ _ (A ⋙ F.functor) (D ⋙ G.functor) h,congrArg (A ⋙ ·) F.source,congrArg (D ⋙ ·) G.dest⟩
noncomputable def flattenOver : Over (rows S) (whole S) := ⟨flatten S,flatten_source S,flatten_dest S⟩
/-- Flatten each individual row, keeping its place in the outer word. -/
noncomputable def inside : (n : Nat) → Over (level S n) (word S n)
  | 0 => ⟨𝟭 _,rfl,rfl⟩
  | 1 => flattenOver S
  | n+2 => mapProduct (inside (n+1)) (flattenOver S)
/-- Merge the outer rows first, leaving individual innermost blocks intact. -/
def outside : (n : Nat) → Over (level S n) (rows S)
  | 0 => ⟨outer S 0,rfl,rfl⟩
  | 1 => ⟨𝟭 _,rfl,rfl⟩
  | n+2 => by
    let I : Over (rows S) (rows S) := ⟨𝟭 _,rfl,rfl⟩
    let K := mapProduct (outside (n+1)) I
    exact ⟨K.functor ⋙ Rows.binary S,(congrArg (K.functor ⋙ ·) (Rows.binary_src S)).trans K.source,
      (congrArg (K.functor ⋙ ·) (Rows.binary_dst S)).trans K.dest⟩
theorem per_length : (n : Nat) → (outside S n).functor ⋙ flatten S = (inside S n).functor ⋙ (collapse S n).functor
  | 0 => rfl
  | 1 => rfl
  | n+2 => by
    let I : Over (rows S) (rows S) := ⟨𝟭 _,rfl,rfl⟩
    let K := (mapProduct (outside S (n+1)) I).functor
    let G := (inside S (n+2)).functor
    let L := Strict.fst (level S (n+1)).dest (Rows.source S)
    have A := congrArg (K ⋙ ·) (Rows.binary_flatten S)
    have H := mul_comp S K (Rows.firstEval S) (Rows.secondEval S) (Rows.matchEval S)
    have e := congrArg (L ⋙ ·) (per_length (n+1))
    exact A.trans (H.trans ((mul_congr S e rfl).trans (Rows.snoc_eval S n G).symm))
abbrev strings3 := Σ n, (level S n).apex
abbrev incl3 (n : Nat) : (level S n).apex ⥤ strings3 S := Sigma.incl (C := fun k => (level S k).apex) n
abbrev source := Sigma.desc (fun n => (level S n).source)
abbrev dest := Sigma.desc (fun n => (level S n).dest)
def mergeRows : strings3 S ⥤ strings S := Sigma.desc (fun n => (outside S n).functor)
noncomputable def mapRows : strings3 S ⥤ strings S := Sigma.desc (fun n => (inside S n).functor ⋙ outer S n)
theorem merge_source : mergeRows S ⋙ Rows.source S = source S := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (outside S n).source x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (outside S n).source f
theorem merge_dest : mergeRows S ⋙ Rows.dest S = dest S := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (outside S n).dest x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (outside S n).dest f
theorem map_source : mapRows S ⋙ Rows.source S = source S := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (inside S n).source x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (inside S n).source f
theorem map_dest : mapRows S ⋙ Rows.dest S = dest S := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (inside S n).dest x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (inside S n).dest f
/-- Three-level associativity as equality of functors on the whole tagged
domain; in particular this identifies the two maps on native matching arrows. -/
theorem flatten_assoc : mergeRows S ⋙ flatten S = mapRows S ⋙ flatten S := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (per_length S n) x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (per_length S n) f
theorem productFaithful {U V W Z : Span (B := B)} (F : Over U V) (G : Over W Z)
    [F.functor.Faithful] [G.functor.Faithful] : (mapProduct F G).functor.Faithful where
  map_injective {x y} {f g} h := by
    apply InducedCategory.hom_ext
    apply CategoryTheory.Limits.CategoricalPullback.hom_ext
    · apply F.functor.map_injective
      exact congrArg ((Strict.fst V.dest Z.source).map) h
    · apply G.functor.map_injective
      exact congrArg ((Strict.snd V.dest Z.source).map) h
theorem insideFaithful : (n : Nat) → (inside S n).functor.Faithful
  | 0 => inferInstanceAs (𝟭 B).Faithful
  | 1 => inferInstanceAs (flatten S).Faithful
  | n+2 => by
    let := insideFaithful (n+1)
    let : (flattenOver S).functor.Faithful := inferInstanceAs (flatten S).Faithful
    exact productFaithful (inside S (n+1)) (flattenOver S)
instance mapFaithful : (mapRows S).Faithful where
  map_injective {x y} {f g} h := by
    rcases x with ⟨n,x⟩
    cases f with | mk f =>
      cases g with | mk g =>
        let := insideFaithful S n
        exact congrArg Sigma.SigmaHom.mk ((inside S n).functor.map_injective ((outer S n).map_injective h))
/-- Associating in either order retains distinctions between parallel native
matching squares at fixed source and target. This is not fullness. -/
theorem mergeFlattenFaithful : (mergeRows S ⋙ flatten S).Faithful := by rw [flatten_assoc]; infer_instance
variable (Y : Bᵒᵖ ⥤ Cat.{j,i})
def weightedOuter := SpanPayload.totalMap Y (mergeRows S) (Rows.dest S) (merge_dest S)
noncomputable def weightedInner := SpanPayload.totalMap Y (mapRows S) (Rows.dest S) (map_dest S)
theorem total_congr {K M : Type*} [Category* K] [Category* M] {e : K ⥤ B} {d : M ⥤ B} {F G : K ⥤ M}
    (h : F = G) {f : F ⋙ d = e} {g : G ⋙ d = e} : SpanPayload.totalMap Y F d f = SpanPayload.totalMap Y G d g := by subst G; rfl
theorem weighted_assoc : weightedOuter S Y ⋙ BlockCartesian.All.weighted S Y =
    weightedInner S Y ⋙ BlockCartesian.All.weighted S Y :=
  (SpanPayload.total_comp Y (mergeRows S) (Rows.dest S) (merge_dest S) (flatten S) (rightLeg S) (flatten_dest S)).trans
    ((total_congr Y (flatten_assoc S)).trans (SpanPayload.total_comp Y (mapRows S) (Rows.dest S) (map_dest S)
      (flatten S) (rightLeg S) (flatten_dest S)).symm)
end Three
end ContextualComposition.GrothendieckStep.NativeAssoc
