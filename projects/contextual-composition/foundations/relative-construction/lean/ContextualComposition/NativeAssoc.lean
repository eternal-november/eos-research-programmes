module
public import ContextualComposition.BlockCartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.NativeAssoc
open CategoryTheory Opposite SpanApex NativeBlocks
universe b w
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,b,w} B} (S : P.Split)
variable {X : Type b} [Category.{w} X]

/-- A diagram of actual native paths at one fixed length. The tag is kept
with the diagram so associating length sums does not identify different apices. -/
abbrev Path (X : Type b) [Category.{w} X] := Σ n, X ⥤ (power S n).apex
abbrev src (p : Path S X) := p.2 ⋙ (power S p.1).source
abbrev dst (p : Path S X) := p.2 ⋙ (power S p.1).dest
abbrev tagged (p : Path S X) := p.2 ⋙ incl S p.1
def nil (A : X ⥤ B) : Path S X := ⟨0,A⟩
noncomputable def join (p q : Path S X) (h : dst S p = src S q) : Path S X :=
  ⟨p.1+q.1,(blocks S p.1 q.1).assemble p.2 q.2 h⟩
theorem join_src (p q : Path S X) (h : dst S p = src S q) : src S (join S p q h) = src S p :=
  let c := blocks S p.1 q.1
  (congrArg (c.assemble p.2 q.2 h ⋙ ·) c.source.symm).trans (congrArg (· ⋙ _) (c.first_assemble ..))
theorem join_dst (p q : Path S X) (h : dst S p = src S q) : dst S (join S p q h) = dst S q :=
  let c := blocks S p.1 q.1
  (congrArg (c.assemble p.2 q.2 h ⋙ ·) c.dest.symm).trans (congrArg (· ⋙ _) (c.rest_assemble ..))
def front (n : Nat) : (power S (n+1)).apex ⥤ (power S n).apex := by rw [succ_power S n]; exact gradeProjection
def last (n : Nat) : (power S (n+1)).apex ⥤ Apex P := by rw [succ_power S n]; exact second P _
theorem boundary (n : Nat) : front S n ⋙ (power S n).dest = last S n ⋙ left P := by
  cases n <;> exact matching P _
theorem last_src (n : Nat) : front S n ⋙ (power S n).source = (power S (n+1)).source := by cases n <;> rfl
theorem last_dst (n : Nat) : last S n ⋙ right P S = (power S (n+1)).dest := by cases n <;> rfl
noncomputable def grow (p : Path S X) (G : X ⥤ Apex P) (h : dst S p = G ⋙ left P) : Path S X :=
  ⟨p.1+1,by rw [succ_power S p.1]; exact attachLast _ p.2 G h⟩
theorem grow_pre (p : Path S X) (G : X ⥤ Apex P) (h : dst S p = G ⋙ left P) :
    (grow S p G h).2 ⋙ front S p.1 = p.2 := by
  rcases p with ⟨(_|n),p⟩ <;> exact attach_prefix _ _ _ _
theorem grow_last (p : Path S X) (G : X ⥤ Apex P) (h : dst S p = G ⋙ left P) :
    (grow S p G h).2 ⋙ last S p.1 = G := by
  rcases p with ⟨(_|n),p⟩ <;> exact attach_last _ _ _ _
theorem grow_src (p : Path S X) (G : X ⥤ Apex P) (h : dst S p = G ⋙ left P) :
    src S (grow S p G h) = src S p :=
  (congrArg ((grow S p G h).2 ⋙ ·) (last_src S p.1).symm).trans (congrArg (· ⋙ (power S p.1).source) (grow_pre S p G h))
theorem grow_dst (p : Path S X) (G : X ⥤ Apex P) (h : dst S p = G ⋙ left P) :
    dst S (grow S p G h) = G ⋙ right P S :=
  (congrArg ((grow S p G h).2 ⋙ ·) (last_dst S p.1).symm).trans (congrArg (· ⋙ right P S) (grow_last S p G h))
theorem snoc_ext (n : Nat) {F G : X ⥤ (power S (n+1)).apex}
    (p : F ⋙ front S n = G ⋙ front S n) (q : F ⋙ last S n = G ⋙ last S n) : F = G := by
  cases n <;> exact last_ext _ p q
theorem grow_eta (n : Nat) (F : X ⥤ (power S (n+1)).apex) :
    grow S ⟨n,F ⋙ front S n⟩ (F ⋙ last S n) (congrArg (F ⋙ ·) (boundary S n)) = ⟨n+1,F⟩ :=
  congrArg (Sigma.mk (n+1)) (snoc_ext S n (grow_pre ..) (grow_last ..))
theorem right_nil (p : Path S X) (A : X ⥤ B) (h : dst S p = src S (nil S A)) :
    join S p (nil S A) h = p := rfl
theorem join_pre (m n : Nat) (F : X ⥤ (power S m).apex) (G : X ⥤ (power S (n+1)).apex)
    (h : F ⋙ (power S m).dest = G ⋙ (power S (n+1)).source) :
    (blocks S m (n+1)).assemble F G h ⋙ front S (m+n) =
      (blocks S m n).assemble F (G ⋙ front S n) (h.trans (congrArg (G ⋙ ·) (last_src S n).symm)) := by
  cases m <;> cases n <;> exact Cut.nextAssemble_pre S _ _ _ _
theorem join_last (m n : Nat) (F : X ⥤ (power S m).apex) (G : X ⥤ (power S (n+1)).apex)
    (h : F ⋙ (power S m).dest = G ⋙ (power S (n+1)).source) :
    (blocks S m (n+1)).assemble F G h ⋙ last S (m+n) = G ⋙ last S n := by
  cases m <;> cases n <;> exact Cut.nextAssemble_grade S _ _ _ _
theorem join_grow (p q : Path S X) (G : X ⥤ Apex P) (h : dst S p = src S q) (k : dst S q = G ⋙ left P) :
    join S p (grow S q G k) (h.trans (grow_src S q G k).symm) =
    grow S (join S p q h) G ((join_dst S p q h).trans k) := by
  apply congrArg (Sigma.mk (p.1+q.1+1))
  apply snoc_ext S
  · refine (join_pre S p.1 q.1 _ _ _).trans (Eq.trans ?_ (grow_pre S (join S p q h) G _).symm)
    let c := blocks S p.1 q.1
    apply c.ext
    · exact (c.first_assemble ..).trans (c.first_assemble ..).symm
    · exact (c.rest_assemble ..).trans ((grow_pre S q G k).trans (c.rest_assemble ..).symm)
  · exact (join_last S p.1 q.1 _ _ _).trans ((grow_last S q G k).trans (grow_last S (join S p q h) G _).symm)
theorem pathInd {M : Path S X → Prop} (z : ∀ A, M (nil S A))
    (g : ∀ p G h, M p → M (grow S p G h)) (p : Path S X) : M p := by
  rcases p with ⟨n,F⟩
  induction n with
  | zero => exact z F
  | succ n ih =>
    rw [← grow_eta S n F]
    exact g _ _ _ (ih _)
theorem join_congr {p p' q q' : Path S X} (e : p = p') (f : q = q')
    {h : dst S p = src S q} {k : dst S p' = src S q'} : join S p q h = join S p' q' k := by subst p'; subst q'; rfl
theorem grow_congr {p q : Path S X} (e : p = q) (G : X ⥤ Apex P)
    {h : dst S p = G ⋙ left P} {k : dst S q = G ⋙ left P} : grow S p G h = grow S q G k := by subst q; rfl
theorem left_nil (p : Path S X) : join S (nil S (src S p)) p rfl = p := by
  apply pathInd S (M := fun p => join S (nil S (src S p)) p rfl = p) _ _ p
  · intro A; rfl
  · intro q G k ih
    let p := nil S (src S q)
    have a := grow_src S q G k
    exact (join_congr S (congrArg (nil S) a) rfl).trans
      ((join_grow S p q G rfl k).trans (grow_congr S ih G))
theorem join_assoc (p q r : Path S X) (h : dst S p = src S q) (k : dst S q = src S r) :
    join S (join S p q h) r ((join_dst S p q h).trans k) =
      join S p (join S q r k) (h.trans (join_src S q r k).symm) := by
  revert k
  apply pathInd S (M := fun r => ∀ k : dst S q = src S r,
    join S (join S p q h) r ((join_dst S p q h).trans k) =
      join S p (join S q r k) (h.trans (join_src S q r k).symm)) _ _ r
  · intro A k; exact (right_nil S _ _ _).trans (join_congr S rfl (right_nil S q A k).symm)
  · intro t G j ih k
    have kt := k.trans (grow_src S t G j)
    have eq := join_grow S q t G kt j
    exact (join_grow S (join S p q h) t G ((join_dst S p q h).trans kt) j).trans
      ((grow_congr S (ih kt) G).trans
        ((join_grow S p (join S q t kt) G (h.trans (join_src S q t kt).symm) ((join_dst S q t kt).trans j)).symm.trans
          (join_congr S rfl eq.symm)))

/-- Horizontal product of arbitrary diagrams in the originally tagged native telescope. -/
noncomputable def mul {Y : Type*} [Category* Y] (F G : Y ⥤ tel S) (h : F ⋙ rightLeg S = G ⋙ leftLeg S) :=
  Strict.lift _ _ F G h ⋙ binary S
theorem mul_src {Y : Type*} [Category* Y] (F G : Y ⥤ tel S) (h : F ⋙ rightLeg S = G ⋙ leftLeg S) :
    mul S F G h ⋙ leftLeg S = F ⋙ leftLeg S := congrArg (Strict.lift _ _ F G h ⋙ ·) (binary_source S)
theorem mul_dst {Y : Type*} [Category* Y] (F G : Y ⥤ tel S) (h : F ⋙ rightLeg S = G ⋙ leftLeg S) :
    mul S F G h ⋙ rightLeg S = G ⋙ rightLeg S := congrArg (Strict.lift _ _ F G h ⋙ ·) (binary_dest S)
theorem mul_comp {Y Z : Type*} [Category* Y] [Category* Z] (J : Z ⥤ Y) (F G : Y ⥤ tel S)
    (h : F ⋙ rightLeg S = G ⋙ leftLeg S) : J ⋙ mul S F G h = mul S (J ⋙ F) (J ⋙ G) (congrArg (J ⋙ ·) h) :=
  congrArg (· ⋙ binary S) (Strict.uniq _ _ (J ⋙ Strict.lift _ _ F G h) (Strict.lift _ _ (J ⋙ F) (J ⋙ G) (congrArg (J ⋙ ·) h)) rfl rfl)
theorem mul_congr {Y : Type*} [Category* Y] {F F' G G' : Y ⥤ tel S} (f : F = F') (g : G = G')
    {h : F ⋙ rightLeg S = G ⋙ leftLeg S} {j : F' ⋙ rightLeg S = G' ⋙ leftLeg S} : mul S F G h = mul S F' G' j := by subst F'; subst G'; rfl
theorem tag_join (p q : Path S X) (h : dst S p = src S q) :
    mul S (tagged S p) (tagged S q) h = tagged S (join S p q h) := by
  let K := Strict.lift (power S p.1).dest (power S q.1).source p.2 q.2 h
  have H : Strict.lift (rightLeg S) (leftLeg S) (tagged S p) (tagged S q) h = K ⋙ tagPair S (p.1,q.1) :=
    Strict.uniq _ _ _ _ rfl rfl
  let c := blocks S p.1 q.1
  have E : K ⋙ c.joinFunctor = c.assemble p.2 q.2 h :=
    c.ext ((congrArg (K ⋙ ·) c.join_first).trans (c.first_assemble ..).symm)
      ((congrArg (K ⋙ ·) c.join_rest).trans (c.rest_assemble ..).symm)
  exact (congrArg (· ⋙ binary S) H).trans (congrArg (· ⋙ incl S (p.1+q.1)) E)
theorem tag_assoc (p q r : Path S X) (h : dst S p = src S q) (k : dst S q = src S r) :
    mul S (mul S (tagged S p) (tagged S q) h) (tagged S r) ((mul_dst S (tagged S p) (tagged S q) h).trans k) =
      mul S (tagged S p) (mul S (tagged S q) (tagged S r) k) (h.trans (mul_src S (tagged S q) (tagged S r) k).symm) := by
  exact (mul_congr S (tag_join S p q h) rfl).trans ((tag_join S _ r ((join_dst S p q h).trans k)).trans
    ((congrArg (tagged S) (join_assoc S p q r h k)).trans
      ((tag_join S p _ (h.trans (join_src S q r k).symm)).symm.trans (mul_congr S rfl (tag_join S q r k).symm))))

namespace Whole
open NativeBlocks.Nested
universe u v
variable {D : Type u} [Category.{max u v} D] {Q : Endpoints.{u,max u v,u,max u v} D} (R : Q.Split)
abbrev triple := (word R 3).apex
abbrev ab : triple R ⥤ pairs R := Strict.fst _ _
abbrev a : triple R ⥤ tel R := ab R ⋙ Strict.fst _ _
abbrev b : triple R ⥤ tel R := ab R ⋙ Strict.snd _ _
abbrev c : triple R ⥤ tel R := Strict.snd _ _
theorem abMatch : a R ⋙ rightLeg R = b R ⋙ leftLeg R := congrArg (ab R ⋙ ·) (Strict.commute _ _)
theorem bcMatch : b R ⋙ rightLeg R = c R ⋙ leftLeg R := Strict.commute _ _
noncomputable def leftThree := mul R (mul R (a R) (b R) (abMatch R)) (c R) ((mul_dst R _ _ _).trans (bcMatch R))
noncomputable def rightThree := mul R (a R) (mul R (b R) (c R) (bcMatch R)) ((abMatch R).trans (mul_src R _ _ _).symm)
abbrev fixed (m n k : Nat) := Strict.Match (Strict.snd (power R m).dest (power R n).source ⋙ (power R n).dest) (power R k).source
abbrev fstTwo (m n k : Nat) : fixed R m n k ⥤ part R (m,n) := Strict.fst _ _
abbrev third (m n k : Nat) : fixed R m n k ⥤ (power R k).apex := Strict.snd _ _
def tagThree (m n k : Nat) : fixed R m n k ⥤ triple R := Strict.lift _ _
  (fstTwo R m n k ⋙ tagPair R (m,n)) (third R m n k ⋙ incl R k) (Strict.commute _ _)
set_option maxHeartbeats 1600000 in
theorem assoc_at (m n k : Nat) : tagThree R m n k ⋙ leftThree R = tagThree R m n k ⋙ rightThree R := by
  let T := tagThree R m n k
  let p : Path R (fixed R m n k) := ⟨m,fstTwo R m n k ⋙ Strict.fst _ _⟩
  let q : Path R (fixed R m n k) := ⟨n,fstTwo R m n k ⋙ Strict.snd _ _⟩
  let r : Path R (fixed R m n k) := ⟨k,third R m n k⟩
  have i : dst R p = src R q := congrArg (T ⋙ ·) (abMatch R)
  have j : dst R q = src R r := congrArg (T ⋙ ·) (bcMatch R)
  have A := mul_comp R T (a R) (b R) (abMatch R)
  have B := mul_comp R T (b R) (c R) (bcMatch R)
  have L := mul_comp R T (mul R (a R) (b R) (abMatch R)) (c R) ((mul_dst R _ _ (abMatch R)).trans (bcMatch R))
  have H := mul_comp R T (a R) (mul R (b R) (c R) (bcMatch R)) ((abMatch R).trans (mul_src R _ _ (bcMatch R)).symm)
  exact L.trans ((mul_congr R A rfl).trans ((tag_assoc R p q r i j).trans ((mul_congr R rfl B.symm).trans H.symm)))
set_option backward.isDefEq.respectTransparency false in
theorem assoc : leftThree R = rightThree R := by
  fapply Functor.ext
  · rintro ⟨⟨⟨m,x⟩,⟨n,y⟩,h⟩,⟨k,z⟩,g⟩
    exact Functor.congr_obj (assoc_at R m n k) ⟨⟨x,y,h⟩,z,g⟩
  · rintro ⟨⟨⟨m,x⟩,⟨n,y⟩,h⟩,⟨k,z⟩,g⟩ ⟨⟨⟨_,x'⟩,⟨_,y'⟩,h'⟩,⟨_,z'⟩,g'⟩ ⟨⟨⟨⟨f,l,e⟩⟩,v,i⟩⟩
    cases f with | mk f =>
      rename_i xnew
      cases l with | mk l =>
        rename_i ynew
        cases v with | mk v =>
          rename_i znew
          exact Functor.congr_hom (assoc_at R m n k) (show (⟨⟨x,y,h⟩,z,g⟩ : fixed R m n k) ⟶ ⟨⟨xnew,ynew,h'⟩,znew,g'⟩ from ⟨⟨⟨⟨f,l,e⟩⟩,v,i⟩⟩)
variable {Y : Type*} [Category* Y]
def liftThree (F G H : Y ⥤ tel R) (i : F ⋙ rightLeg R = G ⋙ leftLeg R) (j : G ⋙ rightLeg R = H ⋙ leftLeg R) :
    Y ⥤ triple R := Strict.lift _ _ (Strict.lift _ _ F G i) H j
theorem mul_assoc (F G H : Y ⥤ tel R) (i : F ⋙ rightLeg R = G ⋙ leftLeg R) (j : G ⋙ rightLeg R = H ⋙ leftLeg R) :
    mul R (mul R F G i) H ((mul_dst R F G i).trans j) = mul R F (mul R G H j) (i.trans (mul_src R G H j).symm) := by
  let T := liftThree R F G H i j
  have A := mul_comp R T (a R) (b R) (abMatch R)
  have B := mul_comp R T (b R) (c R) (bcMatch R)
  have L := mul_comp R T (mul R (a R) (b R) (abMatch R)) (c R) ((mul_dst R _ _ (abMatch R)).trans (bcMatch R))
  have H' := mul_comp R T (a R) (mul R (b R) (c R) (bcMatch R)) ((abMatch R).trans (mul_src R _ _ (bcMatch R)).symm)
  exact (mul_congr R A.symm rfl).trans (L.symm.trans ((congrArg (T ⋙ ·) (assoc R)).trans (H'.trans (mul_congr R rfl B))))
noncomputable def unitLeft := mul R (leftLeg R ⋙ incl R 0) (𝟭 _) rfl
noncomputable def unitRight := mul R (𝟭 _) (rightLeg R ⋙ incl R 0) rfl
theorem left_unit_at (n : Nat) : incl R n ⋙ unitLeft R = incl R n := by
  let q : Path R (power R n).apex := ⟨n,𝟭 _⟩
  exact (mul_comp R (incl R n) (leftLeg R ⋙ incl R 0) (𝟭 _) rfl).trans ((tag_join R (nil R (src R q)) q rfl).trans (congrArg (tagged R) (left_nil R q)))
theorem right_unit_at (n : Nat) : incl R n ⋙ unitRight R = incl R n := by
  let p : Path R (power R n).apex := ⟨n,𝟭 _⟩
  exact (mul_comp R (incl R n) (𝟭 _) (rightLeg R ⋙ incl R 0) rfl).trans ((tag_join R p (nil R (dst R p)) rfl).trans (congrArg (tagged R) (right_nil R p _ rfl)))
theorem left_unit : unitLeft R = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (left_unit_at R n) x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (left_unit_at R n) f
theorem right_unit : unitRight R = 𝟭 _ := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (right_unit_at R n) x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (right_unit_at R n) f
theorem mul_left (F : Y ⥤ tel R) : mul R ((F ⋙ leftLeg R) ⋙ incl R 0) F rfl = F :=
  (mul_comp R F (leftLeg R ⋙ incl R 0) (𝟭 _) rfl).symm.trans (congrArg (F ⋙ ·) (left_unit R))
theorem mul_right (F : Y ⥤ tel R) : mul R F ((F ⋙ rightLeg R) ⋙ incl R 0) rfl = F :=
  (mul_comp R F (𝟭 _) (rightLeg R ⋙ incl R 0) rfl).symm.trans (congrArg (F ⋙ ·) (right_unit R))
end Whole

end ContextualComposition.GrothendieckStep.NativeAssoc
