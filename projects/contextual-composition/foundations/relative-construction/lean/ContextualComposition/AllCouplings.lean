module
public import ContextualComposition.CouplingPullbacks

/-! Relational composition of all couplings. A ternary witness must realize all three prescribed marginals, including the output joint law. -/

@[expose] public section
namespace ContextualComposition.AllCouplings
open CategoryTheory CouplingPullbacks

universe u
variable (F : Type u ⥤ Type u) {X Y Z W S K L : Type u}

def xy (t : X × Y × Z) := (t.1,t.2.1)
def yz (t : X × Y × Z) := t.2
def xz (t : X × Y × Z) := (t.1,t.2.2)
def diag (x : X) := (x,x)

def Comp (a : F.obj (X × Y)) (b : F.obj (Y × Z)) (c : F.obj (X × Z)) : Prop :=
  ∃ t : F.obj (X × Y × Z), push F xy t = a ∧ push F yz t = b ∧ push F xz t = c

/-- Transfer a weak pullback lift to a chosen raw carrier by an actual section of the comparison. -/
theorem glue (weak : WeakPullbacks F) (f : X → S) (g : Y → S) (l : K → X) (r : K → Y)
    (build : PB f g → K) (hl : l ∘ build = left) (hr : r ∘ build = right)
    (a : F.obj X) (b : F.obj Y) (eq : push F f a = push F g b) :
    ∃ s : F.obj K, push F l s = a ∧ push F r s = b := by
  obtain ⟨t,ht⟩ := weak f g ⟨(a,b),eq⟩
  refine ⟨push F build t,?_,?_⟩
  · rw [push_push,hl]; exact congrArg (fun w => w.val.1) ht
  · rw [push_push,hr]; exact congrArg (fun w => w.val.2) ht

theorem marginal (leg : K → X) (small : X → Y) (large : K → Y) (comm : small ∘ leg = large)
    {s : F.obj K} {a : F.obj X} (h : push F leg s = a) : push F large s = push F small a := by
  rw [← comm,← push_push,h]

theorem pair_exists (weak : WeakPullbacks F) (a : F.obj (X × Y)) (b : F.obj (Y × Z))
    (matchY : push F Prod.snd a = push F Prod.fst b) : ∃ c, Comp F a b c := by
  obtain ⟨s,hl,hr⟩ := glue F weak Prod.snd Prod.fst xy yz
    (fun p => (p.val.1.1,p.val.1.2,p.val.2.2)) rfl
    (by funext p; exact Prod.ext p.property rfl) a b matchY
  exact ⟨_,s,hl,hr,rfl⟩

def firstThree (p : X × Y × Z × W) := (p.1,p.2.1,p.2.2.1)
def lastThree (p : X × Y × Z × W) := p.2
def skipSecond (p : X × Y × Z × W) := (p.1,p.2.2.1,p.2.2.2)
def skipThird (p : X × Y × Z × W) := (p.1,p.2.1,p.2.2.2)

/-- Four-coordinate gluing keeps the same outer effect on both sides of the composition relation. -/
theorem associative (weak : WeakPullbacks F) (a : F.obj (X × Y)) (b : F.obj (Y × Z))
    (c : F.obj (Z × W)) (e : F.obj (X × W)) :
    (∃ d, Comp F a b d ∧ Comp F d c e) ↔ ∃ d, Comp F b c d ∧ Comp F a d e := by
  constructor
  · rintro ⟨d,⟨s,sa,sb,sd⟩,t,td,tc,te⟩
    obtain ⟨j,js,jt⟩ := glue F weak xz xy firstThree skipSecond
      (fun p => (p.val.1.1,p.val.1.2.1,p.val.1.2.2,p.val.2.2.2))
      rfl (by
        funext p
        rcases p with ⟨⟨⟨x,y,z⟩,x',z',w⟩,h⟩
        change (x,z) = (x',z') at h
        cases h
        rfl)
      s t (sd.trans td.symm)
    refine ⟨push F xz (push F lastThree j),⟨push F lastThree j,?_,?_,rfl⟩,push F skipThird j,?_,?_,?_⟩
    · rw [push_push]; exact (marginal F _ yz _ rfl js).trans sb
    · rw [push_push]; exact (marginal F _ yz _ rfl jt).trans tc
    · rw [push_push]; exact (marginal F _ xy _ rfl js).trans sa
    · rw [push_push,push_push]; rfl
    · rw [push_push]; exact (marginal F _ xz _ rfl jt).trans te
  · rintro ⟨d,⟨s,sb,sc,sd⟩,t,ta,td,te⟩
    obtain ⟨j,js,jt⟩ := glue F weak xz yz lastThree skipThird
      (fun p => (p.val.2.1,p.val.1.1,p.val.1.2.1,p.val.1.2.2))
      rfl (by funext p; exact Prod.ext rfl p.property)
      s t (sd.trans td.symm)
    refine ⟨push F xz (push F firstThree j),⟨push F firstThree j,?_,?_,rfl⟩,push F skipSecond j,?_,?_,?_⟩
    · rw [push_push]; exact (marginal F _ xy _ rfl jt).trans ta
    · rw [push_push]; exact (marginal F _ xy _ rfl js).trans sb
    · rw [push_push,push_push]; rfl
    · rw [push_push]; exact (marginal F _ yz _ rfl js).trans sc
    · rw [push_push]; exact (marginal F _ xz _ rfl jt).trans te

theorem left_identity (weak : WeakPullbacks F) (p : F.obj X) (a e : F.obj (X × Y))
    (ha : push F Prod.fst a = p) : Comp F (push F diag p) a e ↔ a = e := by
  let duplicate (x : X × Y) := (x.1,x.1,x.2)
  constructor
  · rintro ⟨t,ht,h₁,h₂⟩
    obtain ⟨s,_,hs⟩ := glue F weak diag xy Prod.fst duplicate
      (fun z => (z.val.1,z.val.2.2.2)) rfl
      (by
        funext z
        rcases z with ⟨⟨x,x',x'',y⟩,h⟩
        change (x,x) = (x',x'') at h
        cases h
        rfl) p t ht.symm
    rw [← h₁,← h₂,← hs,push_push,push_push]; rfl
  · rintro rfl
    refine ⟨push F duplicate a,?_,?_,?_⟩
    · rw [push_push,← ha,push_push]; rfl
    · exact (push_push F duplicate yz a).trans (push_id F a)
    · exact (push_push F duplicate xz a).trans (push_id F a)

theorem right_identity (weak : WeakPullbacks F) (p : F.obj Y) (a e : F.obj (X × Y))
    (ha : push F Prod.snd a = p) : Comp F a (push F diag p) e ↔ a = e := by
  let duplicate (x : X × Y) := (x.1,x.2,x.2)
  constructor
  · rintro ⟨t,h₁,ht,h₂⟩
    obtain ⟨s,_,hs⟩ := glue F weak diag yz Prod.snd duplicate
      (fun z => (z.val.2.1,z.val.1)) rfl (by funext z; exact Prod.ext rfl z.property) p t ht.symm
    rw [← h₁,← h₂,← hs,push_push,push_push]; rfl
  · rintro rfl
    refine ⟨push F duplicate a,?_,?_,?_⟩
    · exact (push_push F duplicate xy a).trans (push_id F a)
    · rw [push_push,← ha,push_push]; rfl
    · exact (push_push F duplicate xz a).trans (push_id F a)

structure Effect (F : Type u ⥤ Type u) where
  carrier : Type u
  law : F.obj carrier

def Hom (P Q : Effect F) :=
  {s : F.obj (P.carrier × Q.carrier) // push F Prod.fst s = P.law ∧ push F Prod.snd s = Q.law}

theorem endpoints (a : F.obj (X × Y)) (b : F.obj (Y × Z)) (e : F.obj (X × Z))
    (h : Comp F a b e) : push F Prod.fst e = push F Prod.fst a ∧ push F Prod.snd e = push F Prod.snd b := by
  obtain ⟨s,rfl,rfl,rfl⟩ := h
  constructor <;> rw [push_push,push_push] <;> rfl

def identity (P : Effect F) : Hom F P P :=
  ⟨push F diag P.law, (push_push F diag Prod.fst _).trans (push_id F _),
    (push_push F diag Prod.snd _).trans (push_id F _)⟩

theorem nonblocking (weak : WeakPullbacks F) {P Q R : Effect F} (a : Hom F P Q) (b : Hom F Q R) :
    ∃ e : Hom F P R, Comp F a.val b.val e.val := by
  obtain ⟨e,h⟩ := pair_exists F weak a.val b.val (a.property.2.trans b.property.1.symm)
  have hh := endpoints F _ _ _ h
  exact ⟨⟨e,hh.1.trans a.property.1,hh.2.trans b.property.2⟩,h⟩

end ContextualComposition.AllCouplings
