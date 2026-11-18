import Std

namespace ByzantineRecurringRenewal

-- Quarter-unit coordinates: contact range [0,96], bias/threshold 42.
def clip96 (x : Int) : Int := if x < 0 then 0 else if 96 < x then 96 else x

def contact (q field : Int) : Int := clip96 (q + field - 42)

theorem clip96_bounds (x : Int) : 0 ≤ clip96 x ∧ clip96 x ≤ 96 := by
  unfold clip96
  split
  · omega
  · split <;> omega

theorem clip96_lower (x k : Int) (hk : 0 ≤ k) (hk96 : k ≤ 96) (hx : k ≤ x) :
    k ≤ clip96 x := by
  unfold clip96
  split
  · omega
  · split <;> omega

theorem idle_contact_stays_closed (field : Int) (h : field ≤ 41) :
    contact 0 field = 0 := by
  have hneg : field - 42 < 0 := by omega
  simp [contact, clip96, hneg]

theorem four_tick_open (q a b c d : Int) (hq : 0 ≤ q)
    (ha : 71 ≤ a) (hb : 71 ≤ b) (hc : 71 ≤ c) (hd : 71 ≤ d) :
    contact (contact (contact (contact q a) b) c) d = 96 := by
  have h1 : 29 ≤ contact q a := clip96_lower _ _ (by omega) (by omega) (by omega)
  have h2 : 58 ≤ contact (contact q a) b :=
    clip96_lower _ _ (by omega) (by omega) (by omega)
  have h3 : 87 ≤ contact (contact (contact q a) b) c :=
    clip96_lower _ _ (by omega) (by omega) (by omega)
  have h4 : 96 ≤ contact (contact (contact (contact q a) b) c) d :=
    clip96_lower _ _ (by omega) (by omega) (by omega)
  have cap := (clip96_bounds (contact (contact (contact q a) b) c + d - 42)).2
  change contact (contact (contact (contact q a) b) c) d ≤ 96 at cap
  omega

theorem active_close_one_tick (q field : Int) (hq : q ≤ 96) (hf : field ≤ -183) :
    contact q field = 0 := by
  have hneg : q + field - 42 < 0 := by omega
  simp [contact, clip96, hneg]

def cell (opened old : Bool) (field : Int) : Bool :=
  if opened then if 42 < field then true else if field < -42 then false else old else old

theorem weak_field_retains (opened old : Bool) (field : Int)
    (lo : -41 ≤ field) (hi : field ≤ 41) : cell opened old field = old := by
  have hn1 : ¬ 42 < field := by omega
  have hn2 : ¬ field < -42 := by omega
  simp [cell, hn1, hn2]

theorem positive_field_writes (old : Bool) (field : Int) (h : 71 ≤ field) :
    cell true old field = true := by
  have hp : 42 < field := by omega
  simp [cell, hp]

theorem negative_field_writes (old : Bool) (field : Int) (h : field ≤ -71) :
    cell true old field = false := by
  have hn1 : ¬ 42 < field := by omega
  have hn2 : field < -42 := by omega
  simp [cell, hn1, hn2]

def write (mem : Nat → Bool) (a : Nat) (v : Bool) : Nat → Bool :=
  fun b => if b = a then v else mem b

def fields (mem : Nat → Bool) (z : Nat → Int) : Nat → Bool :=
  fun b => cell true (mem b) (z b)

theorem physical_bit_step (mem : Nat → Bool) (z : Nat → Int) (a : Nat) (v : Bool)
    (selected : if v then 71 ≤ z a else z a ≤ -71)
    (other : ∀ b, b ≠ a → -41 ≤ z b ∧ z b ≤ 41) :
    fields mem z = write mem a v := by
  funext b
  by_cases h : b = a
  · subst b
    cases v with
    | false => simpa [fields, write] using negative_field_writes (mem a) (z a) selected
    | true => simpa [fields, write] using positive_field_writes (mem a) (z a) selected
  · have hb := other b h
    simpa [fields, write, h] using weak_field_retains true (mem b) (z b) hb.1 hb.2

def copyPrefix (image initial : Nat → Bool) : Nat → (Nat → Bool)
  | 0 => initial
  | n+1 => write (copyPrefix image initial n) n (image n)

theorem copied_prefix (image initial : Nat → Bool) (n a : Nat) (ha : a < n) :
    copyPrefix image initial n a = image a := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : a = n
    · simp [copyPrefix, write, h]
    · have old : a < n := by omega
      simpa [copyPrefix, write, h] using ih old

theorem unwritten_suffix (image initial : Nat → Bool) (n a : Nat) (ha : n ≤ a) :
    copyPrefix image initial n a = initial a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : a ≠ n := by omega
    have old : n ≤ a := by omega
    simpa [copyPrefix, write, h] using ih old

theorem selected_field_margin (G B good bad noise : Int)
    (hg : 28 ≤ G) (hb : B ≤ 5) (hgood : 4*G ≤ good)
    (hbad : -8*B ≤ bad) (hnoise : -1 ≤ noise) :
    71 ≤ good + bad + noise := by omega

theorem idle_field_margin (B bad noise : Int)
    (hb : B ≤ 5) (hbad : bad ≤ 8*B) (hnoise : noise ≤ 1) :
    bad + noise ≤ 41 := by omega

theorem closing_field_margin (G B good bad noise : Int)
    (hg : 28 ≤ G) (hb : B ≤ 5) (hgood : good ≤ -8*G)
    (hbad : bad ≤ 8*B) (hnoise : noise ≤ 1) :
    good + bad + noise ≤ -183 := by omega

theorem predicted_boot_phase (c m k P : Nat) (hk : k < m) :
    (((c+4+k)%P) + (m+1-k))%P = (c+m+5)%P := by
  rw [Nat.mod_add_mod]
  congr 1
  omega

theorem next_cycle_window (t start period duration : Nat)
    (within : start < t + period) :
    start + duration < t + (period + duration) := by omega

theorem separated_events_not_in_short_window (s t a H L : Nat)
    (_order : s < t) (sep : s + L ≤ t) (hs : a ≤ s)
    (ht : t ≤ a + H) (short : H < L) : False := by omega

theorem early_support_bound (permanent initial boundary events maintenance : Nat)
    (hp : permanent ≤ 1) (hi : initial ≤ 1) (ha : boundary ≤ 1)
    (he : events ≤ 1) (hm : maintenance ≤ 1) :
    permanent + initial + boundary + events + maintenance ≤ 5 := by omega

theorem late_support_bound (permanent boundary events maintenance : Nat)
    (hp : permanent ≤ 1) (ha : boundary ≤ 1)
    (he : events ≤ 1) (hm : maintenance ≤ 1) :
    permanent + boundary + events + maintenance ≤ 4 := by omega

theorem disjoint_maintenance (S D k l t : Nat) (fit : D ≤ S) (order : k < l)
    (hk : k*S ≤ t ∧ t < k*S+D) : ¬ (l*S ≤ t ∧ t < l*S+D) := by
  intro hl
  have hm : (k+1)*S ≤ l*S := Nat.mul_le_mul_right S order
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem numeric_timing :
    65536+5=65541 ∧ 65536+30=65566 ∧ 34*65600=2230400 ∧
    2230400+65566=2295966 ∧ 65566≤65600 ∧ 2295966<10000000 := by decide

#print axioms clip96_bounds
#print axioms clip96_lower
#print axioms idle_contact_stays_closed
#print axioms four_tick_open
#print axioms active_close_one_tick
#print axioms weak_field_retains
#print axioms positive_field_writes
#print axioms negative_field_writes
#print axioms physical_bit_step
#print axioms copied_prefix
#print axioms unwritten_suffix
#print axioms selected_field_margin
#print axioms idle_field_margin
#print axioms closing_field_margin
#print axioms predicted_boot_phase
#print axioms next_cycle_window
#print axioms separated_events_not_in_short_window
#print axioms early_support_bound
#print axioms late_support_bound
#print axioms disjoint_maintenance
#print axioms numeric_timing
end ByzantineRecurringRenewal
