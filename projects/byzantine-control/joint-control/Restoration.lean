import Std

namespace ByzantineJointRestoration

def put (m : Nat → α) (address : Nat) (value : α) : Nat → α :=
  fun a => if a = address then value else m a

def install (addresses : List Nat) (image : Nat → α) (m : Nat → α) : Nat → α :=
  match addresses with
  | [] => m
  | a :: rest => install rest image (put m a (image a))

theorem put_same (m : Nat → α) (a : Nat) (v : α) : put m a v a = v := by
  simp [put]

theorem install_preserves_correct (addresses : List Nat) (image m : Nat → α)
    (a : Nat) (h : m a = image a) : install addresses image m a = image a := by
  induction addresses generalizing m with
  | nil => exact h
  | cons b rest ih =>
    apply ih
    by_cases hab : a = b
    · simp [put, hab]
    · simpa [put, hab] using h

theorem installed_member (addresses : List Nat) (image m : Nat → α)
    (a : Nat) (h : a ∈ addresses) : install addresses image m a = image a := by
  induction addresses generalizing m with
  | nil => simp at h
  | cons b rest ih =>
    simp only [List.mem_cons] at h
    rcases h with hab | hr
    · subst a
      exact install_preserves_correct rest image (put m b (image b)) b (by simp [put])
    · exact ih (put m b (image b)) hr

theorem unlisted_untouched (addresses : List Nat) (image m : Nat → α)
    (a : Nat) (h : a ∉ addresses) : install addresses image m a = m a := by
  induction addresses generalizing m with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.mem_cons, not_or] at h
    exact (ih (put m b (image b)) h.2).trans (by simp [put,h.1])

structure Processor where
  cells : Nat → Bool
  halted : Bool
  deriving Inhabited

inductive Operation where
  | halt
  | write (address : Nat) (value : Bool)
  | boot

def applyOp (op : Operation) (s : Processor) : Processor :=
  match op with
  | .halt => { s with halted := true }
  | .write a v => if s.halted then { s with cells := put s.cells a v } else s
  | .boot => { s with halted := false }

def execute (ops : List Operation) (s : Processor) : Processor :=
  match ops with
  | [] => s
  | op :: rest => execute rest (applyOp op s)

def writes (addresses : List Nat) (image : Nat → Bool) :=
  addresses.map (fun a => Operation.write a (image a))

theorem execute_writes (addresses : List Nat) (image : Nat → Bool) (s : Processor)
    (halted : s.halted = true) :
    execute (writes addresses image) s = { cells := install addresses image s.cells, halted := true } := by
  induction addresses generalizing s with
  | nil => cases s; simp_all [execute,writes,install]
  | cons a rest ih =>
    simp only [writes,List.map_cons,execute]
    simp only [applyOp,halted, if_true]
    simpa only [writes,install] using ih { cells := put s.cells a (image a), halted := true } rfl

theorem execute_append (a b : List Operation) (s : Processor) :
    execute (a ++ b) s = execute b (execute a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (applyOp x s)

def repairScript (addresses : List Nat) (image : Nat → Bool) : List Operation :=
  .halt :: (writes addresses image ++ [.boot])

theorem actual_script_installs (addresses : List Nat) (image : Nat → Bool) (s : Processor) :
    execute (repairScript addresses image) s =
      { cells := install addresses image s.cells, halted := false } := by
  simp only [repairScript,execute,applyOp]
  rw [execute_append, execute_writes addresses image _ rfl]
  rfl

theorem actual_script_member (addresses : List Nat) (image : Nat → Bool)
    (s : Processor) (a : Nat) (h : a ∈ addresses) :
    (execute (repairScript addresses image) s).cells a = image a := by
  rw [actual_script_installs]
  exact installed_member addresses image s.cells a h

theorem script_operation_count (addresses : List Nat) (image : Nat → Bool) :
    (repairScript addresses image).length = addresses.length + 2 := by
  simp [repairScript,writes,Nat.add_comm,Nat.add_left_comm]

/- Real elapsed phases: each nominal operation is one tick in the selected
specialization; the general prose law sums arbitrary bounded durations. -/
def outage (m inference lag : Nat) : Nat := m + 2 + inference + lag

theorem memory_completion_not_functional_completion (m inference lag : Nat) :
    m + 2 ≤ outage m inference lag := by unfold outage; omega

theorem reconstruction_horizon (release start period duration : Nat)
    (_afterRelease : release ≤ start) (coverage : start < release + period) :
    start + duration < release + (period + duration) := by omega

def InMaintenance (S D k t : Nat) : Prop := k*S ≤ t ∧ t < k*S+D

theorem maintenance_nonoverlap (S D k l t : Nat) (fit : D ≤ S) (order : k < l)
    (hk : InMaintenance S D k t) : ¬ InMaintenance S D l t := by
  intro hl
  have hmul : (k+1)*S ≤ l*S := Nat.mul_le_mul_right S order
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  unfold InMaintenance at hk hl
  omega

def phaseWait (P phase residue : Nat) : Nat :=
  if residue ≤ phase then phase-residue else P-(residue-phase)

theorem phase_wait_bounded (P phase residue : Nat) (_hp : 0 < P)
    (hphase : phase < P) (_hr : residue < P) : phaseWait P phase residue < P := by
  unfold phaseWait
  split <;> omega

theorem numeric_horizon : outage 8 20 4 = 34 ∧ 13*(34+1)=455 ∧ 455+34=489 := by decide

theorem numeric_loss_bound (tools initial acquisitions maintenance : Nat)
    (ht : tools ≤ 1) (hi : initial ≤ 1) (ha : acquisitions ≤ 1) (hm : maintenance ≤ 1) :
    tools + initial + acquisitions + maintenance ≤ 4 := by omega

#print axioms put_same
#print axioms install_preserves_correct
#print axioms installed_member
#print axioms unlisted_untouched
#print axioms execute_writes
#print axioms execute_append
#print axioms actual_script_installs
#print axioms actual_script_member
#print axioms script_operation_count
#print axioms memory_completion_not_functional_completion
#print axioms reconstruction_horizon
#print axioms maintenance_nonoverlap
#print axioms phase_wait_bounded
#print axioms numeric_horizon
#print axioms numeric_loss_bound
end ByzantineJointRestoration
