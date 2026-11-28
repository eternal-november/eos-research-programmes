import Mathlib

namespace TimerSupport

def occurs (arm offset target : Int) : Int :=
  max arm (target-offset)

def tolerable (first last lo hi a b : Int) : Prop :=
  (lo ≤ a ∧ a ≤ hi) ∧ (lo ≤ b ∧ b ≤ hi) ∧
       ((a ≤ first ∧ b ≤ first) ∨ (last < a ∧ last < b))

def projects (first last lo hi aa ab da db h : Int) : Prop :=
  ((lo ≤ aa ∨ lo+da ≤ h) ∧ aa ≤ hi ∧ h ≤ hi+da) ∧
  ((lo ≤ ab ∨ lo+db ≤ h) ∧ ab ≤ hi ∧ h ≤ hi+db) ∧
  (((aa ≤ first ∧ h ≤ first+da) ∧ (ab ≤ first ∧ h ≤ first+db)) ∨
   ((last < aa ∨ last+da < h) ∧ (last < ab ∨ last+db < h)))

theorem exact (first last lo hi aa ab da db h : Int) :
    tolerable first last lo hi (occurs aa da h) (occurs ab db h) ↔
          projects first last lo hi aa ab da db h := by
  unfold tolerable occurs projects
  simp only [max_le_iff, le_max_iff, lt_max_iff]
  omega

theorem unique_common_target (h : Int) :
    (projects 4 6 3 9 1 1 1 1 h ∧ projects 4 6 3 9 1 1 (-2) (-2) h) ↔ h=5 := by
  unfold projects
  omega

theorem mixed_distinguishes :
    ¬ projects 4 6 3 9 1 1 1 (-2) 5 := by
  unfold projects
  norm_num

theorem translates_held_clock (t h bias shift : Int) :
    h ≤ t+bias ↔ h+shift ≤ t+(bias+shift) := by
  omega

end TimerSupport
