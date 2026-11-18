import Std

/-! The algebraic kernel of the existing certified-watermark argument.
The integer true rank may be the analyst's floor of a real physical rank;
no runtime quantization, shared clock, physical progress or bank availability
is supplied by these theorems. The source and timing decode is in the note. -/
namespace PortabilityWatchdog

 theorem refresh_rank_gain (before after high low step : Int)
    (upper : before ≤ high) (lower : low ≤ after)
    (fires : high + step < low) : before + step < after := by
  omega

 theorem no_second_refresh_in_bin (left before after high low step : Int)
    (insideBefore : left ≤ before) (insideAfter : after ≤ left + step)
    (upper : before ≤ high) (lower : low ≤ after) :
    ¬ high + step < low := by
  omega

 theorem measured_refresh_gain (before after oldSample newSample error step : Int)
    (oldUpper : before ≤ oldSample + error)
    (newLower : newSample - error ≤ after)
    (fires : oldSample + error + step < newSample - error) :
    before + step < after := by
  omega

 theorem refresh_increases_mark (oldMark sample error step : Int)
    (nonnegativeError : 0 ≤ error)
    (fires : oldMark + step < sample - error) :
    oldMark + step < sample + error := by
  omega

 theorem monotone_bins_do_not_reenter (bin : Nat → Nat)
    (monotone : ∀ i j, i ≤ j → bin i ≤ bin j)
    (i j k : Nat) (ij : i ≤ j) (jk : j ≤ k)
    (same : bin i = bin k) : bin j = bin i := by
  have a := monotone i j ij
  have b := monotone j k jk
  omega

#print axioms refresh_rank_gain
#print axioms no_second_refresh_in_bin
#print axioms measured_refresh_gain
#print axioms refresh_increases_mark
#print axioms monotone_bins_do_not_reenter
end PortabilityWatchdog
