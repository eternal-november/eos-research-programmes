import Mathlib

namespace DiskMidpoint

theorem center_identity (x y bx bY cx cy : ℝ) :
    ((x-bx)^2+(y-bY)^2 + ((x-cx)^2+(y-cy)^2))/2 =
      (x-(bx+cx)/2)^2+(y-(bY+cy)/2)^2+((bx-cx)^2+(bY-cy)^2)/4 := by
  ring

theorem enclosure (x y bx bY cx cy r s : ℝ)
    (hb : (x-bx)^2+(y-bY)^2 ≤ r^2)
    (hc : (x-cx)^2+(y-cy)^2 ≤ s^2) :
    (x-(bx+cx)/2)^2+(y-(bY+cy)/2)^2 ≤
      (r^2+s^2)/2-((bx-cx)^2+(bY-cy)^2)/4 := by
  have ident := center_identity x y bx bY cx cy
  linarith

end DiskMidpoint

#print axioms DiskMidpoint.center_identity
#print axioms DiskMidpoint.enclosure
