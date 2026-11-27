# Qualifying the native clip guard at a frame cut

[Proof and audit](Guard_Cut_Qualification.tex). This is a proposed
publisher-side diagnostic, not a change to stock Gazebo. A serial source
can apply a typed register and named end around a frame and still have
the same mode at two polling cuts. The exact possible frame modes are
computable from the two polls and the admitted transition slots. If at
most H guard flips fit between the polls, an exact zero-flip check
needs floor(H/2)+1 extra tag values when the guard bit is already
returned. The count is for this header-only certificate, not for
detecting a real obstacle or extending the mission.

The [Space archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80)
includes all pinned #740 dependencies. Run
`sh run_guard.sh | cmp expected_guard.txt -`. Alternatively supply those
files plus the four source files here in one directory; extraction
checks the exact existing hashes. Lean 4.36.0 + Mathlib checks the
arithmetic and finite-cardinality kernel in `GuardCut.lean`.
