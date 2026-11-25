# Retirement and amendment squares

What_A_Retirement_Square_Must_Preserve.tex gives the scope, sharp
counterexamples, the residual-profile proof and the pricing obstruction.

Run python3 -B on signatures.py, occupancy-square.py and fee.py; compare
replay.txt, occupancy.txt and fee.txt. The raw product check runs without
external libraries. To also replay the public offline HoldSpec comparator,
pass the path to the pinned checkout to product-controls.py and compare
product.txt. No networked payment APIs are used. RetirementSquares.lean
was checked with Lean 4.35.0 and Mathlib.
