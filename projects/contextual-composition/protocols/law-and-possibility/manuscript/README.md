# Zero-weight branches in finite probabilistic protocols

Working manuscript draft. The draft gives an exact marked-span criterion
for sound contextual replacement: a relation-supported probability coupling
plus one-sided coverage of declared candidate possibilities, including
zero-weight rows. It compares finite typed protocols under stated ownership,
normalization, and occurrence-composition conditions. See the
[longer technical treatment](../Law_and_Possibility_Repair_for_Dependent_Protocols.tex)
for additional results and context.

Build the reading copy with two runs of
`pdflatex -interaction=nonstopmode -halt-on-error Zero_Weight_Branches.tex`.
The generated PDF is not tracked in this draft directory.

The [finite rational checker](checker/README.md) consumes supplied legal
raw-row pairs. From `checker/`, run `python3 -B -m unittest -v`.
The checker tests local certificates over finite rational data. It does
not type-check the protocol language, certify contextual closure, or
constitute Lean verification.
