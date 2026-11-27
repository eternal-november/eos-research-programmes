# Effective radio model check for the held-in cave benchmark

[Technical note](Requested_And_Effective_Radio_Model.tex).
Seven pinned inputs exercise selected SubT C++ load/selection and RF
functions. The DOT and SDF come from the already viewed cave development
asset; the small rounded model-origin lookup and tested relay row are
staged fixture inputs, not the stock LUT or relay selection. No native
packet send or full simulator is claimed.

After staging the original inputs named in SOURCE.tsv under INPUTS:

    sh run.sh INPUTS | cmp expected.json -

The Space backup includes those exact inputs under up/.
