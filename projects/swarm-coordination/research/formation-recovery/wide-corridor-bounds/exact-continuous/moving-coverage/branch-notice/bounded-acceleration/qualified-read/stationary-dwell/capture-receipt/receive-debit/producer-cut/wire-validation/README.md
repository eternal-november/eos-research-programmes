# Density metadata versus finite point evidence

[Dense_Is_Not_Evidence.tex](Dense_Is_Not_Evidence.tex) tests the selected
sensor, bridge, and PCL finite-filter contract. The point flag can say
all data are finite when the payload contains infinity. An explicitly
conservative filter retains only finite points and their original indices;
it cannot restore an observation lost at the producer.

Place the parent study's INPUTS.tsv, extract.py, rgbd_probe.cpp and their
exact native input aliases in the parent directory. Place WIRE_INPUTS.tsv
aliases beside these files. Run sh run-wire.sh and compare stdout to
expected.txt. The Space backup contains both sets of inputs.
