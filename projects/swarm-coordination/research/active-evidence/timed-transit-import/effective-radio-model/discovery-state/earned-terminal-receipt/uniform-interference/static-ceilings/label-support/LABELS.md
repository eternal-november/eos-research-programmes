# Static receipt-label support and reuse

[Scope, theorem and native discriminators](Receipt_Label_Support.tex).
Use the exact parent `static_ceilings.cpp` and pinned source manifests,
shim, extractors and cave graph importer. The self-contained backup
contains them. Run:

    sh run_labels.sh | cmp expected_labels.json -
