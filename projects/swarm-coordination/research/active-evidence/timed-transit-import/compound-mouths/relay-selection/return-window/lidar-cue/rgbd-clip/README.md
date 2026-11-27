# A depth-image subscription can change the point stream

[Technical note](Subscriber_Dependent_Clipping.tex). CoSTAR's specified
ordinary camera far clip is 300 m and depth-image far clip is 10 m. With
a fresh finite 37 m sample supplied to the selected pinned RGB-D source
slice, the same point consumer sees finite XYZ without a depth-image
connection and infinite XYZ with one. Near and exact 10 m controls,
both infinity signs and per-frame subscription changes were checked.

Run `sh run.sh | cmp expected.txt -` with Python 3 and GCC in a directory
containing the inputs listed in `INPUTS.tsv`. The five fields of that
manifest are local filename, GitHub repository, immutable revision,
source path, and Git blob SHA-1. The [Space
checkpoint](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80)
also has a source-complete offline archive. The replay's selected native
branches receive authored buffers and connection booleans. It does not
run an Ignition bridge or test which connection regime actually occurs,
the stock deployed build, a rendered cave observation, or local
availability before a movement decision.

[Depth bridge retirement](bridge-retirement/README.md): a registered bridge
can disappear as a process yet still affect the depth clamp numerically.
The named topic/node retirement and the process-only callback differ.
