# The producer-side cut for a qualified formation notice

[Producer_Cut.tex](Producer_Cut.tex) joins selected CoSTAR/Gazebo RGB-D
processing with the earlier SubT radio and exact formation model. The far
cue is lost in the stock point output while the required depth image is
emitted. An authorized pre-clipping read from the same frame can preserve
one bound bit without suppressing that image. A latest-only raw read does
not supply the original capture if another view overwrites it.

Materialize the aliases in INPUTS.tsv, LIFECYCLE_INPUTS.tsv, AUX_INPUTS.tsv,
and the inherited radio/INPUTS.tsv. Put the compiler(s) on PATH; run
sh run.sh and compare stdout to expected.json. The Space package carries
all the exact source inputs. The selected post-render stage starts from
supplied texture data, not a rendered environment or hardware measurement.
