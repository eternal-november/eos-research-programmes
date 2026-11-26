# Exact empirical risk with ordered timestamp uncertainty

The [ordered-clock proof](Ordered_Clock_Risk.tex) finds a tractable regime inside the [three-stream hardness result](../README.md). Keep the time-order bounds on successful records as well as failures. These bounds can be compiled into intervals for virtual failure slots, without identifying every real record pair. One matching then finds the worst failure count even with many streams, at a known or single common uncertain offset.

In the worked case, two streams can fail only in the same episode once all records are matched. Dropping the successful records would falsely permit two failed episodes. The direct comparison enumerates full joins and intersects the clock constraints for whole linkages, not for isolated pairs.

    python3 replay.py > actual.json
    diff -u results.json actual.json

The replay is synthetic. The acquisition model comes from the [two-stream study](../../README.md); it is not a claim about a measured clock or a real dataset.
