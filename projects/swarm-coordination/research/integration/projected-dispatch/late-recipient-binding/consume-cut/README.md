# The consuming broker joins the handoff receipt and the real debit window

[Pins, proof and comparison](Consume_Cut_Authority.tex). Jointly
requiring a qualified handoff arrival and room on the actual local
rows avoids predicting the exact remote cut, but may delay old work.
A stale positive check can attempt a receive-rejected operation, burn
sender capacity, and lose an independently owed report.

Materialize SOURCE.tsv, then:

    sh replay.sh /path/to/upstream | cmp expected.json -

Requires Python 3.10+, NumPy, C++17, git. Consume_Window.lean covers
the integer deadline and overflow kernels. Bridge and source
failure schedules are authored. No independent or field result.
