# A shared admission kernel for warehouse and radio effects

**I1 development only.** This runs one admission interpreter over joined
events from two pinned replay plants. It neither closes I1/I2 nor sets
aside an independent acceptance mission. The independently written
factored check gets the same results with the same evidence.

See [the contract and results for this model](Shared_Admission_Core.tex)
and the [development freeze](FREEZE.txt). The two native components
are the ordered warehouse source producer (#588) and the timed radio
source producer (#589). The bridge from bay clearance to channel
availability is authored; it is not something either plant proved.

## Replay

Python 3.10+, NumPy and a C++17 compiler. Use the exact paths below
from a checkout of this repository; their relevant blobs are pinned in
`COMPONENTS.tsv`. The upstream input tree has the same layout as in
the [radio producer's source manifest](../subt-relay-debit/pending-scope/timed-source-producer/SOURCE.tsv),
including the pinned warehouse simulation files.

    RESEARCH=/path/to/eos-research-programmes/projects/swarm-coordination/research
    sh replay.sh /path/to/upstream \
        "$RESEARCH/multi-owner-coordination/named-withdrawal/in-flight/source-producer" \
        "$RESEARCH/multi-owner-coordination/named-withdrawal" \
        "$RESEARCH/multi-owner-coordination/named-withdrawal/in-flight" \
        "$RESEARCH/integration/subt-relay-debit/pending-scope/timed-source-producer" \
        | cmp expected.json -

`core.py` interprets typed facts, rolling capacity, deadlines and
exactly-once effects. `replay.py` translates plants, compares to direct
rules, and executes five selected decisions against the radio plant in
addition to the standalone native controls. Neither the bridge nor the
shared variable used in the correlation control was inferred from traces.

## Action-dependent follow-up

[Two-cut reactive diagnostic](reactive-observation/README.md): two probes can produce the same timely evidence yet differ in whether the old clearance still meets its deadline. The same checker also distinguishes state-dependent silence from an unqualified loss model. The direct adaptive comparison ties.

## Native authority follow-up

[Live reservation replacement](live-authority/README.md): the same native range can refer to a newly granted path, while an earlier reservation receipt and the actual crossing clearance remain separate. Five in-process controls also distinguish inline qualification from a remote snapshot. The matched direct check ties.
