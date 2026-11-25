# ARIAC: Expiry of one fault can lift another fault's disable flag

[Source, cut, proof and limitations](Compound_Health_Expiry.tex).

For ARIAC 2024.3.0, the test executes exact starts, expiry writes before the
first erase, and health message construction with stubs. It then feeds the
result to the pinned Python controller switcher with controlled service
outcomes. It stops each native expiry at the erase boundary; the replay is
not a full Gazebo execution or evidence that a physical arm moved.

Retrieve the two native files listed in [SOURCE.tsv](SOURCE.tsv) from the
pinned NIST commit, without changing their basenames. The script checks both
blob hashes before running their code.

    sh replay.sh /path/to/upstream | cmp results.txt -

Requires Python 3 and a C++17 compiler. The three Lean lemmas check the
active-occurrence rule, not the source behavior. The independent direct
interval-union specification agrees with the occurrence implementation.
