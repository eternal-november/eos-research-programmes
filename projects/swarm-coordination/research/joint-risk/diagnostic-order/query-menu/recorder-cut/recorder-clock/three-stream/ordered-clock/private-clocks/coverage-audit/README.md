# Sound brackets for a private-clock failure cap

The [certificate proof](Certificates_For_Private_Clock_Audits.tex) gives an exact weighted oracle for each group sharing an unknown offset and a verifiable upper bound across private groups. A concrete compatible choice gives a lower bound. No true risk probability is inferred from fractional assignments used to find witnesses.

On the opposing-offset fixture, pooling the records gives an upper count of two. The certificate proves one. On the four-clause control, the real worst count is three and the fractional upper bound remains four. The exact-cap problem stays hard even though some caps can be certified cheaply.

Run with Python 3 and SciPy:

    python3 replay.py .. > actual.json
    diff -u results.json actual.json

The argument to the script is the [private-clocks directory](../README.md); its parent supplies the ordered-slot checker. The [linear-inequality separation result](https://www.zib.de/userpage/groetschel/pubnew/paper/groetschellovaszschrijver1981a.pdf) supports the theoretical oracle formulation. The executable uses explicit small LPs and checks their recovered rational certificates rather than trusting numerical optimality.
