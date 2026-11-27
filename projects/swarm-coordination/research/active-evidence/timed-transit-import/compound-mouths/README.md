# Cave mouths, trigger volumes and a two-edge trapping cut

Held-in I2 preflight on the already-viewed Cave Circuit 01. See [technical note](Cave_Mouths_And_Two_Cuts.tex).
This is source-derived topology and an explicit two-edge deletion control,
not a replay of vehicle motion, rock collision, live packet delivery,
or an independently selected mission.

To reproduce, place the files named in column 1 of `SOURCE.tsv` beside
`replay.mjs`, using the repository, commit and path in columns 2–4.
The script checks byte identity against the Git blob in column 5 before
reading any numerical input. Run:

    node replay.mjs | cmp - expected.json

The event and RF sources are checked evidence for the interface
interpretation, not executed code in this replay. The numerical part
reimplements a selected connector predicate and checks the reconstructed
edges against the published graph before reporting cut witnesses.
