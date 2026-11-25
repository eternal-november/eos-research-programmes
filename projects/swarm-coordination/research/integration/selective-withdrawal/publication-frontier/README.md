# Old movement at the publication cut

Read [the argument](Publication_Frontier.tex). Run `python3 check_frontier.py`
for the standalone model and `python3 replay.py` for the exact selected Java
bodies against an in-memory sink; use OpenJDK 21. The latter needs the five
hash-pinned files listed in the script, from openTCS
`742b0e6df9ccbabc660e585a85e55d585c0642fc` under
`opentcs-commadapter-vda5050/src/main/java/org/opentcs/commadapter/vehicle/vda5050/v2_0`
(the mapper and edge/node helpers are in `ordermapping/`). The Space archive
contains the pinned source and both expected outputs. This is an offline test.
