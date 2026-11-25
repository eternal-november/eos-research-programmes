# A failed attempt can change the next send

Two SubT fixture histories agree on every one-send test. Their first failed attempt spends transmit allowance in only one history; the following retry distinguishes them. The proof gives the exact payload/capacity boundary and states what the controller would need to learn.

Run `sh replay.sh | diff -u replay.txt -` after materializing the original six sources and the #437 shim. See SOURCE.tsv and the verifier. All originals, notices and exact replay are in the Space archive. The renamed original shim `main` is not called. No external network or field test is performed.
