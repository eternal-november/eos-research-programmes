# Exact certified bracket for staggered density recovery

[Proof and scope](Staggered_Bracket.tex). For the five-robot prior fixture, the maximum span gain lies between 11087/2896 and 88697/23168, an interval of width 1/23168. The lower witness is continuous motion; a distinct outer model and checked exact dual bound all admissible continuous motions. The exact optimum is not claimed.

Run `node certificates.js | cmp expected_lower.txt -` and `python3 -B outer.py | cmp expected_upper.txt -`. Only the optional searches require NumPy and SciPy. No timing measurement or independent mission.
