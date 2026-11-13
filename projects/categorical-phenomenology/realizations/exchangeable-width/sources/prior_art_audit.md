# Positive realization: proof and source audit

Date: 3 November 2026.

## Reviewed result

The frozen manuscript `observable_exchangeable_width.tex`, SHA256 `6ab7011c6be13c529017e68660e5e2892fa85a749c81c94c502a1642f543399a`, was reviewed independently. This final hash includes the source-only clarification that the Mond–Smith–van Straten comparison is for rank-size factorizations. No mathematical blocker was found. This is a mathematical review, not formal verification or a priority determination.

The following steps were checked:

- Finite-alphabet exchangeability and constant finite Hankel rank give a unique finitely supported mixing measure. Constant support size and weak continuity give local continuous atom labels, positive continuous weights, and a finite component cover. Compactness gives uniform separation and a positive minimum weight.
- The finite-block classifiers are continuous on the frame cover. The stated Hoeffding exponent, choice of block length, and diagonal conditional-table bound of 6/7 are valid.
- The native factorization across two output blocks requires neither hidden stationarity nor reachability or minimality. Thus the lower bound applies to arbitrary outcome-labelled nonnegative kernels with a stochastic sum.
- The same-width truncation at decoder value 3/4, buffered decoder at 2/3, and denominator lower bound 3/28 produce a continuous exact stochastic split. The target-dependent tests and total-variation margin also prove the stated finite-horizon obstruction.
- The disjoint-support-to-split conversion changes the encoder before adding a continuous decoder. This correctly avoids a false assertion that every prescribed encoder has a continuous decoder on disappearing supports.
- The reconstructed kernels are normalized, have the exact all-word law, and admit both ordinary state-emission conventions at the same width. The signed extraction embeds the centered bundle in the fixed mass-zero hyperplane.
- The Moore-space conclusion separates three distinct counts: pointwise width three, global normalized signed width four, and global stochastic width five. Triviality of the full rank-three predictive bundle is compatible with nontriviality of its centered plane subbundle.

## Closest inspected sources

1. **Finesso and Prosdocimi, Stochastic Realization of Binary Exchangeable Processes (MTNS 2010), Theorem 3.** This directly characterizes finite binary iid mixtures through observable Hankel rank and gives a realization algorithm. Their Theorem 2 records Dharmadhikari's finite/countable exchangeable-HMM characterization. It is a close antecedent for observable reconstruction and pointwise width, not a statement of the continuous family criterion. Distinct Bernoulli parameters can be globally sorted, so the binary setting does not itself exhibit nontrivial component-label monodromy. [Primary proceedings PDF](https://www.conferences.hu/mtns2010/proceedings/Papers/330_039.pdf).

2. **Dharmadhikari, Exchangeable Processes which are Functions of Stationary Markov Chains (1964), 35:429–430.** Bibliography and content were corroborated through the preceding primary paper and the next one. Direct full-text retrieval was unavailable; do not claim that original proof was inspected. [DOI](https://doi.org/10.1214/aoms/1177703768).

3. **Prosdocimi and Finesso, Countable Partially Exchangeable Mixtures, Theorem 4.2 and Lemma 6.10.** Theorem 4.2 characterizes countable iid mixtures of Polish-valued exchangeable sequences as HMMs with recurrent underlying chains. Its proof replaces the transition matrix pointwise by its Cesàro limit, with identical-row blocks for recurrence classes. This is not a continuous choice of recurrence classes or a continuous fixed-width family theorem. The reviewed manuscript's two-finite-block argument avoids needing such a choice. [Primary text, arXiv version 2](https://arxiv.org/html/1306.5631v2).

4. **Mond, Smith and van Straten, Stochastic factorizations, sandwiched simplices and the topology of the space of explanations (2003), Theorem 2.4 and Corollary 2.5.** The theorem identifies rank-size stochastic factorizations of a fixed finite matrix with sandwiched-simplex spaces, equivariantly under permutation. The paper also studies quotient topology. Thus topology and label symmetry of positive explanation spaces are established themes. It does not state the all-word arbitrary-HMM extraction and exact continuous width criterion reviewed here. [DOI](https://doi.org/10.1098/rspa.2003.1150); [inspected author-hosted primary PDF](https://download.uni-mainz.de/mathematik/Algebraische%20Geometrie/DvS-Publikationen/30.Stochastic%20factorizations,%20sandwiched%20simplices%20and%20the%20topology%20of%20the%20space%20of%20explanations%20-%202003.pdf).

5. **Babson and Kozlov, Complexes of graph homomorphisms.** The homotopy equivalence of Hom(K_p,K_k) with a wedge of (k−p)-spheres is classical. Its connectivity, not a new Hom-complex computation, supplies the general dimension bound and five-state upper bound. [Primary paper](https://arxiv.org/abs/math/0310056).

6. **Monràs and Winter, Quantum learning of classical stochastic processes: The Completely-Positive Realization Problem, Theorem 6.** This gives the classical polyhedral-cone criterion in stochastic-process language and discusses access/observation reductions. It concerns pointwise existence, not a continuous exact-state-budget selection theorem. The longstanding Heller criterion should not be promoted, without additional proof, to “k native states iff at most k extreme rays in a reduced-space cone.” A higher-dimensional nonminimal realization can involve an accessible-subspace intersection before taking the observable quotient. [Primary paper](https://arxiv.org/html/1412.3634v1).

7. **Knudsen and Weinberger, Analog category and complexity.** Continuously varying finite-support probability measures and sectional-category obstructions are relevant adjacent topology. Their probability measures lie in fibers of a map; the reviewed disjoint-support space consists instead of several disjoint distributions on fixed native labels. The invariants should not be identified without an explicit comparison. Correct publication: SIAM Journal on Applied Algebra and Geometry 8 (2024), 713–732, [DOI](https://doi.org/10.1137/24M1635004), [primary preprint](https://arxiv.org/abs/2401.15667). Their AGT 26 (2026), 1585–1596 paper is the distinct *On the analog category of finite groups*.

8. **Shitov, A universality theorem for nonnegative matrix factorizations.** The universality of fixed-size nonnegative-factorization spaces provides a caution against treating unrestricted positive-realization fibers as automatically contractible or locally trivial. It is not by itself an HMM family theorem. [Primary paper](https://arxiv.org/abs/1606.09068).

## Scope of the potentially new bridge

The search did not locate a prior statement of the exact equivalence between continuous arbitrary native HMMs of width k and equivariant maps from the observable component-frame cover to Hom(K_p,K_k), including the same-width finite-horizon robust extraction. Absence from this search is not proof of novelty. The manuscript correctly makes no priority claim. A specialist review should compare the bridge with statistical sufficiency, stochastic splitting, parameterized positive realization, and topology of factorization spaces.

The result is restricted to held finite iid mixtures derived from all-word exchangeability and constant rank on a compact base. It is not a positive-realization solution for arbitrary dynamics, nor a certificate of exchangeability or uniform approximation from finitely many parameter samples.

