# Reconstruction, example, and literature review

Reviewed: `periodic_phase_observable_theorem.tex`

- Initial full-read SHA256: `7aef1706ec629fd9df6bd5348014a95ddd1b90750bfefe10b5b29c2bb836866a`
- Reviewed revision after corrections: `100d35a3ebcf50387081feb77843b56f49f589108eb43385bbdc21a541eabf52`

## Outcome

No substantive mathematical blocker found in the reconstruction, stationary-block proposition, or temporal Moore-space example. This is a targeted human-readable proof and source audit, not formal verification or a priority certificate.

The stationary-block proof correctly uses the law of the shifted empirical limit, rather than incorrectly asserting conditional independence of adjacent shifted blocks. Splitting into even and odd subsequences supplies the required conditional strong law. Iterating F forces product atoms, and strict one-symbol stationarity supplies rotation invariance. The nonstationary case correctly uses the full rotation closure, not just initial directing support.

For the Moore example, affine independence makes V full row rank, so symmetry of V^T Pi V would imply symmetry of the three-cycle permutation matrix. The temporal nonexchangeability argument is therefore valid. The nonzero order-three Euler class and vanishing mod-two obstruction support the stated centered-plane and rank-three bundle behavior. The graph quotient obstruction at four positive states and Hom-complex connectivity at five states match the construction.

## Corrections requested and confirmed

1. The native stochastic initial row now explicitly must be nonnegative. This is essential for extraction of stochastic Q from arbitrary competitors.
2. St(r,s) now explicitly denotes nonnegative row-stochastic matrices.
3. The quantitative robustness corollary now assumes p >= 2, avoiding its formerly undefined separation constant at p = 1.
4. The empirical boundary now states that exact infinite symmetry, fixed period, and constant rank are structural inputs. A single mixture trajectory does not generally recover all weights/components, and continuity on an arbitrary compact base gives no quantitative finite-sampling uniform guarantee.

## Literature assessment

The revised text properly separates classical representation/reconstruction from the proposed continuous minimum-width theorem. Graham's [2009 manuscript](https://arxiv.org/pdf/0902.0539), Theorem 3, directly treats conditional independence of classes given their directing laws and credits the all-infinite case to Aldous. It is a different paper from Graham's correctly described 2008 Journal of Applied Probability article.

The [Vandermeulen–Scott manuscript](https://arxiv.org/pdf/1607.00071), Theorems 4.1 and 4.3, supports the grouped-mixture comparison. The draft correctly distinguishes initial block-component count from full phase count and does not claim these finite reconstruction thresholds as new.

[Monras–Winter](https://arxiv.org/html/1412.3634), Theorem 6, indeed states the classical pointed-polyhedral-cone criterion. Mond–Smith–van Straten, Theorem 2.4, concerns the equivariant correspondence between rank-size stochastic factorizations and sandwiched simplices. The [Babson–Kozlov abstract](https://arxiv.org/abs/math/0310056) explicitly states the wedge-of-(n-m)-spheres result needed for Hom(K3,K5) simple connectivity. These sources establish important ingredients, not the entire parameterized native-width theorem.

The source-comparison section makes no unsupported priority claim. The potentially distinguishing content is the observable reconstruction of full phases, same-width time averaging, continuous extraction/repair for arbitrary native competitors, and consequent global width criterion. A specialist priority search remains necessary before asserting that combination is novel.

## Final frozen-source check

Final SHA256 inspected: `1098741a19d81f52f1371eed6b0a391b9f65e3302f7ba11e0409452b5af1eab3`.

The added classical dimensional corollary is correct under its stated assumptions. For a finite q-dimensional CW base, the (q-1)-connectivity of D(p,p+q) permits extending the associated-bundle section over all q-cells. The zero-dimensional case is immediate. At width p, D(p,p) consists of permutation matrices, so its section is exactly a global labeling of the phase cover. On a general compact Hausdorff base, a finite trivializing cover with subordinate partition of unity gives finitely many chart-specific slots and a continuous disjoint-support map; the earlier buffered repair supplies a decoder. The new paragraph appropriately identifies these deductions as applications of classical topology. The additional lmodern package changes presentation only.

Final scoped outcome: no outstanding reconstruction, stationary-block, temporal-example, citation, novelty-wording, or empirical-scope blocker found in this exact source revision. The earlier caveat remains: this is not formal verification or an exhaustive priority certification.
