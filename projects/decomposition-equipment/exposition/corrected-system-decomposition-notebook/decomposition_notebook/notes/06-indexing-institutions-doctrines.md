# 06 — Fibrations, institutions, and doctrines: three different law/parameter interfaces

**Origin:** chat L723–759, L800–823, L882–910, L477–514. **Status:** corrected typing; extensions identified.

## Fibrations: varying *families of systems* over a base

A fibration \(p:\mathcal E\to\mathcal B\) has a base of contexts/parameters/signatures and fibers \(\mathcal E_b\) of objects over \(b\). Along \(u:b\to b'\), a chosen cartesian lifting gives **contravariant reindexing**

\[
u^*:\mathcal E_{b'}\longrightarrow\mathcal E_b.
\]

It is incorrect to interpret this as arbitrary forward transport of one system to any new law setting. Reindexing generally *pulls back* a system already living over the target of \(u\). Forward transport is extra, often an opfibration or suitable adjoint, and does not always exist. Different choices of cleavages affect strictness of functoriality.

**A use case:** model families indexed by admissible parameter domains, sensor configurations, or signatures, where changing the indexing context must induce coherent restriction of models.

## Institutions: separate formal laws from models satisfying them

An institution has signature category \(\mathbf{Sig}\), a sentence functor \(\operatorname{Sen}:\mathbf{Sig}\to\mathbf{Set}\), a contravariant model assignment \(\operatorname{Mod}:\mathbf{Sig}^{op}\to\mathbf{Cat}\), and satisfaction relations. For \(\sigma:\Sigma\to\Sigma'\),

\[
M'\models_{\Sigma'}\operatorname{Sen}(\sigma)(\varphi)
\iff
\operatorname{Mod}(\sigma)(M')\models_{\Sigma}\varphi.
\]

This says that satisfaction is respected by translation of **signatures**, not that physical laws are true in nature or that every model admits a numerical solution. Source: [Goguen on institutions](https://cseweb.ucsd.edu/~goguen/projs/inst.html); [institution survey](https://iep.utm.edu/insti-th/).

**A use case:** exchanging law signatures or theories while making changes to vocabulary, equations, and satisfaction explicit.

## Doctrines: predicate operations indexed by contexts

A common categorical doctrine is a functor of predicates \(P:\mathcal C^{op}\to\mathbf{Poset}\), often with fibers carrying logical structure and reindexing by substitution. Quantifiers, equality, and connectives require extra adjoints/laws. This is **not** synonymous with an institution: one starts from indexed predicates and proof-relevant structure, the other from signatures, sentences, models, and satisfaction. They can be connected, but not by relabeling one as the other.

## Limits of the proposed combination

An institution can say that \(M\) satisfies equations; a fibration can reindex models with their parameters; an actegory can encode some genuine operator action on systems. The three do not automatically compose into a single theory. Before integrating them, specify whether the base indexes *syntax*, *physical parameters*, *geometric carriers*, or *assumptions about observations*. A parameter value such as mass \(m\) does not necessarily define a morphism to another value \(m'\), and changing it may change the topology of the solution set.

**Related notes:** [03](03-types-of-physical-law.md), [04](04-actegories.md), [20](20-architecture-and-proof-obligations.md).
