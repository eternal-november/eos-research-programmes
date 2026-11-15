# Native synchronization and selective adjoints

Scoped categorical tools for retaining native comparisons while admitting selected synchronization adjoints. These results do not complete the feedback/concurrency construction.

## General categorical results

1. [Singleton module actions](Singleton_Module_Actions_and_Lax_Adjoints.tex) retain old module maps and native cells fully faithfully, preserve specified incoming lax bilimits, and admit right adjoints in a lax-transformation enlargement. Column residual existence is verified for the local presheaf base.
2. [Adjoint output comparisons](Adjoint_Output_Comparison_Synchronization.tex) construct native synchronization from an adjoint to the output comparison, without requiring that comparison to be an equivalence. Projection cells can remain noninvertible.
3. [Selective assembly mates](Selective_Adjoints_and_Assembly_Mates.tex) derive coherent assembly of the selected synchronized transitions from pre-synchronization squares; invertible mates give a local sufficient condition for pseudo assembly.
4. [Product-indexed parallel](Product_Indexed_Parallel_and_Lax_Cones.tex) derives compatibility of old directed parallel with enriched normal-lax cone presentations indexed independently. Shared indexing is a separate restriction.
5. [Native bicolimit normalization](Native_Bicolimit_Normalization_and_Parallel.tex) proves separated right bi-Kan pairing under terminal-bicolimit normalization, retaining pseudonatural transformations and modifications. It does not substitute Set-level connectivity for native normalization.

## Boundary and ordinary realizations

- [Pure exactness versus adjoint admission](Pure_Exactness_and_Adjoint_Admission_Boundary.tex) shows why admitting every new lax arrow while keeping every completed module pure is incompatible with the specified unital pure-layer-exact parallel doctrine. This is not an obstruction to the original pure interface alone.
- [Connected commas](Connected_Commas_and_Selective_Parallel.tex) give the exact Set-valued criterion for separated right-Kan pairing, with noncocontinuous fixed-point examples.
- [Shared boundaries from connected lifts](Shared_Boundaries_from_Connected_Lifts.tex) derive that ordinary criterion from independent component hypotheses over a classical sifted base, including nonrepresentable normal-lax Prof transitions and coherent finite shared restriction.

## Remaining gap

The native bicolimit criterion and the ordinary connected-lift criterion are different. Neither automatically extends the original effectful directed parallel operation to arbitrary new residual arrows. Deriving the requisite native normalization, mixed assembly and feedback compatibility from the original independent context/content data, while preserving the actual admitted pure tags, remains open. External Cartesian pairing is not itself the effectful operation.

These notes build on [relative enriched completion](../relative-synchronization-completion/README.md) and [bicategorical synchronization](../bicategorical-synchronization/README.md). They use established module, adjunction, Kan-extension and bicolimit machinery with explicit scoped proofs; no novelty or full-unifier claim is made.

## Verification

The manuscripts contain written mathematical proofs, not proof-assistant certification. `MANIFEST.json` records SHA-256 hashes of the source and guide. TeX compilation is not required to read the sources and was not used as proof evidence.
