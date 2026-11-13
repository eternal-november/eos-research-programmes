# Non group full unital compression and the branching boundary

## A genuine noninjective full unital monoid map

The injectivity conclusion in the branching theorem depends on branching. It is false for general monoid maps on a genuinely nonbranching graph family, even when every vertex-free unit and every positive tree is retained.

For n>=1 let L_n^1 consist of 1 and n nonunits c_1,...,c_n, with 1 the identity and

    c_i z = c_i     for every z in L_n^1.

These are actual finite transformation monoids: take the identity and n distinct constant functions on an (n+1)-point set, with ordinary composition f g=f after g. The constants multiply as a left-zero semigroup and are distinct from the identity.

Let f:{1,...,n}->{1,...,m} be a surjection, with n>=m>=1. The map

    h(1)=1,                 h(c_i)=d_(f(i))

is a surjective unital monoid homomorphism and h^{-1}(1)={1}. It is proper whenever n>m.

Take the original graph calculus with maximum graph size N=1. Retain every full profile, arbitrary empty gaps, all allowed old interfaces, every finite tree, every vertex-free identity, and unbounded unary syntax. Each nonempty operation has exactly one active input. Each active cut therefore has exactly one active root-to-leaf path, although the full tree may have arbitrarily many empty branches and vertices. This is a parameterized C5 subfamily varying its finite witness palette, not a positive-only cut grammar.

## Exact path lifting with a coherent choice

The product of a nonempty path of L_n^1-labels is its first nonunit if there is one, and 1 otherwise. Fix a section s:L_m^1->L_n^1 of h that sends 1 to 1 and selects one preimage of each nonunit. Every such section is a unital monoid homomorphism, because both nonunit multiplications are left-zero.

Given a prescribed target path (a_1,...,a_k) and concrete source x with h(x)=a_1...a_k:

* If all a_i are 1, identity reflection forces x=1; lift every factor to 1.
* Otherwise let j be the first nonunit index. Then h(x)=a_j and x is a nonunit. Lift a_j to x, every target unit to 1, and every later nonunit a_i to s(a_i).

The lifted product is exactly x and each factor has the prescribed image. For k=0, the target empty path is the vertex-free identity; h(x)=1 forces x=1, and its empty record is the unique lift. Empty graph positions carry no coefficients. This proves full source-fixed lifting for every actual tree in the N=1 family, not only for bounded chains.

The chosen lifting commutes with path contraction. A contracted interval before the first nonunit contains only units. An interval containing the first nonunit has concrete product x. An interval after it has product s of the corresponding target product because s is a homomorphism. These are exactly the three cases of the lifting rule on the contracted path. Conversely refining a target factor and applying the same rule at its already chosen concrete source reproduces the expanded path: a factor carrying x propagates x to the first nonunit in its refinement, whereas a factor carrying s(a) propagates s(a) there. Unit refinements carry only units. Thus insertion, contraction and the empty-unit case are coherent for this fixed section. Full retained records are compared entrywise; contraction may intentionally forget factors and is not asserted injective.

For two channels use h squared and s squared. The first nonunit positions may differ between the channels; apply the construction independently in each channel. The resulting pair still labels one actual path and preserves every factor. Channel swap commutes with this coordinatewise construction.

## Proper minimal decoder

On P[(L_n^1)^2] with N=1, observe the exact old record and the first-channel h-value at its active input, permit swap, all contexts and all actual cuts including vertex-free units. The encoder is h squared on the sole active coefficient and is unique at rank zero. It is a monoid homomorphism and has the exact all-tree lifting proved above, so it induces an actual quotient witness calculus with exact joint cut relations.

The decoder reads the first target coordinate. Equality of encodings implies equality of every generated mixed experiment by composition compatibility and exact cuts. Different encodings are distinguished by the initial readout or that readout after swap. Therefore this is the minimal reachable exact-may realization for the predeclared language.

Its concrete label carrier has (n+1)^2 states and its minimum quotient has (m+1)^2 states over each rank-one old record. For n=4,m=2 it gives a genuine 25-to-9 compressed full-unital decoder. Letting n=2m and m grow yields an unbounded finite-palette family. Full profiles are not merged, and all exact old data and empty occurrence positions remain to be encoded.

## Why this cannot be exported as a uniform branching quotient

Choose distinct c_i,c_j with h(c_i)=h(c_j)=d. In a realizable two-descendant group use concrete source tuple (c_i,c_j), target outer coefficient d and target child coefficients (1,1). Each individual descendant has a lift: its parent would be c_i or c_j respectively. Since h reflects 1, both concrete child coefficients must be 1. The single shared parent would therefore have to equal both c_i and c_j, which is impossible.

Thus a noninjective full-unital map can pass every unary factorization and every vertex-free test while failing a realizable branching cut. This is precisely why the shared-parent intersection is necessary and why a unary positive example cannot certify the principal N>=2 uniform coefficient theorem. The rank-sensitive group quotient in the companion I2 repair supplies a separate proper full-profile branching realization, but it is not a uniform coefficient map.
