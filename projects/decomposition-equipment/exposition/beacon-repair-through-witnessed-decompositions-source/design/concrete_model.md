# A finite emergency-beacon assembly: proposed exact model

## Operational meaning and bounds
A robot salvages two identical active-high relay boards P and Q. They lie in a serial alarm-signal path. A shared mode switch g controls them through different wiring. The beacon also has an independent eligibility monitor S requiring mode 0. This is a Boolean, combinational model; it does not prove RF reliability, physical fail-safety, timing, or fault tolerance. In particular **do not call the two serial boards redundant paths**.

Types are Boolean signal, control, mode and eligibility ports; identity and complement maps between mode/control ports are explicitly declared. Every occurrence has a unique label. The trusted wiring diagram and the exhaustive component truth tables are the model data. One may motivate the tables as safe bench discoveries, but no theorem below infers stationarity or completeness of a physical device from finite samples.

Vertices of original whole G are N,P,Q,S. Its equations are

    n=1-g; p=a AND n; y=p AND g; ok=1-g.

N is the mode-to-control inverter. P,Q have the same component relation B(d,c)=d AND c. S is the eligibility monitor. External input is (a,g); external output is (y,ok). Edges retain source and target ports, including the single external mode source feeding N,Q,S. The mode source must not be silently copied into independently chosen existential variables.

Board truth table (d,c,y): (0,0,0),(0,1,0),(1,0,0),(1,1,1). N and S each map 0 to 1 and 1 to 0. Whole table (a,g,y,ok): (0,0,0,1),(1,0,0,1),(0,1,0,0),(1,1,0,0).

A fixed mode is mission-good iff for **both** a=0 and a=1 the output satisfies y=a and ok=1. This includes nontrivial alarm transmission, not merely silence preservation.

## Exact compatibility calculation
The identity-behavior certificate for either board requires control c=1. As an isolated test, each board has a nonempty set of suitable controls. The actual interface maps pull those certificates back to the common mode:

    P-good={g:1-g=1}={0}; Q-good={g:g=1}={1}; S-good={0}.

The global certificate space is their fibre product over the shared mode set, namely their intersection. It is empty. This is not evidence of a general compositionality failure; the correctly represented relational composition diagnoses it exactly. The invalid inference uses separate existential witnesses and drops the shared-mode equation.

## One replacement, occurrence-specific
Insert a declared inverter J on Q's control port, retaining the relay Q. The replacement module Qminus has external relation y=d AND (1-g). Its opening into J then Q is a genuine decomposition of that new module. Replacing Q by Qminus changes the whole from G to G_Q; it is **not** a same-whole refinement of G.

More generally, let epsilon_P and epsilon_Q indicate inserted inverters on the two board controls. Then

    c_P=(1-g) XOR epsilon_P; c_Q=g XOR epsilon_Q;
    y=a AND c_P AND c_Q; ok=1-g.

The four placement choices have signal-good mode sets:

| epsilon_P | epsilon_Q | signal-good modes | mission-good modes |
|---|---|---|---|
|0|0|empty|empty|
|0|1|{0}|{0}|
|1|0|{1}|empty|
|1|1|empty|empty|

Thus the correct occurrence is Q. An adapter attached to P, or a type-indexed rewrite that modifies both occurrences of B, fails. The good Q repair reuses P and S certificates; Q's old {1} predicate is replaced by the transported {0} predicate, and a new global certificate is built. It does not transport a nonexistent global certificate from G.

The actual transport is the pullback of B along (d,g) |-> (d,1-g). The graph-of-complement interface span is an isomorphism; its inverse is itself. This proves the claimed local adapter semantics without appealing to mere equality of component names.

## Competing decompositions, honestly scoped
The whole G admits two useful ordered partitions:

* physical boxes: X={N,P}, Y={Q,S};
* functional parts: C={N,S}, D={P,Q}.

The first makes boxes easy to inventory. The second separates mode control/eligibility from signal processing. The induced quotient wiring is acyclic in both cases. Retain all boundary incidences and the same whole G, not only the induced internal subgraphs.

Physical opening has atomic frontier (N,P,Q,S). Functional opening has frontier (N,S,P,Q). Their set-partition common refinement consists of singleton labelled occurrences. **They do not have the same ordered atomic frontier**, so crossing between them is not an I4 planar cut rotation and must not be asserted to be one. Each opening separately is a valid ordered graft/refinement. Comparing the two requires the following additional, proved finite labelled-coordinate bridge.

For each component let E_v be its complete local port-assignment relation. Let J be the subset of product E_N x E_P x E_Q x E_S satisfying all wire equations. Each partition's assembly witness is exactly a compatible tuple of its block assignments with those same retained equations. Flattening either such tuple gives J; splitting a member of J gives its inverse. The two maps are inverse bijections and preserve every external and internal labelled port value. Between the two flattened orders the explicit coordinate permutation is (N,P,Q,S) -> (N,S,P,Q). This is a result about these labelled assignments, not an extension of the original planar calculus by fiat.

This bridge changes which interface must be exposed: the functional signal module D needs two controls (n,g) constrained by n=1-g in C; the physical box split has a data seam p plus the shared external mode. The corresponding local summaries are not interchangeable if either omits the connecting equations.

## Whole witness versus observation repair
Let q:{0,1}->{*} forget the shared mode. The images q(P-good), q(Q-good), q(S-good) are all {*}, so gluing those images produces one spurious purported certificate. But q(P-good intersect Q-good intersect S-good) is empty. Consequently image-taking and this pullback do not commute.

The repair retains g and the actual control maps. It restores the equality between the global certificate space and the pullback of local certificate spaces. Relative to the declared test language containing P-good, Q-good, S-good and their conjunctions, this repair is minimal up to renaming: P-good separates 0 and 1, so every exact observation for that language must distinguish them. **Do not advertise this as minimal for the single original whole-mission query**: that query is constantly false and needs no distinguishing bit. Nor is this a claim of smallest hidden physical realization.

## Four machinery obligations actually exercised
1. Witnessed ordered graph decompositions and occurrence-indexed grafts retain G, port incidences, and P/Q distinction. The wrong type-indexed replacement is rejected by the finite mission table.
2. Interface restriction by actual port maps transports board predicates and relations. The joint pullback is empty before replacement and nonempty afterward; independent existential witnesses give the wrong answer.
3. Exact assembly of **full compatible assignment tuples**: the flatten/split bijections are proved for each partition and their explicitly reindexed comparison. Crossing is not passed off as a planar theorem instance.
4. Observation repair: the mode-forgetting image fails to preserve the shared-witness pullback; retaining a mode distinction restores it and is minimal for the fixed local-predicate language.

Standard relational/CSP natural join computes every finite compatibility verdict here. The contribution of the decomposition presentation is a verified record of which decomposition, occurrence, interface map, witness and observation permit that computation and its reuse. No novel general algorithm is claimed.

## Explicit operational assembly maps (separate from mission certificates)
The original hardware **does assemble and has four operational runs**, one for each (a,g). It is only the space of mission certificates that is empty. For G_Q there are likewise four runs; precisely two runs at the one eligible mode collectively witness the mission over both alarm inputs.

A whole run is the labelled record (a,g,n,p,y,ok) satisfying all four component equations. Write this set J_G. Its endpoint span is Bool^2 <- J_G -> Bool^2 with endpoints (a,g) and (y,ok). Each left-endpoint fibre has one element. Keep the entire J_G record when marking exactness; endpoint equality alone is insufficient to identify certificates in a more general nondeterministic example.

Physical assembly uses block records

    X=(a,g,n,p), n=1-g, p=a*n;
    Y=(p,g,y,ok), y=p*g, ok=1-g.

Take X fibre-product Y over their **ordered pair (p,g)**. Flatten to J_G by deleting only the repeated occurrences of p,g. Its inverse restricts the full record to X and Y. Functional assembly uses

    C=(g,n,ok), n=1-g, ok=1-g;
    D=(a,n,g,p,y), p=a*n, y=p*g.

Take C fibre-product D over **(n,g)**. Flatten/restrict are again inverse; a is supplied to D and ok is supplied by C. These explicit maps prove exact assembly and preserve intermediate p,n as well as external values. They also identify the common run set between the two different ordered partitions without declaring a planar interchange.

The same formulas after a Q adapter replace only y=p*g by y=p*(1-g). If its internal control value j is retained, also impose j=1-g and y=p*j; projection forgetting j is a bijection because j is uniquely determined. This is the special finite seam-lift calculation needed for exact opening of Qminus into inverter plus board.

The mission-witness set is

    M_G = {(g,(t_0,t_1)) : t_a in J_G has source (a,g),
                            output (a,1), for a=0,1}.

It is empty in G and singleton in G_Q. This displays the quantifier order exists g forall a explicitly. For this relay model the local identity certificates are not merely sufficient: mission correctness at a=1 forces both controls to be 1, and ok=1 forces g=0. Thus the local-good-set pullback exactly classifies M_G, rather than providing an incomplete sufficient test.

## Sequential span typing and the actual five-vertex repaired whole
For a literal sequential span path rather than an informal hypergraph join, include identity carry wires. Physical X has source (a,g), target (p,g); Y has source (p,g), target (y,ok). Functional Cbar has source (a,g), target (a,n,g,ok), apex (a,g,n,ok) satisfying n=ok=1-g. Functional Dbar has source (a,n,g,ok), target (y,ok), apex (a,n,g,ok,p,y) satisfying p=a*n,y=p*g, with ok carried unchanged. The path pullback matches the entire ordered seam tuple (a,n,g,ok). Deleting duplicate coordinates gives J_G bijectively. The Cbar and Dbar apices have 4 and 16 records, respectively; their path pullback has 4.

The actual repaired whole G5 has five labelled vertices N,P,J,Q,S, and runs (a,g,n,j,p,y,ok) with n=j=1-g,p=a*n,y=p*j,ok=1-g. Do not erase J merely because its value is determined: the exact witness retains its occurrence and its internal value. Two partitions of THIS SAME repaired whole are

    physical ({N,P},{J,Q,S});
    functional ({N,J,S},{P,Q}).

Within the physical second box, Qminus={J,Q} is first a named module, followed by S. Opening Qminus to its ordered children (J,Q) is a genuine occurrence-specific refinement and has a unique lift of its internal value j. The physical atomic frontier is (N,P,J,Q,S); the functional frontier is (N,J,S,P,Q). Compare them only through the specified labelled-record bijection, not a planar rotation.

Sequential physical spans are X:(a,g)->(p,g) as before, and Y5:(p,g)->(y,ok) with apex (p,g,j,y,ok), j=1-g,y=p*j,ok=1-g. Sequential functional C5:(a,g)->(a,n,j,g,ok) has apex (a,g,n,j,ok), n=j=ok=1-g; D5:(a,n,j,g,ok)->(y,ok) has apex (a,n,j,g,ok,p,y), p=a*n,y=p*j, and g,ok are carried. Their seam matches all five coordinates (a,n,j,g,ok). Both assembly path apices flatten bijectively to the full seven-coordinate run set of G5. This gives the positive same-whole root comparison with actual intermediate witnesses.

Conversely no claim is made that the replacement preserves the original whole output: at input (a,g)=(1,0), G outputs (0,1), while G5 outputs (1,1). A purported comparison over identity external endpoints that maps this old run to its new counterpart fails its root square. Local adapter transport does not waive that global check.

Finally the mode-erasure ghost concerns the declared **atomic local mission-certificate diagram** P-good,Q-good,S-good, not every possible observation quotient of either macro partition. For example forgetting only g at the physical X/Y seam while keeping the internal Q/S coupling need not create a spurious mission success. Keep the counterexample's precise diagram in the statement.
