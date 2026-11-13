# The maximal interface doctrine supported by the circuit semantics

## Plain-language abstract

Not every mathematical change of interface can be carried out by a device. But this does not force us to abandon the equipment structure. There is an exact permitted class: an interface map is eligible when the hardware can both apply it and realize its inverse-image choices with the correct execution records. For these maps, restrictions of any executable component are executable by a concrete three-stage construction. Conversely, no larger class of interface maps can have all equipment restrictions without demanding those same two capabilities. This is a standard categorical principle applied to the operational model, not a claim to invent equipment theory. It identifies precisely where that machinery is valid, while leaving finite hardware budgets and circuit synthesis as separate questions.

## 1. One fixed operational setting

Fix an opaque immutable snapshot X and the nonadaptive eager circuit grammar of `Finite_Acquisition_Circuits_and_Exact_Lifting.md`, §§1–3. Every actual boundary carries X; ordinary gates see only declared readable payloads. Installed sensor invocations read only their fixed supported source coordinates, all execute once, and distinct invocations retain distinct event records. There is no implicit adaptive sensor selection or discarded multiplicity.

Let C=FinSet/X. A horizontal span in C has finite event carrier M over X, source and target maps over X, and thus the same snapshot at both endpoints. Its composition is pullback over the complete intermediate boundary. Choose the collection O of nominal interface objects admitted by the circuit language, including X×A with its specified readable capability type. Equal underlying finite carriers do not identify capability types. Formally one may use separately tagged copies of their carriers. Horizontal apex sets need not themselves be circuit interface types: they are semantic execution carriers in C.

Let H(A,B) be the **endpointwise replete semantic image** of the unbounded finite circuit language: it contains the span denotation of every permitted finite circuit A->B and every span isomorphic to such a denotation over the fixed endpoints A,B. Repleteness concerns apex isomorphisms with endpoints fixed; it does not authorize arbitrary changes of endpoint capability types.

The language has identity wire circuits and is closed under permitted sequential composition. The normalization lemma proves that sequential composition stays in the nonadaptive snapshot grammar when the complete shared snapshot interface is retained. Therefore H contains all horizontal identities and is closed under horizontal composition, up to the canonical span isomorphisms. The word unbounded means finitely many acquisitions per circuit with no one uniform slot cap; it does not mean infinite executions. Hardware sharing must remain an explicit shared acquisition vertex, and independent calls retain separate records.

This is the positive theorem's concrete closure input. A k-slot hardware fibre by itself need not satisfy it and is not used in place of H.

## 2. Permitted vertical maps

For an actual function f:A->B over X between the chosen interface objects, write

    f_* = (A <-id- A -f-> B),
    f^* = (B <-f- A -id-> A).

The first span applies f deterministically. The second has exactly one execution for each preimage choice a of the input b=f(a), and none when b has no preimage. A circuit merely having the same support relation as f^* does not suffice: its execution multiplicities must also be correct.

Define

    V_H(A,B) = {f over X : f_* in H(A,B) and f^* in H(B,A)}.

Membership can be certified by two actual finite circuits and endpoint-preserving event bijections. The second certificate is a genuine implementation of inverse-image choice, not an assertion that a set-theoretic inverse exists. No hidden event tags may be invented to obtain it.

### Proposition 1. V_H is a category.

Identity maps qualify because both associated spans are the unit. If f:A->B and g:B->D qualify, then

    (g f)_* ≅ f_* ; g_*,
    (g f)^* ≅ g^* ; f^*.

The composite witness in the first expression is uniquely determined by a. In the second it is a pair (b,a) with g(b)=d and f(a)=b, hence again uniquely determined by a with g(f(a))=d. Thus these are actual span isomorphisms, not support-only identities. Closure and repleteness of H prove the result. The given circuits compose to certificates for the new map. ∎

## 3. Exact restriction compiler

Let E=(B<-s-M-t->C) be in H(B,C). For f:A->B and g:D->C in V_H, form the circuit composite

    f_* ; E ; g^*.

Its event carrier is canonically

    R = {(a,m,d): f(a)=s(m), t(m)=g(d)},

with boundary a on the left and d on the right. This is precisely the cartesian restriction E(f,g), retaining every actual E event and every matching inverse-image choice. The concrete compiler consists of a supplied forward-f circuit, the E circuit, and a supplied converse-g circuit. It does not freely add an inverse-image selector.

The comparison cell E(f,g)->E sends (a,m,d) to m and has vertical boundary f,g. Its cartesian property is inherited directly from the pullback: given a compatible event map n:N->M with endpoint maps a:N->A,d:N->D, the unique lift is z |-> (a(z),n(z),d(z)). This formula is over X because every interface and every map preserves the snapshot.

### Proposition 2. Equipment of permitted interfaces.

Take objects O; vertical maps V_H; horizontal spans H; and **all** ambient span cells whose vertical boundaries lie in V_H and whose horizontal endpoints lie in H. Then these data form a pseudo double category with horizontal units and all cartesian restrictions, hence a virtual equipment (indeed a span-style equipment). Its cartesian restrictions are implemented by the compiler above.

Proof. Vertical closure is Proposition 1. Horizontal closure, units, associators, and unitors follow from the circuit closure and endpointwise repleteness. Every cell is an endpoint-commuting map of event carriers, and all horizontal/vertical compositions and interchange are inherited from the ambient span double category. The restriction composite lies in H, and the preceding universal property remains true in the substructure because its cell sets contain all compatible ambient witness maps. Thus the required cartesian cells exist. ∎

These **cells are semantic certificates**, not necessarily executable physical transformations between circuits. The theorem would not follow for an arbitrarily selected smaller class of executable cell transformations. Likewise it gives a semantic equipment with circuit certificates; it does not claim to classify circuit syntax, compilation traces, or circuit-layout isomorphisms.

## 4. Exact maximality

### Proposition 3. V_H is the largest vertical base supporting every restriction with the same H.

Suppose V is any category of actual functions over X on O such that the horizontal class is H and restrictions of its units along every map in V exist as the ambient cartesian restrictions. For f:A->B in V, restrict the unit span U_B along (f,id_B). Its span is isomorphic to f_*. Restrict U_B along (id_B,f). Its span is isomorphic to f^*. Both must lie in H. Thus f belongs to V_H, proving V subset V_H. Proposition 2 proves that V_H itself works. ∎

The qualification 'ambient cartesian restrictions' is substantive: this is maximality for the faithful span semantics, not a claim about an unrelated double category that calls different cells cartesian. If the proposed subequipment embeds with the usual restrictions preserved, the qualification holds automatically.

The constructions f_*, f^* are the standard companion/conjoint mechanism. The result here instantiates it with exact finite sensor-execution semantics and supplies the interface-capability test. It is not claimed to be a new general theorem about equipments.

## 5. Consequences and limits

* There is a constructive positive doctrine, not merely a warning that arbitrary restrictions fail: eligible interface maps have actual forward and reverse circuit certificates, and restrictions compile by composition.
* Unbounded semantic H is composition-closed. A fixed slot budget need not be composition-closed, so finite-budget reconstruction remains a capability-lifting problem inside this equipment, not itself an equipment closure claim.
* The fixed-allocation synthesis theorem decides membership under the supplied finite hardware bounds. It does not establish a decision procedure for unrestricted membership in H or V_H. Exhaustive circuit enumeration may find certificates but is not by itself a terminating negative test.
* For a deterministic-only grammar with no actual branching executions, a noninjective map cannot have a realized converse span, since some source input would require more than one execution. If partial execution is also unavailable, a nonsurjective map cannot have a converse, since some input would require none. Thus in a total deterministic-only grammar V_H can contain only bijections, and even a bijection must have both directions computable by the allowed gates. Genuine sensor choices or explicit permitted partial operations can enlarge V_H, but not by declaration alone.
* Inverse-image choice is stronger than having the right relation. A proposed inverse circuit with extra hidden executions fails the witness-bijection certificate even if its returned values are correct.
* Snapshot-preserving restrictions and sequential substitution here are coherent via ordinary span pullback associators. This does not assert automatic reconstruction under arbitrary refinement, arbitrary changes of the physical sensor catalogue, or changes that discard the common snapshot and later reuse it.

## 6. A noninvertible permitted map with a concrete certificate

Take the one-point snapshot and a permitted binary-outcome sensor primitive

    1 <-!- {0,1} -id-> {0,1}.

Its two executions return different measured values; they are not invisible labels attached to an unrelated operation. Suppose discarding a readable bit is also permitted. The noninjective function f:{0,1}->1 then has f_* implemented by discard and f^* implemented by this sensor, so f belongs to V_H. Restricting the right boundary of a circuit ending at 1 along f introduces one actual binary measurement after each old execution; the resulting event carrier has precisely two events per old event. The restriction compiler produces exactly this apparatus and these records.

Removing the binary sensor from an otherwise total deterministic-only apparatus removes the converse certificate and hence removes f from the permitted vertical base. This makes the capability criterion operationally nonvacuous: the same underlying finite function can be a valid equipment interface change for one physical library and unavailable for another.

## Standard categorical source

Michael Shulman, *Framed bicategories and monoidal fibrations*, Theory and Applications of Categories 20 (2008), 650–738. [Paper](https://www2.math.ethz.ch/EMIS/journals/TAC/volumes/20/18/20-18.pdf), [arXiv record](https://arxiv.org/abs/0706.1286). Appendix Theorem A.2 characterizes framed bicategories by existence of companions and conjoints for vertical arrows; the span example and its base changes appear in §4.15. The present note's general equipment mechanism is an instance of that established theory. Its operational content is the selection of the exact circuit-realizable graph/converse pairs, witness-sensitive compilation, and separation from bounded hardware synthesis.
