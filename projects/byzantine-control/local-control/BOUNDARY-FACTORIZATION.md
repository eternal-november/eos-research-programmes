# Boundary factorization and hidden-current obstructions

Status: proved finite-dimensional linear factorization criterion and induced-norm bounds; exact rational checks and concrete obstruction witnesses are supplied. The linear algebra is reconstructed established mathematics, not a novelty claim. Its use here is to generate a common source-to-interface obligation instead of adding a separate exception for each electrical component. Physical realization, source admission and useful return are different certificates.

## The judgment and its kernel

Fix a source mode, actual port identities and one allowed physical fault support. Let r in R^n be represented physical flows, u in R^m unrepresented flows and j in R^k explicitly retained residual inputs. These are actual flows, not unverified reports. Suppose the actual cut equations are

    A_r*r + A_u*u = j.

Let the source quantity whose absolute components matter be

    e = T_r*r + T_u*u + T_j*j.

The exposure is ||e||_1. Its rows name the actual distinct contacts/branches; replacing separate rows by their signed sum changes the judgment. Likewise, an actual current not present in the cut equation is not made zero by omitting its column.

The interface forgets u while retaining (r,j). The question is exact: does every compatible hidden completion produce the same e? The declared linear kernel admits every real u satisfying the equations. It does not impose passivity, component ratings, nonnegative-current cones, finite stored energy, fault probability or a temporal evolution. Those additional constraints can justify a different, weaker bound; they are not silently used in the exact theorem.

## Exact cut-kernel theorem

For finite real matrices, the following are equivalent:

1. For each feasible (r,j), all hidden completions u give the same e.
2. ker(A_u) is contained in ker(T_u).
3. There is a matrix D with T_u = D*A_u.

The feasible set is nonempty at least at(r,j,u)=(0,0,0). Necessity of2 follows by comparing u=0 and any v in ker(A_u) at that same retained interface. Conversely, two completions differ by such a v, so2 makes their exposures equal. For2⇒3, define D on im(A_u) by D(A_u*u)=T_u*u. Kernel inclusion makes that map well-defined and linear; extend it from a basis of im(A_u) to the finite ambient space. The reverse implication is immediate.

For any such D, every source flow satisfying the cut equations obeys the explicit reconstruction

    e = B*r + C*j,
    B = T_r - D*A_r,   C = T_j + D.

Thus the diagram commutes: extracting the actual exposure from a concrete flow equals first forgetting u and then applying this reconstruction. The proof is an exact quotient/factorization law for the stated query, not a complete abstract-control theorem. D need not be unique outside feasible retained inputs. Different extensions can give different conservative norm bounds; selecting the smallest such bound is a separate optimization problem.

This result is also a zero-residual impossibility criterion for the unrestricted linear class. If kernel inclusion fails, choose v with A_u*v=0 and T_u*v!=0. Then every scaled v has the same retained interface(0,0), while its exposure is unbounded. No finite homogeneous upper bound based only on that interface can hold. Whether that vector is an admitted physical trajectory still requires its constitutive/source witness. Passivity or a charged finite-state bound may eliminate or limit it; an algebraic kernel vector alone is not a universal physical impossibility theorem.

## Quantitative transport to a controller interface

The induced one-norm is the maximum absolute column sum. Hence

    ||e||_1 <= kappa*||r||_1 + eta*||j||_1,
    kappa=||B||_(1→1),   eta=||C||_(1→1).

For a positive diagonal weight matrix W, use Q=||W*r||_1 and kappa=||B*W^(-1)||_(1→1). This keeps real current ratings and different units explicit. The column norm is sharp over unrestricted retained vectors for the chosen B or C: an appropriately signed basis vector attains the largest column sum. It need not be the optimal constant on the smaller feasible physical behavior set or among all extensions D.

If the source also proves Q(t)<=rho*Q(s)+v*(t-s), and an actually delivered low reading y supplies Q(s)<=y+epsilon, then

    ||e(t)||_1 <= kappa*(rho*(y+epsilon)+v*(t-s)) + eta*J(t),

where J bounds the real residual. Oldest sample ancestry and the entire command/withdrawal/effect tail belong in t-s. This implication does not supply any of those premises: a calibrated head, ordinary code, delivery age and actual withdrawal are separate source/controller refinements. The represented r are not thirteen independent observations merely because a provider rereads them thirteen times.

The law may be indexed by an unobserved fault history h. It is enough that every allowed h has some D_h with common bounds kappa,eta and common physical meanings for r,j,e. The proof may select D_h; the controller uses only the uniform bound and its local observations. This does not grant it a fault-identification oracle. All h must be projections of the same actual joint fault history, with their true multiplicities; separately choosing a convenient fault budget for each component is invalid.

Sequential exact factorizations compose by substitution. Wiring open components can additionally hide ports that were previously retained. In that case the actual combined conservation equations and newly hidden columns must be formed before applying the kernel criterion. Two locally adequate summaries do not automatically cover a new circulating mode created by their interconnection. Feedback also requires nonempty compatible dynamics and any consumed dissipativity or continuation result; matrix reconstruction alone supplies neither.

## The actual failure cases become instances

For one passive electrode with one conducting neck r and one reference-capacitor branch u, charge conservation gives r+u=0. The actual exposure vector is(r,u). Reconstruction gives(r,-r), with kappa=2. The capacitor's displacement current has not been ignored or falsely described as crossing an inductor.

If a reference dielectric defect creates a separate retained conducting flow s, the equation is r+s+u=0 and the actual vector is(r,s,u). The coefficient remains2 for Q=|r|+|s|. A residual charge input j that is itself a contact exposure contributes twice its absolute bound: once directly and once through charge balance. Its omission is a source error, not an improvement in the inequality.

With two unmeasured reference branches, r+u1+u2=0 has hidden vector(u1,u2)=(1,-1). If both branches' absolute currents matter, that vector is in ker(A_u) but not ker(T_u). Net charge is insufficient. The same witness applies to two separate physical necks observed only through their net current. This is why adding a parallel reference path or declaring two contacts equipotential did not automatically preserve the earlier interface.

For22 actual electrodes, let N map each represented strand to its actual electrode incidence. The ordinary single-neck/reference construction has exposure vector(Nr,-Nr), so kappa=2 when each column has exactly one unit incidence. A route that enters one contact and leaves another has two incidences and gives factor4 if counted once in Q. The checker exhibits that changed coefficient. The physical map must retain multiplicity; assigning one logical route label does not make its second contact disappear.

The active final-cell DC calculation is another instance. Let u be one uncontrolled final current, n the net cut flow and g the bounded other outputs. Conservation gives u=n-sum(g). Therefore

    |u|+sum|g| <= |n|+2*sum|g|.

The exact matrix columns have coefficients1 for n and2 for each g, giving BARRIERS' B_DC=m0+m1+2*C_out once the actual net-cut and good-output bounds are supplied. If two uncontrolled active final ports are retained only by their sum, the hidden vector(1,-1) reappears. A proof that works for one port cannot be extended by changing a number in the prose. Alternatively, a passive flow-cone/topology argument may rule out the cycle; that is a different supplied restriction and must be checked under the actual faults.

## Bounded and nonlinear alternatives

Kernel inclusion is not necessary for every useful conservative abstraction. For r+u1+u2=0 retain the circulation distinction d=u1-u2. Then

    E=|r|+|u1|+|u2| = |r|+max(|r|,|d|)
      <=2|r|+|d|.

A proved bound on d gives a real residual; observing d gives a finer interface. Neither is supplied by naming a hidden mode. Finite energy alone need not bound instantaneous current: a fixed-energy capacitor discharged through successively smaller resistance has unbounded initial current. A state/energy residual therefore needs the actual constitutive path and its temporal bound.

More generally, define the actual fiber F(z) of source states/flows consistent with an available interface z, including physical laws and admitted faults. A sound upper interface U requires E(f)<=U(z) for every f in F(z). Linear reconstruction is the special case where the query is constant on fibers. Nonlinear constitutive inequalities, passive cones, capacity cuts and dissipativity certificates can establish a finite supremum without exact reconstruction. Empty fibers do not provide a nonblocking source or a successful controller; a bound that always rejects does not supply the required useful-service result.

If a new component introduces a kernel mode, the justified choices are to retain/measure that mode, prove its actual bounded contribution, constrain the source by a warranted physical law, or change the specification explicitly. The choice is governed by this obstruction and the required source scope, not by an obligation to keep inventing hardware.

## Selected realization and exact outstanding suppliers

The detailed CONDUIT-GRAPH candidate is retained at commit373a15a in the conduit research branch. It presents the single-electrode and one-active-port premises using separately reached reference elements, a retained G charge state, insulating control links and distinct electrical cells. Its fixed neck and reference-defect routes have explicit incidence consumers. That is a conditional graph candidate, not a universal electrical equivalence or an admitted physical implementation. Its complete flow-label, reference, energy and fault maps still require their own refinement if that electrical realization is claimed.

The independently reproduced a0dafce program component already supplies ordinary finite code for B_DC and Q_Z, the real low-reading/current-head relation at its stated scope, source-compatible primary-input sensitivity, and the inclusive30/reject31 guard. The matrix law explains its factor2 and the final-output coefficient2. It does not establish useful braking or renewal.

In particular, source energy composition needs the actual stores and port currents. A brake-port capacitor can make terminal/diode current differ from the internal strand current; then assigning a damping term B*Sign(i_strand) from the wrong port is an invalid refinement. The coupled-storage certificate must establish its own well-posed dynamics, storage balance and finite entry into the actual safe/authority-inert region. A useful energy sublevel must be proved to imply the needed physical output/launch restrictions; small energy is not automatically clean code, erased history, or absence of replayable authority. Re-energization and cold formation retain their separate ordinary protocol obligations.

A typed hybrid/port source may serve as the primary mathematical source when its constitutive and transition laws are declared inputs of the theorem. A detailed electrical implementation is then an optional further refinement unless the exported claim specifically consumes it. Conversely, a primitive that already promises truthful aggregate evidence, permission, timely successful recovery or a clean origin has encoded achieved service and cannot be smuggled in as a raw law. This factorization theorem helps check a proposed interface; it does not itself settle that assumption-admissibility judgment.

## Warranted connections to the concurrent-activity drafts

The primary checkout's concurrent-activity TODO/README and three requested notes were read as draft evidence, without editing that checkout. Their exact residual construction says a local contract must work against every counterpart allowed by the supplied contract, rather than some counterpart in an existential projection. That is the right quantifier for a bound over all hidden completions. Their local-selection criterion distinguishes a decoder on observation cells from a pointwise omniscient witness; here the controller must use the same uniform certificate in indistinguishable histories. Their assembly note distinguishes positive capability witnesses from upper bounds on all prohibited behavior, and keeps shared resources, accumulated effects and higher-arity compatibility separate.

These elementary statements were checked directly against the current counterexamples: the net-current quotient loses a law-relevant fiber; two individually satisfactory reference components can create an unbounded hidden circulation when assembled; source/capacitor and controller contracts may each have a good implementation but use different currents or different fault supports; and a static safe-current calculation supplies neither a causal measurement nor a useful return. The drafts therefore supply warranted organizing structures, not a completed categorical synthesis theorem or evidence that every advertised concern is relevant here. The full source/interface/controller assembly remains a separate obligation.

[✓, abstract-level comparison] Van der Schaft and Maschke's [Port-Hamiltonian systems on graphs](https://arxiv.org/abs/1107.2006) explicitly treats open-graph flow/effort incidence, storage/dissipation relations and interconnection. This is the relevant established composition setting. The present finite matrix proof is given in full and does not rely on an unchecked imported theorem for Byzantine faults, causal inference or recovery.

## Reproduction and claim boundary

Run `C:\Python312\python.exe -B boundary_factorization_model.py --check`. Exact rational elimination checks all729 two-by-two/row-map pairs with entries in{-1,0,1}; concrete checks cover nominal and shorted references, residual charge, multi-neck/parallel-reference obstructions, one/two active final ports, physical incidence multiplicity, norm coefficients and bounded circulation. The general result rests on the written linear proof; finite tests check its encoding and named countercases. Independent review checked that proof, its unrestricted-linear scope and the quantitative transport, and reproduced the immutable worker record; coordinator reproduction also passed. No whole-source or program-completion claim is made by this artifact.
