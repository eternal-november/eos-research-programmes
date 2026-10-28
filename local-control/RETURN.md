# Raw exposure covers and the remaining return induction

Status: proved raw-history containment and a specified assembly obligation, not a proved full return theorem. This is a reuse/generalization of recurring-control/RENEWAL R4 and local-control/INFORMATION's window accounting to concurrent episodes and whole consumer windows. The old aligned schedule, effective-outage count and return deadline do not transfer. Independent review confirmed the raw containment argument and identified the initial-debt and host/bank distinctions retained below.

## Raw history before any recovery claim

A domain is a physical/code/input reach domain in the admitted source map, not a packet identity. Let A(t−) be direct external access immediately before the events at time t. Record every acquisition with its actual start and release, including events at the same physical boundary. Bound direct occupancy at every intervening event state by c; release and reacquisition ordering must not hide a temporary extra occupant. Let Acq[a,b] be the set of domains acquired in the closed interval[a,b]. Its cardinality is at most the number of acquisition events, even when a domain is acquired repeatedly. Suppose that count is at most floor(σ+λ(b−a)). This closed-endpoint convention includes a burst at one instant. Retained ordinary actions, code corruption, learned handles and launched effects are not new acquisitions.

Let P be the persistent physical footprint. For a proposed return budget H>0 and t≥0 put a_t=max(0,t−H) and define the **raw** set

    E_H(t) = P ∪ A(a_t−) ∪ Acq[a_t,t] ∪ (D_0 if t<H else empty).

D_0 is explicit initial released-but-unreturned debt, not arbitrary incoming records or inactive images that the entry procedure still has to handle. INSTANCE's current numerical candidate sets D_0 empty and places active-code/private-state initial defects in P∪A(0−). Initial unknown observations are handled by evidence-invalid startup and actual acquisition; declaring them all trustworthy or all Byzantine would be a different argument.

The definition of E_H(t) makes no assertion about actual cleanliness. Without a recovery operation, old bad code can continue after its domain has disappeared from this bookkeeping set. The executable records precisely that countermodel. No program reads E_H, P, actual fault identity or a cure flag.

For a consumer interval I=[s,s+W], define

    F_H(I) = P ∪ A(max(0,s−H)−) ∪ Acq[max(0,s−H),s+W] ∪ (D_0 if s<H else empty).

Then union_{u∈I} E_H(u) ⊆ F_H(I). Proof: each persistent member is already included. A domain directly held at an intermediate lower boundary either was held at the earlier lower boundary or was acquired between them. An acquisition in an intermediate rolling window is in the larger interval. Initial debt appearing at any u≥s implies s<H. This order argument holds for real event times as well as discrete ones; it does not assume aligned controller clocks. Return.lean checks the integer event-carrier instance and the clipped-boundary step. The finite checker includes same-boundary releases/acquisitions and zero-duration recorded episodes.

Consequently

    |F_H(I)| ≤ p+c+floor(σ+λ(H+W)) + (|D_0| if s<H else 0).

This is a derived bound on raw history only. Actual observation support is the union of the affected physical slots under one compatible incidence/history pair, with all continuing reach/descendants included. Actual actuator support and image/reference support use their own projections of that SAME set/history. A maximum per compatible layout is permitted; unioning mutually exclusive layouts or granting independent budgets per module is not. A global domain cover implies each local intersection bound; separate region-only bounds need not bound a neighborhood straddling a border.

## What must turn bookkeeping into actual support

The intended joint invariant has three distinct parts: source domains outside E_H provide their specified code/reference/execution/path/effect interfaces; every actually intact consumer retains the fixed factual-response duty even if its domain lies inside E_H because an input apparatus was reached; and the world/service/resource predicates hold. The second part cannot be inferred from the first. In particular, a faithfully misled primary-frame recipient does not become a Byzantine decision maker merely because the world-output calculation conservatively charges its host.

There are three substantive obligations for a finite-prefix/first-failure closure:

1. **Entry and ordinary preservation.** The actual commissioning/initial-acquisition procedure supplies a safe base while information is pending. On an already valid prefix, nominal data flow preserves code/references and bounded private state, actual old/new output actions remain compatible, and the physical force/write/record graph prevents uncharged spread. A candidate bay filled by a bad producer is not automatically another corrupted running host, but the actual selection/custody/start proof must justify that distinction. Raw acquisitions enter E_H immediately; malformed input and legitimate partial repair states are not relabeled acquisitions.
2. **Actual old-debt clearance.** For a nonpersistent domain released at r and not reacquired during the relevant interval, the mechanism reaches useful return before r+H from every source-reachable interrupted state. Return includes correct installed C and initialized/private execution, current evidence/report behavior, actual fields/access, closure of every retained path, and bounded old effects. A raw release changes none of those by itself. Continuously occupied and persistently defective domains remain covered exceptions; the theorem does not promise their individual cure.
3. **Common quantitative continuation.** The proof of that return uses only the initialized prefix, compatible local intervals and the same raw cover, plus actual affordable work/energy/supply and physical evolution. For each consumed interval its coherent-cover bound must fit the component's margin. A full attempt, an entire wait-plus-retry history and a short local job are different intervals. Strict deadline slack is needed before a domain ages out; a completed image or a pointwise good-count premise is not sufficient.

Once these are proved for the actual source, the closure argument excludes a first unexplained failure: ordinary steps cannot cause it, a new acquisition is charged, and a domain leaving the raw cover has already completed actual return strictly before that boundary. Plant and stock continuation must be included in the same prefix argument so that unavailable power or unsafe evolution is not assumed away. For hybrid time, finite-rate event/non-Zeno and continuous safety arguments are separate consumers; an integer proof alone does not license them. These source premises remain open until CYCLE, ACQUISITION, the complete P(d), hybrid and resource refinements discharge them. This paragraph is not a substitute proof of any of those services.

## Host continuity does not supply a fixed bank cohort

The raw cover can leave34 usable hosts throughout an attempt without leaving any one bank per host powered throughout it. Ready intervals[20k,20k+30] cover every ten-unit job but no forty-unit attempt. Therefore CLAMP/OPERATIONS' fixed participating-bank hypotheses cannot follow directly from the host cover or CONTINUITY's interval theorem.

The needed semantic handoff retains actual physical candidates and identities across producer retirement; nominal reincarnations write only expected values on their own private leads; new banks reconstruct a compatible physical-stage action and common frozen-image selection through complete local jobs; and compatible new force is applied before old force disappears. Reset, stale rank/choice state, old commands and report/driver entry are part of this invariant. CYCLE supplies a proposed stage-specific argument; its actual ready intervals and full programmed realization are still separate suppliers. This is why a time-cover theorem is useful but does not itself complete the recursive construction.

The earlier illustrative p=1,c=2,σ=3,λ=3/(10C),H=2C and W≈0.83C yield six domains over H+W. Requiring a coherent set over2H instead yields seven. The physical margin then fails: seven adverse hosts can supply31.8 against stiction28. The appropriate response is to prove the actual sequence of source-local handoffs/windows or recompute the architecture/budget, not silently use the six-domain result over the longer interval.

## Checks and result boundary

return_model reproduces the five selected Lean declarations, checks the raw inclusion over finite episode histories at every relevant boundary and intervening cell, and retains countermodels for bookkeeping without recovery, uncharged initial debt, endpoint omission and the fixed-bank inference. The general raw proof is the order argument above, not inference from enumeration. The complete source return, no-spread, conduct, stock and mission theorem is deliberately not recorded as passed.
