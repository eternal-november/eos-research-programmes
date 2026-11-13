# Constructions, enrichments and applications

> Exploratory orientation. Established constructions, conditional integrations and proposed extensions are distinguished in the discussion. Application possibilities are not implementation or theorem-completion claims.

The easiest way to understand these constructions is to ask: What kind of computational system can be represented, and what new capability does its composition law provide?

For example, \\(\mathrm{Para}\\) represents parameterized computation, which gives the compositional architecture of neural networks. Adding reverse differentiation gives backpropagation. Adding probability gives stochastic neural networks. Adding feedback gives recurrent computation.

The distinction is between representing a system and providing algorithms for operating on it. \\(\mathrm{Para}\\) does not itself implement gradient descent, and a probabilistic contextad would not automatically implement Bayesian inference.

There are two groups below: the constructions established in the paper, and the additional structures proposed in the previous answer.

## 1. Constructions already available

These are established mathematical constructions, several of which the paper unifies through \\(\mathrm{Ctx}\\) or its dual \\(\mathrm{Cnt}\\).&#x20;

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org\&sz=32)

arXiv+2



| Construction                        | What it supports                                                                          | Concrete applications                                                                                                    |
| ----------------------------------- | ----------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| Para                                | Composable functions with explicit parameters                                             | Neural network architectures, trainable controllers, parameterized simulations, differentiable programming architectures |
| Para + lenses                       | Parameterized forward computation with backward information flow                          | Backpropagation, gradient-based learning, optimizer interfaces, bidirectional controllers                                |
| CoKleisli (comonads)                | Computations that read or depend on structured context                                    | Cellular automata, image filters using neighborhoods, environment-dependent computation, contextual dataflow             |
| Span                                | Computations or relationships with explicit intermediate witnesses                        | Database joins, graph paths, nondeterministic transition systems, proof-relevant relations                               |
| Partial-map construction            | Functions defined only when particular conditions hold                                    | Partial functions, guarded computation, program failure, restricted-domain transformations                               |
| Ctx (contextads)                    | Computations whose required contexts can depend on inputs and earlier contexts            | Dependent parameterization, capability-sensitive programs, typed pipelines with input-dependent requirements             |
| Kleisli (monads)                    | Computations producing effects rather than just ordinary outputs                          | Exceptions, logging, mutable state, nondeterminism, probability, effectful programming                                   |
| Cnt (contentads)                    | Effectful computations with explicitly structured, potentially dependent produced content | Graded effects, output annotations, effect accumulation, structured generation                                           |
| Cospan                              | Systems composed by identifying or gluing interfaces                                      | Circuit wiring, network assembly, open graphs, interconnected physical systems                                           |
| Monoidal/cartesian structure on Ctx | Parallel composition, products, and compatible structural operations                      | Parallel model execution, multi-component systems, circuit composition, structured workflow assembly                     |

A few distinctions are especially useful.

Span versus Cospan: a span describes what mediates a relationship between two objects. A cospan describes how objects attach to a common system. A database join is a good span intuition; connecting two electrical circuits along a shared terminal is a good cospan intuition.

Comonad versus Monad: in their familiar computational presentations, a comonad supplies context to be consumed, whereas a monad represents effects produced by computation. The paper's interesting twist is that some traditionally monadic effects—such as state, writer output, and optional results—can also be represented through dependent context grades. Those representations are related but are not literally the same data structure.

Ctx versus Para: Para has a global parameter category. In Ctx, the admissible context \\(P\\) can depend on the object \\(A\\), and later contexts can depend on earlier extensions. That is why Ctx can represent partial maps and spans as well as ordinary parameterization.

One should also separate plain network wiring from physical behavior: a cospan describes how components are connected; a decorated cospan or an appropriate semantic construction is needed to represent component dynamics or electrical laws.

## 2. Proposed enrichments: what they would actually enable

These are the additions discussed previously. Some ingredients already exist independently in category theory, but their integration with general contextads is proposed or conditional.

| Enrichment                                    | What it would support                                                   | Concrete applications                                                                                                   | Status                                           |
| --------------------------------------------- | ----------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| 1. Stochastic contextads                      | Explicit randomness, latent variables, probabilistic composition        | Probabilistic programming, Bayesian networks, stochastic neural networks, Monte Carlo simulation, randomized algorithms | Concrete finite construction proposed            |
| 2. Differential contextads                    | Differentiation through input-dependent context and parameter spaces    | Constrained optimization, geometric deep learning, differentiable controllers, models with dependent parameter bundles  | Research extension                               |
| 3. Relations (Rel)                            | Relationships where only existence matters, not individual witnesses    | Database queries, constraint satisfaction, nondeterministic specifications, symbolic model checking                     | Established construction; integration proposed   |
| 4. Corelations (Corel)                        | Connectivity with internal implementation details forgotten             | Circuit topology, network connectivity, wiring equivalence, black-box interconnection                                   | Established construction; integration proposed   |
| 5. Logical doctrines / predicate transformers | Reasoning about what computations guarantee, require, or make reachable | Formal verification, refinement types, weakest-precondition semantics, probabilistic program verification               | Conditional extension                            |
| 6. Mixed Ctx–Cnt constructions                | Computations that simultaneously consume context and produce effects    | Stateful transactions, sensor–actuator systems, effectful neural networks, read/write pipelines                         | Research direction in paper                      |
| 7. Traced / feedback contextads               | Feedback loops, iteration, recursive interconnection                    | Recurrent neural networks, feedback control, cyclic circuits, iterative algorithms, dynamical systems                   | Requires suitable trace or fixed-point structure |
| 8. Commuting / independent contexts           | Safely exchanging or parallelizing context-dependent operations         | Concurrent programming, parallel computation, separation logic, independent distributed operations                      | Research extension                               |
| 9. Composed contextads                        | Combining several kinds of contextual requirements into one semantics   | Randomness + state, permissions + partiality, resources + uncertainty                                                   | Requires distributive laws                       |
| 10. Recognition theorems                      | Determining whether a given semantics can be represented as Ctx         | Classifying effect systems, reconstructing program semantics, comparing categorical models                              | Foundational research direction                  |

The key additions are easier to understand by examining what new behavior each permits.

### Stochastic contextads: a neural network that explicitly uses randomness

Ordinary Para describes a model

\\[ f:X\times P\to Y. \\]

A stochastic version could describe

\\[ f:X\times P\times \Omega\to Y, \\]

where \\(\Omega\\) represents randomness.

This can express dropout, random initialization, stochastic policies, latent-variable generative models, and Monte Carlo estimators. With dependent contexts, the permitted randomness or its distribution could also depend on the input or intermediate state.

The key extra capability is composition that tracks how random choices are generated and propagated. Ordinary stochastic kernels forget those implementation details.

Bayesian conditioning is a further operation, not an automatic consequence of introducing randomness.

### Differential contextads: gradients through dependent contexts

Para plus ordinary reverse differentiation already supports the structural foundations of neural network training.

A differential contextad would investigate the more general case where the legal parameter space varies with context.

For instance, a controller may have parameters constrained by the current physical operating regime, or a geometric model may use parameters living in fibres of a bundle rather than in one global Euclidean space.

The goal would be to differentiate while respecting those dependencies.

Main limitation: differentiation must commute with the relevant reindexing operations. Arbitrary input-dependent parameter types do not automatically support smooth differentiation.

### Relations and corelations: forgetting different kinds of information

These two are extremely useful, but for different reasons.

Span → Relation

A span remembers how two things are related, through its apex \\(S\\). A relation only records whether they are related.

Example: a database join that reports whether a match exists versus one that retains all matching records.

Cospan → Corelation

A cospan retains an intermediate system used to join interfaces. A corelation retains the induced boundary connectivity, discarding unnecessary internal nodes.

Example: two wiring diagrams with different internal junction layouts but identical connectivity among their external terminals.

These give two forms of abstraction: forget witnesses of a relationship, or forget internal details of an interconnection.

### Logical doctrines: programs that carry specifications

Consider a partial program

\\[ f:X\rightharpoonup Y. \\]

Without logical enrichment, this represents a computation that may be undefined.

With a suitable predicate-transformer structure, one can express properties such as:

- Every input satisfying precondition \\(P\\) produces an output satisfying \\(Q\\).
- Some execution can reach a target state.
- The probability of failure is below a chosen bound.
- The expected cost of the computation is below a budget.

The connection to neural networks would be verification of compositional neural systems, rather than training. Examples include formally specified input domains, output constraints, and safety conditions.

### Mixed contextads–contentads: reading and writing in one computation

Think of a controller that reads sensors, computes an action, updates a state, and emits a log.

A contextad can express the requirements under which the computation takes place. A contentad can express the effects or additional information it produces.

The mixed construction would make both sides compose coherently.

This matters for systems that cannot be adequately described as either purely context-reading or purely effect-producing: stateful agents, database transactions, closed-loop controllers, and programs that consume capabilities while producing events.

The missing ingredient is an interchange/distributive law specifying how reading context interacts with producing content.

### Traces and feedback: making cycles compositional

Ordinary Para models a feedforward layer

\\[ f:X\times P\to Y. \\]

A feedback extension would aim to support internal state circulated around a loop:

\\[ f:X\times P\times S\to Y\times S. \\]

That is the interface of a stateful transition, but turning the internal \\(S\\)-interface into categorical feedback requires additional trace, iteration, or fixed-point structure.

This connects directly to recurrent neural networks, state-space models, dynamical systems, and feedback control.

There is a useful distinction: state threading is not the same as tracing. A recurrent network unrolled through time can be described using sequential composition; a categorical trace supplies an abstract operation for closing feedback wires. Arbitrary feedback is not defined in every category.

### Independent and composed contexts: parallelism versus layering

These are two different extensions.

Independent contexts ask when contextual operations can be reordered without changing their behavior. That is relevant to concurrent programs, race-free computation, and disjoint resource usage.

Composed contextads ask when different context mechanisms can be combined into a single coherent one. For example, a probabilistic program may also require permissions and have partial behavior.

The order may matter: sampling a value and then potentially failing is not necessarily equivalent to first restricting the possible outcomes and then sampling. A composite contextad must encode the actual interaction law rather than assume that effects commute.

### Recognition theorems: understanding what the framework can express

A recognition theorem would not add an operation such as differentiation or randomness.

Instead, it would answer:

> Given a category or double category of computations, can its arrows be factored into acquiring some context and then performing an ordinary map, in a way compatible with composition?

That is useful for reconstructing semantics, establishing equivalences between computational models, and determining which programming-language effects admit contextad presentations.

The negative result about continuation monads in the previous answer belongs here: it identifies a boundary of certain discrete context presentations, rather than supplying an additional computational capability.

## 3. What combinations would support

Taking neural networks as the reference point:

| Desired system                                                            | Candidate structural ingredients                                       |
| ------------------------------------------------------------------------- | ---------------------------------------------------------------------- |
| Feedforward neural network                                                | Para                                                                   |
| Trainable neural network                                                  | Para + reverse differentiation / lenses                                |
| Bayesian or stochastic neural network                                     | Para + stochastic semantics + suitable inference operations            |
| Recurrent neural network                                                  | Para + state threading; trace if abstract feedback closure is required |
| Neural controller interacting with an environment                         | Para + lenses + state/effect semantics                                 |
| Verified neural network                                                   | Differential Para + logical predicates and verification machinery      |
| Neural network whose admissible parameters depend on operating conditions | Differential contextads                                                |
| Distributed or parallel neural computation                                | Monoidal Para/Ctx + suitable independence/interchange laws             |
| Neural agent with observations, internal state, and actions               | Mixed Ctx–Cnt, potentially differential and stochastic                 |
| Graph-based computation with hidden intermediate witnesses                | Span-based semantics                                                   |
| Composable hardware or circuit network implementing a neural system       | Cospan-based wiring + decorated or behavioral semantics                |

These combinations are capability targets, not automatically available products. Each combination requires compatibility between the component structures. The mixed and differential cases are particularly nontrivial.

## 4. The deeper organization

There are roughly six independent questions about a computational system:

| Question                                                   | Relevant construction                   |
| ---------------------------------------------------------- | --------------------------------------- |
| What can be tuned?                                         | Para                                    |
| What contextual information is required?                   | Comonads / Ctx                          |
| What can the computation produce beyond its result?        | Monads / Cnt                            |
| What uncertainty is involved?                              | Stochastic enrichment                   |
| How are components interconnected, possibly with feedback? | Span/Cospan, monoidal structure, traces |
| What can be proved about its behavior?                     | Logical enrichment                      |

Differentiation adds sensitivity and optimization structure; independence adds controlled reordering; recognition theorems establish whether a semantics admits one of these representations.

The important takeaway is that these structures are not competing architectures. They expose different dimensions of a system that ordinary function composition suppresses.

A neural network, a stochastic stateful controller, and a verified probabilistic program may all contain parameterized functions. What distinguishes them is the additional structure carried through composition.

For the paper's program, the most interesting integrations are those where the dimensions interact rather than merely coexist: dependent gradients, stochastic contexts with explicit implementations, logical specifications stable under context substitution, and mixed context-consuming/content-producing composition. Those are the places where the wreath-product perspective could do work that a straightforward juxtaposition of existing categories cannot.