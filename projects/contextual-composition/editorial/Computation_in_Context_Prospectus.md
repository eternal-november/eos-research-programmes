# Computation in Context

*A research prospectus for contextual composition*

Building a system from components is attractive because each part can be understood, reused, and replaced. Yet a component’s behavior depends on its surroundings. Information available elsewhere, a shared resource, or a response from another component can affect what happens next. **Combining components also combines their dependencies.** Reusing a component therefore requires understanding which assumptions about its surroundings must remain valid.

Contextual composition develops a common account of what a computation can depend on, what it contributes, and how those relationships change when computations are combined. Its aim is a mathematical architecture for constructing computational models and carrying reasoning between them. Different choices about information, resources, effects, and interaction become explicit parts of a model, with rules governing how they fit together.

# What a computation needs and produces

The starting point is a pair of descriptions. *Context* describes what a computation draws on, such as parameters, structured information, or resources. *Content* describes the structure of what it produces, including results, effects, records, or further work. This split is a choice of representation; the same computational behavior can admit different descriptions.

These descriptions can vary with the computation. The context needed at one input may differ from the context needed at another. A result can change the requirements of the next stage. An interaction rule specifies how what one stage produces affects the context required by another, and how their requirements and produced structures are assembled.

The framework separates the descriptions of context and content, then constructs their interaction under suitable compatibility conditions. An *interactad* is the resulting structure. It makes the composite available as another component, so the construction can be repeated. Coherence ensures that regrouping a sequence of stages preserves its meaning. The theory also retains maps between representations of context and content, which become essential when components are compared. [1](https://github.com/eternal-november/eos-research-programmes/blob/68fe68124e84034160a12a032153c5a3c06de67b/projects/contextual-composition/publications/interactads/Interactads.tex)

# A design space with rules for combination

A model of computation makes consequential choices. Information may be private or shared. A resource may be reusable or consumed. A result may retain details of its production or expose only a selected observation. Components may run in sequence, overlap, or feed results back into further activity. These choices affect which compositions and transformations are valid.

Making such choices explicit helps explain what changes when a model changes. Replacing a representation of resources, for example, raises a precise question about whether the new representation supports the operations used to combine them. Changing what a component can observe changes the comparisons that can justify its replacement. The framework provides structures and preservation conditions through which such changes can be assessed.

This is where generality becomes useful. A construction can apply to a family of models because the proof depends on specified structural properties. Those properties identify which parts of the argument remain available when an ingredient changes. The aim is **reuse of reasoning across models**, alongside reuse of components within a model.

# Concurrency and feedback

Sequencing arranges dependencies across successive stages. Concurrency permits components to act with different information while contributing to an evolving system. Feedback connects outputs back into the conditions of computation. These forms of organization lead from isolated computations to sustained interaction.

The concurrent developments construct comparisons of joint behavior from local comparison data. Further results identify conditions under which a change of component preserves the information available to its partners, their opportunities to act, and specified progress properties. These are distinct aspects of replacement: preserving an output alone need not preserve the surrounding interaction. [2](https://github.com/eternal-november/eos-research-programmes/blob/68fe68124e84034160a12a032153c5a3c06de67b/projects/contextual-composition/foundations/local-joint-comparison/Local_Joint_Comparison_and_Generated_Interference.tex) [3](https://github.com/eternal-november/eos-research-programmes/blob/68fe68124e84034160a12a032153c5a3c06de67b/projects/contextual-composition/feedback-and-concurrency/information-and-progress/Information_and_Progress_Native_Comparisons.tex)

The recursive developments describe activity that can unfold while earlier activity remains in progress. In suitable constructions, subcomputations can start before their parents finish, and the semantics retains ongoing interactions as well as completed outcomes. Feedback can also close an internal interface instantaneously; this requires a different construction from a loop that evolves through time. The project develops both kinds, keeping their conditions for valid composition explicit. [4](https://github.com/eternal-november/eos-research-programmes/blob/68fe68124e84034160a12a032153c5a3c06de67b/projects/contextual-composition/foundations/incremental-arenas-and-guarded-feedback/Guarded_Incremental_Arena_Feedback_and_Cost_Trace.tex) [5](https://github.com/eternal-november/eos-research-programmes/blob/68fe68124e84034160a12a032153c5a3c06de67b/projects/contextual-composition/foundations/finite-measure-native-feedback/Finite_Measure_Native_Feedback.tex)

Across these developments, the central issue is how interaction changes what is available, who can act, and what can happen next. A model that retains this evolving structure can support reasoning about a system throughout its execution.

# Changing a model while preserving its use

A useful computational model must support simplification and comparison. Detailed representations may be needed to construct or analyze a system; smaller representations may suffice to describe a particular aspect of its behavior.

The appropriate simplification depends on how a component will be used. Two components can agree on a reported result while depending differently on shared information. A later component that can access that information may distinguish them. An abstraction therefore has to be assessed against the surrounding computations with which it must still interact.

The framework retains explicit maps between presentations of resources and produced content, and these maps participate in composition. For specified constructions and classes of surrounding computations, comparison results establish when information may be forgotten and when a distinction must remain visible. Finite probabilistic results also measure the discrepancy created by particular losses of information. [6](https://github.com/eternal-november/eos-research-programmes/blob/68fe68124e84034160a12a032153c5a3c06de67b/projects/contextual-composition/feedback-and-concurrency/retained-boundary-refinement/Retained_Boundary_Refinement_and_Correlation.tex)

This connects the choice of a model to the reasoning it supports. An abstraction comes with an account of the interactions it preserves. A replacement comes with conditions under which its comparison extends to a larger system.

# Mathematical connections and research scope

Parameterized computation, monadic effects, comonadic context, spans, and cospans provide familiar mathematical points of entry. Building on contextads and contentads, the categorical foundation relates their presentations over a shared category of pure maps. Its central work is to construct coherent interaction laws while retaining the maps that compare the ingredients. [1](https://github.com/eternal-november/eos-research-programmes/blob/68fe68124e84034160a12a032153c5a3c06de67b/projects/contextual-composition/publications/interactads/Interactads.tex)

For programming languages and semantics, the connections are to computational effects, refinement, and compositional reasoning. For concurrency, they concern local information, shared behavior, and progress under replacement. The feedback developments connect to guarded recursion and partial trace. These connections identify where existing expertise enters the programme and which questions the constructions address.

The core construction and several extensions are established under stated hypotheses; integrating the full range of concurrent and feedback models remains a research task. The larger ambition is a reusable mathematics of computational interaction: one in which a change of model comes with an explanation of which constructions still apply, which distinctions must be retained, and why the resulting components continue to compose.
