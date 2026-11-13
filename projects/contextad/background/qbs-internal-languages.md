# QBS internal languages and higher-order boundaries

> Status: Background exposition of established QBS probability and its limitations, not a new theorem or completion claim. Literature attributions have not received a fresh independent audit. Contextad conclusions remain governed by the relevant manuscripts.

## Probability presentation

Let \(P:\mathbf{QBS}\to\mathbf{QBS}\) be the Heunen–Kammar–Staton–Yang probability monad and

\[
\mathbf{QBStoch}:=\mathbf{Kl}(P),
\qquad
\mathbf{QBStoch}(X,Y)=\mathbf{QBS}(X,PY).
\]

There are **two different things one can mean by “the internal language”**, and collapsing them loses most of what is interesting about QBS.

The **bare internal language of the Markov category** \(\mathbf{QBStoch}\) looks essentially like every other Markov-category language: first-order stochastic `let`, pairing, projection, copying and discarding. The **internal language retaining the presentation \(\mathbf{QBS}\xrightarrow{P}\mathbf{QBS}\)** is substantially richer: it is a higher-order monadic probabilistic lambda calculus, because \(\mathbf{QBS}\) is cartesian closed and \(P\) is strong. That second language is the one that captures why QBS was introduced in the first place. [Department of Computer Science](https://www.cs.ox.ac.uk/people/samuel.staton/papers/lics2017-qbs.pdf)

The kernel of the forgetful move

\[
(\mathbf{QBS},P)\longmapsto \mathbf{Kl}(P)\text{ merely as a Markov category}
\]

contains the important structure: exponentials, the explicit probability object \(PA\), and the fact that every stochastic arrow is represented by a deterministic QBS map \(X\to PY\).

---

## 1. The bare Markov-language

A generic internal language for a Markov category has roughly

\[
\tau ::= 1\mid X\mid \tau\times\tau
\]

and

\[
M ::= x
\mid ()
\mid (M,N)
\mid \pi_iM
\mid \textsf{let }x=M\textsf{ in }N
\mid f(M),
\]

where the \(f\)'s are chosen stochastic primitives. This is essentially the standard MK calculus used in the literature. [eCommons](https://ecommons.cornell.edu/server/api/core/bitstreams/277be417-7d1b-43b1-ad7d-9fa1d236ead4/content?utm_source=chatgpt.com)

For \(\mathbf{QBStoch}\),

\[
\Gamma\vdash M:A
\]

denotes a QBS morphism

\[
\llbracket M\rrbracket:
\llbracket\Gamma\rrbracket
\longrightarrow
P\llbracket A\rrbracket.
\]

`let` is Kleisli composition:

\[
g\mathbin{\odot}f
=
\mu\circ Pg\circ f.
\]

So

```text
let x <- M in N
```

means “run \(M\), obtain one realized value \(x\), and continue with \(N\).”

That last clause matters. Variables denote **realized samples**, hence they can be copied. Stochastic computations themselves cannot be duplicated without rerunning them. Thus

```text
let x <- μ in
return (x,x)
```

has law

\[
\Delta_*\mu,
\]

whereas

```text
let x <- μ in
let y <- μ in
return (x,y)
```

has law

\[
\mu\otimes\mu
\]

for a closed \(\mu\). The first is one sample copied; the second is two independent samples.

This is why unrestricted β-style substitution of probabilistic terms is wrong:

\[
\textsf{let }x\leftarrow M\textsf{ in }N
\;\not\equiv\;
N[M/x]
\]

when \(x\) occurs more than once. The right side may rerun \(M\). This phenomenon is generic to Markov-category languages, not peculiar to QBS.

Likewise, the Markov “pair” is not cartesian pairing in the universal-property sense. Given two stochastic terms from the same context, the context is copied and the terms are run independently conditional on that context. Hence

\[
\pi_1\langle f,g\rangle=f,
\qquad
\pi_2\langle f,g\rangle=g,
\]

but generally

\[
\langle\pi_1h,\pi_2h\rangle\neq h:
\]

the left side reconstructs the product of the marginals and loses whatever correlation \(h\) contained.

---

## 2. What commutativity and affinity become syntactically

The probability monad is commutative. In programming terms, independent probabilistic computations commute:

\[
\begin{aligned}
&\textsf{let }x\leftarrow M\textsf{ in}\\
&\quad\textsf{let }y\leftarrow N\textsf{ in }K
\end{aligned}
\quad=\quad
\begin{aligned}
&\textsf{let }y\leftarrow N\textsf{ in}\\
&\quad\textsf{let }x\leftarrow M\textsf{ in }K,
\end{aligned}
\]

provided \(x\notin FV(N)\) and \(y\notin FV(M)\). This is the programming-language form of Fubini/interchange. The QBS probability monad is explicitly proved commutative. [Department of Computer Science](https://www.cs.ox.ac.uk/people/samuel.staton/papers/lics2017-qbs.pdf)

Affinity,

\[
P1\cong 1,
\]

gives probabilistic weakening/dead-code elimination:

\[
x\notin FV(N)
\quad\Longrightarrow\quad
\textsf{let }x\leftarrow M\textsf{ in }N
=
N.
\]

Running a normalized random experiment and throwing its answer away has no observable effect.

That also tells you what is **not** in this language. There is no nontrivial

```text
score : ℝ₊ -> ...
observe : ...
```

living purely in the Markov category: every map \(X\to1\) is the unique discard map. Scoring changes total mass, while an affine probability monad contains normalized probability only. This is why work on QBS-based Bayesian languages often separates an affine probability monad from a non-affine measure monad, or adds conditioning through a separate construction. [arXiv](https://arxiv.org/abs/2212.07250?utm_source=chatgpt.com)

So the raw \(P\)-Kleisli language is a **generative PPL**, not by itself a full `sample + observe` language.

---

# 3. The QBS-specific language is much richer than that

The crucial additional fact is

\[
\mathbf{QBS}\text{ is cartesian closed}.
\]

Therefore deterministic function types exist:

\[
B^A,
\]

with evaluation

\[
\operatorname{ev}:B^A\times A\to B.
\]

And since \(P\) is an endofunctor on QBS, all of these are legitimate QBS types:

\[
P(B^A),\qquad
(PB)^A,\qquad
P((PB)^A),\qquad \ldots
\]

This is precisely what ordinary measurable spaces fail to provide: \(\mathbf{Meas}\) is not cartesian closed, whereas QBS was constructed to accommodate higher-order continuous probability. [Department of Computer Science](https://www.cs.ox.ac.uk/people/samuel.staton/papers/lics2017-qbs.pdf)

A natural source language therefore looks more like a call-by-value probabilistic ML:

```text
A,B ::= Bool | Real | A × B | A + B | A -> B | Prob A

return : A -> Prob A
bind   : Prob A -> (A -> Prob B) -> Prob B

normal    : Real -> PosReal -> Prob Real
bernoulli : Real -> Prob Bool
...
```

with ordinary lambda abstraction/application at the deterministic layer and monadic sequencing at the probabilistic layer.

For example,

```text
randomLine : Prob (Real -> Real)
randomLine =
  do s <- normal 0 3
     b <- normal 0 3
     return (fun x -> s*x + b)
```

is literally meaningful denotationally:

\[
1\longrightarrow P(\mathbb R^{\mathbb R}).
\]

The original QBS paper uses exactly this sort of random-function prior in Bayesian linear regression. [Department of Computer Science](https://www.cs.ox.ac.uk/people/samuel.staton/papers/lics2017-qbs.pdf)

---

## 4. More interestingly: kernels themselves become higher-order values

For any \(A,B,X\),

\[
\begin{aligned}
\mathbf{QBStoch}(X\times A,B)
&=
\mathbf{QBS}(X\times A,PB)\\
&\cong
\mathbf{QBS}\bigl(X,(PB)^A\bigr).
\end{aligned}
\]

So a parameterized Markov kernel can be **curried into a deterministic QBS value of type**

\[
A\to PB.
\]

In programming syntax,

```text
kernel : A -> Prob B
```

is not an ad hoc encoding. It is exactly what cartesian closure of the QBS base says a stochastic map should look like internally.

The strength of \(P\) goes further: Kleisli extension itself internalizes as a QBS morphism

\[
(PB)^A\longrightarrow(PB)^{PA}.
\]

Heunen et al. use precisely this internalization to establish strength. [Department of Computer Science](https://www.cs.ox.ac.uk/people/samuel.staton/papers/lics2017-qbs.pdf?utm_source=chatgpt.com)

This is one major difference from an arbitrary Markov category. In a generic Markov category an arrow

\[
A\rightsquigarrow B
\]

is just an arrow. There need not be any object whose elements are such arrows. In QBS you have a genuine higher-order object

\[
(PB)^A
\]

representing kernels as first-class values.

But notice the typing: it is **not** \(B^A\) as a Kleisli exponential. The Kleisli category itself has not magically become cartesian closed. The closure sits in the deterministic base.

That distinction is load-bearing.

---

## 5. \(P(B^A)\) and \((PB)^A\) mean very different probabilistic programs

QBS makes a distinction that is particularly useful in higher-order PPL semantics:

\[
\boxed{P(B^A)}
\qquad\text{versus}\qquad
\boxed{(PB)^A}.
\]

The first means **a random deterministic function**. You sample \(f\) once, and calls to \(f\) share that same latent function:

```text
f <- randomFunction
return (f x1, f x2)
```

The resulting outputs can be strongly correlated because the randomness was used once to choose \(f\).

The second means **a deterministic stochastic kernel**:

```text
k : A -> Prob B
```

and

```text
y1 <- k x
y2 <- k x
return (y1,y2)
```

runs the kernel twice, giving fresh conditional randomness.

And

\[
P((PB)^A)
\]

means a **random kernel**: first choose a kernel, then invoke it.

A bare Markov-category language has no generic syntax capable of even stating all three types. QBS does.

---

# 6. The genuinely strange QBS feature: higher-order observational privacy

There is also a property in which QBStoch is not merely richer than standard examples such as Borel stochastic kernels, but actually behaves differently.

Take an atomless distribution \(\nu\) on \(\mathbb R\). Consider

```text
do x <- ν
   return (fun y -> y == x)
```

of type

\[
P(\mathbb R\to\mathbf{Bool}).
\]

In QBS this has **exactly the same distribution** as

```text
return (fun y -> false).
```

Categorically,

\[
P(\{-\})(\nu)=\delta_{\varnothing}
\qquad
\text{in }P(2^{\mathbb R}).
\]

This is the QBS **privacy equation**. The relevant higher-order QBS structure does not admit an operation

\[
2^{\mathbb R}\to2
\]

which tests whether a predicate's extension is empty, so the random singleton predicate cannot be distinguished from the constantly-false predicate when observed only as a function value. [UCL Discovery](https://discovery.ucl.ac.uk/id/eprint/10206634/1/Fritz%20Gonda%20Houghton-Larsen%20Lorenzin%20Perrone%20Stein%20-%20Dilations%20and%20information%20flow%20axioms%20in%20categorical%20probability.pdf)

But now retain the sampled \(x\):

```text
do x <- ν
   return ((fun y -> y == x), x)
```

This is **not** equal in distribution to

```text
do x <- ν
   return ((fun y -> false), x)
```

because the first predicate can be applied to the accompanying \(x\): it returns `true`, while the second returns `false`.

Thus a deterministic marginal can look completely trivial while still being correlated with another output. Fritz et al. use exactly this example to show that QBStoch fails **positivity**, and consequently also their stronger information-flow “causality” axiom. [UCL Discovery](https://discovery.ucl.ac.uk/id/eprint/10206634/1/Fritz%20Gonda%20Houghton-Larsen%20Lorenzin%20Perrone%20Stein%20-%20Dilations%20and%20information%20flow%20axioms%20in%20categorical%20probability.pdf)

That is a real semantic difference from the standard Borel fragment. The authors explicitly note that positivity survives on the full subcategory coming from standard Borel spaces; the pathology enters with genuinely higher-order objects such as \(2^{\mathbb R}\). [UCL Discovery](https://discovery.ucl.ac.uk/id/eprint/10206634/1/Fritz%20Gonda%20Houghton-Larsen%20Lorenzin%20Perrone%20Stein%20-%20Dilations%20and%20information%20flow%20axioms%20in%20categorical%20probability.pdf)

One immediate consequence is important for PPL design: **QBStoch cannot have categorical conditionals/disintegrations for all its objects**, since existence of conditionals implies positivity. So QBS buys you general higher-order continuous probability, but you cannot simultaneously assume that all of the ordinary regular-conditional-probability machinery transports unchanged to arbitrary higher-order QBS types. [UCL Discovery](https://discovery.ucl.ac.uk/id/eprint/10206634/1/Fritz%20Gonda%20Houghton-Larsen%20Lorenzin%20Perrone%20Stein%20-%20Dilations%20and%20information%20flow%20axioms%20in%20categorical%20probability.pdf)

---

## So what is actually “special”?

The clean comparison is:

| Feature | Bare Markov-category language | QBS \(+\) probability-monad presentation |
|---|---|---|
| stochastic `let` | yes | yes |
| copy realized samples / discard | yes | yes |
| independent tensoring | yes | yes |
| commutation of independent samples | Markov/Kleisli examples | explicit from commutative \(P\) |
| normalized/dead-code elimination | yes | from affine \(P\) |
| ordinary function types | **not implied** | yes, QBS is CCC |
| first-class kernel \(A\to PB\) | **not implied** | yes |
| distribution over functions \(P(B^A)\) | **not implied** | yes |
| random kernels \(P((PB)^A)\) | **not implied** | yes |
| generic `observe`/scoring | no | no, not in affine \(P\) |
| global conditionals | extra assumption | impossible over all QBStoch |
| positivity | extra axiom | fails at higher-order QBS types |
| standard first-order Borel behavior | model-dependent | agrees with Giry on standard Borel spaces |

The short version is therefore:

> **If you throw away the Kleisli presentation and retain only QBStoch as a Markov category, its generic internal language is not particularly special. It is the usual first-order Markov `let`-calculus.**
>
> **If you retain that it is \(\mathbf{Kl}(P)\) for a strong probability monad on the cartesian-closed category QBS, you get a genuine higher-order probabilistic metalanguage: deterministic functions, stochastic functions \(A\to PB\), distributions over functions \(P(B^A)\), and even distributions over kernels.**
>
> And the price of those higher-order spaces is substantive: at those types QBStoch exhibits the privacy equation and fails positivity/global disintegration, so some classical probabilistic reasoning principles that hold for standard Borel kernels cease to be valid.

I would therefore regard the **two-level deterministic/stochastic language**, rather than the undifferentiated Markov internal language, as the correct internal PPL for the QBS construction.