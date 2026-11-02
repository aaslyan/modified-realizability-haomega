# From Existence to Algorithm
## The analysis companion to "How a Proof Becomes a Program" — seven posts, captions and articles

*Status of this compilation: revised against repository commit `f424383` (Sept 2, 2026). The named extracted derivations and running realizers in this series report `[propext, Quot.sound]`; meta-level rational-arithmetic discharges in `QAnalysis.lean` may additionally use `Classical.choice`. Post 6 now reflects the current state: the concrete Riemann-sum operator is the `∃G` witness, while its Lipschitz premise is still assumed rather than derived internally.*

---

# From Existence to Algorithm — Post 1
# From Arithmetic to Analysis: Three Questions Before the First Theorem

---

## CAPTION

The last series ended in strange territory: Goodstein sequences and the Hydra, theorems too strong for Peano Arithmetic, each still yielding a program — extracted from its proof, checked by the kernel, with the running extracted programs staying choice-free.

But everything in that series was, in the end, arithmetic. Every object finite. Every witness a number you could print.

Analysis is where mathematics does most of its actual work — roots, fixed points, moduli, integrals — and nothing in it looks finite. So before extending the machine, three questions have to be answered honestly:

**Can the extraction pipeline reach analysis at all?**

**How do you represent a real number** — in the object language used here, whose citizens are naturals, rationals, and functions built from them? There is no completed real-number datatype in this fragment. √2 will never be a primitive value.

**How do you talk about functions** — as inputs to theorems that must hold for *all* of them, and as outputs a proof must literally hand over?

The constructive tradition — Bishop, Kreisel — has precise answers, and they reorganize everything: a real number becomes a program, a function becomes a rule *plus a modulus*, and continuity stops being a topology exercise and becomes the physics of computation itself.

This post is the front door. The program — simple to complex, one new element per post, always the same triad of realizability, extraction, continuity — starts next.

#Lean4 #ConstructiveMathematics #FormalMethods #ProgramExtraction

---

## ARTICLE

### From Arithmetic to Analysis: Three Questions Before the First Theorem

The previous series, *How a Proof Becomes a Program*, ended somewhere genuinely exotic: Goodstein's theorem and the Hydra game — statements that outrun Peano Arithmetic, provable only by induction along ordinals up to ε₀ — and yet the same small machine read their proofs and produced terminating programs, with the kernel confirming the extracted derivations and running programs stayed choice-free. The broader soundness layer has its own printed axiom budget; the executable evidence is the point here.

Exotic in strength. But look at the *objects*, and that series never left home. A Goodstein sequence is a list of natural numbers. A hydra is a finite tree. Every witness the machine ever produced was a finite thing you could print. The realizability discipline — statements interpreted as evidence types, proofs read out as programs — was only ever exercised on data.

Analysis is the opposite country. Its objects are limits, its functions are uncountable, its central theorems assert existence of things no one can write down. And analysis is where mathematics earns its living — root-finding, fixed points, differential equations, integration. If the extraction machine cannot go there, it is a curiosity. So the question this new series answers:

**Can we extend from arithmetic to mathematical analysis?**

Not by waving at the difficulty — by answering the three questions the difficulty is made of.

#### Question 1: How can we represent a real number?

The object language used in this series has naturals, rationals — a pair of integers, honestly finite — and functions built over them. It does not have a completed ℝ base type: a real number carries infinitely much information, and every closed value in this fragment is finite.

The constructive tradition's answer, Bishop's answer, is to stop asking for the completed object and take the *approximation process* as primary. What can be finite about √2? Any single approximation. What captures √2 entirely? The ability to produce an approximation **at every precision**: for each n, a rational within 2⁻ⁿ, coherently.

So in this series a real number will never appear as a value. It will appear as a theorem shape:

```
∀n. ∃k.  ⟨the k-th grid point at resolution 2⁻ⁿ brackets the target⟩
```

— and realizability interprets `∀n ∃k` as evidence of type ℕ → ℕ. Read that twice, because it is the founding move of everything that follows: **the real number is the extracted program.** Not "the program approximates the real" — under this representation, the coherent family of approximations is what a real *is*, and the program is that family, packaged executably. Classical analysis treats the number as primary and approximation as an afterthought; constructively the order reverses, and the reversal is what makes extraction possible.

#### Question 2: How can we talk about functions?

Reals were the easy half. Analysis is really about *functions* — and functions show up in two roles, each with its own problem.

**As inputs.** A theorem worth having says "for every continuous f…" — quantifying over an infinite totality of infinite objects. How can a proof, a finite text, handle an f it cannot inspect? By treating f as a **function variable**: a black box the proof may *query* at points but never expand. The logic for this is Heyting Arithmetic in all finite types, HA^ω — the ω is exactly the license to quantify at type ℚ → ℚ, at (ℚ → ℚ) → ℕ, and up the whole hierarchy. The proofs of this series live there, and their extracted realizers are System T terms at the corresponding types.

And here the deepest constraint of the series surfaces, disguised as a triviality. An extracted realizer is a program; programs terminate; so a program consuming a function can only ever have *queried it finitely often* before answering. Its output depends on a finite probe of an infinite input. That property has a name — **continuity** — and in this repository it is not just a slogan but a checked theorem about extracted terms. The ε-δ definition you learned is the metric shadow of this computational fact. When this series says *continuity*, this is what it means, and it will mean it in every single post.

**As outputs.** Harder still: some theorems must *hand over* a function — "there exists G such that…". A bare rule for G is unusable to a constructive consumer: to compute with G at all, you must know how finely to sample its input for a given output demand. That knowledge is the **modulus of continuity**, and the standing convention of constructive analysis follows: a function is not a rule. **A function is a rule plus a modulus**, and the pair travels together or the object does not exist for us. When, late in this series, an existential appears at arrow type, its witness will be exactly such a pair — a function carrying its own certificate.

#### Question 3: What happens to the theorems?

Re-represent the objects and every classical statement must be re-read. "A root exists" — where every quantifier now ranges over finite data — becomes "for every precision, some grid cell brackets the crossing." "The iterates converge" becomes "here is the stopping rule." "The integral exists" becomes "here is a function, with its modulus." In each case the existential is now the kind of claim that can *fail* — a wrong bracket, a premature stopping count, a broken modulus are all refutable by concrete terms — and a claim that can fail is a claim whose proof must build something. What it builds is the algorithm.

Notice what happened to the witnesses across those three re-readings: a number; then a function ℕ → ℕ; then a function-with-certificate. The witness types climb. That climb is not incidental — it is the natural difficulty ordering of constructive analysis, and it hands this series its table of contents.

#### The program

Simple to complex, one new element per post, and every post ending on the same triad — **realizability** (the statement's shape fixes the program's type), **extraction** (the proof, read at that type, is the program), **continuity** (the finiteness that makes higher-type computation possible at all):

**Post 2** — the ground floor, plus the test that polices the whole series: what makes an existential worth extracting from. A number witness — √2 bracketed at every precision, traced end to end.

**Post 3** — the first new element: a *function variable*. One theorem, blind to its function, whose extracted solver brackets F(x) = y for any F supplied with endpoint colours witnessing a crossing — and whose finitely-many-queries behavior makes continuity visible for the first time.

**Post 4** — continuity itself becomes the extracted object: the modulus, the ε-δ correspondence as a callable function.

**Post 5** — the modulus turned ninety degrees, from space to time: a Banach-style contraction theorem whose realizer is the exit condition of your while loop, sharp to the boundary.

**Post 6** — the climb's top: an existential at arrow type, whose witness is a function bundled with its own modulus. The Riemann-sum integral operator — including, stated plainly, the Lipschitz premise still assumed rather than derived internally.

**Post 7** — the payoff: a differential equation that two earlier theorems solve *together*, though neither was built for it. Composition as the argument that this is a small theory, not a pile of examples.

Three questions, three answers — the real as program, the function as rule-plus-modulus, the theorem as falsifiable approximation claim — and the same mechanism as the last series, lifted to all finite types and pointed at the country those answers open. The program begins next post, with the test.

*Series: From Existence to Algorithm — the analysis companion to "How a Proof Becomes a Program." Source links pinned to commit in the comments.*

---

# From Existence to Algorithm — Post 2
# The Test: What Makes an Existential Compute

---

## CAPTION

Post 1 asked whether the extraction machine reaches analysis at all, and answered with representations: a real number as an approximation procedure, a function as a rule plus a modulus. Now the program begins.

But before the first theorem, a test. A statement of the form "there exists a y equal to f(n)" is provable for any f you've already written: hand over f(n), close by reflexivity. Nothing was discovered. So for every result in this series, one question decides whether it counts:

**Is there a term that would make this statement false?**

If not, there was nothing to prove — and nothing to extract.

Post 2 takes the simplest statement that passes: a bracket for √2. Traced completely — statement, proof obligation, Sperner-derived search, kernel run, 181/128. One number witness, honestly sourced, including the endpoint-colour premise the object-level derivation takes and the repository's later arithmetic discharge of that premise.

The ladder runs from here: each post adds one element, and every one is about the same triad: realizability, extraction, continuity.

#Lean4 #ConstructiveMathematics #ProgramExtraction #FormalMethods

---

## ARTICLE

### The Test: What Makes an Existential Compute

Classical analysis is full of existence theorems. *A root exists. A fixed point exists. The integral exists.* Each is proved by an argument that establishes existence without producing the object — a supremum, a compactness argument, a contradiction.

Read the same statements constructively and the existential has to deliver. `∃x. φ(x)` means: *here is an x, and here is why it works.* That is realizability in one sentence — Kreisel's modified realizability assigns to every formula a type of evidence, and to `∀n ∃k` the type of evidence is a **function** from n to k. A proof is then a recipe for evidence, and extraction is the mechanical step that reads the recipe out as a program.

The previous series showed that pipeline on discrete mathematics, ending with theorems that outrun Peano Arithmetic. Analysis is a different kind of challenge, and it is worth being precise about why before touching any theorem.

#### There is no finite object called √2

Post 1 made the case: √2 is not a datum but a destination, and a constructive real is the ability to approximate it at every precision. What follows is that move applied to one theorem, with nothing hidden — the precision parameter is the object, not an appendix.

#### The test

One more piece of discipline before the first theorem, because it decides which results count and which are theater.

A specification of the form

```
∃y. y = f(n)
```

is provable for any `f` already defined. Hand over `f(n)`, close by reflexivity. The proof discovered nothing; the extracted "program" is the function you already had, returned to you with ceremony. Early rounds of this project produced several of these before the pattern was named, and the cure is a single question asked of every formalized statement:

**Is there a term that would make this statement false?**

A property that any term satisfies is not a specification. A property that most terms *fail* — a bracket that must actually bracket, a bound that must actually bound — forces the proof to construct something, and what it constructs is the algorithm. Every post in this series applies this test out loud.

#### The simplest statement that passes

Here it is — call it `sqrtApproxD`, and read it slowly:

```
∀n. ∃k.  (k/2ⁿ)² ≤ 2  <  ((k+1)/2ⁿ)²
```

For every precision, there is a grid index whose cell brackets √2. Apply the test: could a wrong k make this false? Immediately — k = 0 at n = 8 gives 0 ≤ 2 < (1/256)², which is false. Almost every k fails. The existential has content.

Now watch what realizability does to the statement's *type*. `∀n ∃k` over naturals gets evidence of type `ℕ → ℕ`. Whatever proof we give, the extracted program will be a function from precision to grid index. The statement's logical shape has already dictated the program's type signature, before a single line of proof exists. That correspondence — formula shape to program type — is the whole discipline, and it is why the proof cannot cheat.

#### What the proof must do, and what falls out

The derivation does not build a special square-root proof from scratch. It instantiates one-dimensional Sperner with the colouring

```
colour(k) = 1  iff  2 < (k/2ⁿ)²
```

Sperner supplies the induction: if the left endpoint is coloured 0 and the right endpoint is coloured 1, some adjacent pair changes colour. Read through the square colouring, that adjacent change is exactly the bracket for √2.

I want to be plain about the endpoint hypothesis, because it is the honest edge of this theorem's object-level statement. `sqrtApproxD` takes the endpoint colours as premises. In `SquareRoot.lean`, the build checks the relevant instances by `#guard`; in the full repository, `QAnalysis.sqrt_premises` proves a computable bound for every nonnegative q using `sqrtBound`. That discharge lives at the meta-level rational-arithmetic layer, not as a new object-level grid proof.

Run the Sperner-derived derivation through `extract` and out comes a closed System T term — a search loop nobody wrote. In the kernel, at n = 8:

```
k = 362        362/256 = 181/128 ≈ 1.41406
```

with the bracket checked by `#guard` at compile time: (181/128)² ≈ 1.99982 ≤ 2, and the next cell up overshoots. Exact rational arithmetic, no floating point anywhere, and the answer is not "√2 ≈ 1.414" but a *certified interval* — which, at every precision simultaneously, is what a constructive real number is.

#### The triad, which every post will end on

**Realizability** turned `∀n ∃k` into the promise of a function `ℕ → ℕ` before any proof existed — the statement's shape fixed the program's type.

**Extraction** kept the promise: reading the Sperner induction produced a search term, and — given the endpoint-colour premises — the kernel's soundness theorem certifies that its output satisfies the bracket. The extracted derivation and running realizer report `[propext, Quot.sound]`; the later arithmetic proof that computes a general bound for q ≥ 0 is a separate meta-level discharge and reports its own axiom footprint.

**Continuity** appeared as the precision parameter itself: the program never touches a completed real, only finite information — a rational answer for each finite demand. Holding that thought is the key to the entire series, because next time the *input* becomes infinite too.

**Next post:** the proof stops knowing its function. One quantifier moves to function type — `∀F : ℚ → ℚ` — and the same extraction yields a solver that brackets `F(x) = y` for any F you can write, including several it has never met.

*Series: From Existence to Algorithm, the analysis companion to "How a Proof Becomes a Program." Source links pinned to commit in the comments.*

---

# From Existence to Algorithm — Post 3
# The Solver That Never Met Its Function

---

## CAPTION

Last post extracted a program that brackets √2. Nice, but a specialist — it knows one equation.

This post moves one quantifier, and everything changes:

```
∀F : ℚ → ℚ. ...
```

F is a *function variable*. The proof does not know which function it will be handed — so nothing in the derivation can depend on F's formula, and the extracted program inherits that indifference. One theorem, proved once, and the solver it yields brackets `F(x) = y` for whatever you supply, once the two endpoint colours certify a crossing:

2x + 1 = 5 → 2
x³ + x = 10 → 2
x⁵ = 32 → 2
x² = 2 → 181/128 at 2⁻⁸
x⁴ = 2 → 19/16 at 2⁻⁴

Same extracted term, five equations. And the conclusion asserts a *disagreement* — two adjacent evaluations differ — so reflexivity has no grip. Last post's falsifiability test, passed at a higher type.

Underneath is Sperner's lemma in one dimension. Not "analogous to" the intermediate value theorem — the same theorem, at a different colouring.

And one thing the extracted solver can never do: read all of F. It asks finitely many questions. That finiteness has a name, and it becomes the spine of the series.

#Lean4 #ConstructiveMathematics #ProgramExtraction #TypeTheory

---

## ARTICLE

### The Solver That Never Met Its Function

Post 2 ended with a certified bracket for √2 and a promise: the input was about to become infinite.

Here is what that means. The √2 program took a natural number — a precision — and returned a natural number. Finite in, finite out. The theorem in this post takes a **function** as input. A function `ℚ → ℚ` is an infinite object; you can never be handed all of it. And yet the extracted program accepts one, does its work, and returns a certified answer. How a finite program consumes an infinite input is the real subject of this post, and the answer is the series' central word. But first, the theorem.

#### Moving one quantifier

```
fnCrossingD :
  ∀F : ℚ → ℚ. ∀y ∀n ∀K.
      F brackets y on [0, K]  →  ∃k.  k < K  ∧  colour(k) ≠ colour(k+1)
```

Colour each grid cell by a single bit: is `F` at this point still below `y`, or already above? The hypothesis says the left end is coloured one way and the right end the other. The conclusion locates two *adjacent* cells that disagree — which is exactly a bracket for the crossing of `F(x) = y`, at grid resolution `2⁻ⁿ`.

Apply Post 2's test before anything else. Could a term make this false? Yes, instantly: the conclusion asserts that two evaluations *differ*, and no term is unequal to itself, so reflexivity — the cheat that trivializes `∃y. y = f(n)` — has no grip here. The proof must locate the disagreement. There is something to extract.

Now the important part. `F` is quantified as a **function variable**. The derivation never sees a formula for F. It cannot expand F, differentiate F, or exploit that F is a polynomial, because as far as the proof is concerned F is a black box answering one kind of question: *at this rational point, are you below y or above?* Everything else in the proof is grid bookkeeping — walk the cells, compare colours, and the hypothesis guarantees the walk cannot exit without finding the flip.

#### Why this is Sperner, and why that matters

That colour-walking argument has a name. It is Sperner's lemma in dimension one: a path whose endpoints are coloured differently contains an adjacent disagreeing pair. Sperner's lemma quantifies over the colouring as a function variable, so its proof never inspects the arithmetic that produced the colours.

Which yields a sentence I want to state carefully, because it is the most structural claim in this post: the discrete intermediate value theorem and the combinatorial lemma are not *analogous* here. They are the **same theorem, instantiated at a different colouring**. Colour by "below y / above y," supply endpoints with different colours, and Sperner *is* the discrete IVT. The proof was never about analysis; analysis is one reading of it. That is what quantifying over the function bought — a theorem that does not know which subject it belongs to.

#### One term, five equations

Extraction reads the derivation and returns a closed higher-type term — roughly `(ℚ ⇒ ℚ) ⇒ ℚ ⇒ ℕ ⇒ ℕ ⇒ ℕ`: function, target, precision, range, out comes the index. Run in the kernel, exact rationals, `#guard`-checked:

| Equation | Certified answer |
|---|---|
| `2x + 1 = 5` | `2` |
| `x³ + x = 10` | `2` |
| `x⁵ = 32` | `2` |
| `x² = 2` | `181/128` at `2⁻⁸` |
| `x⁴ = 2` | `19/16` at `2⁻⁴` |

The same extracted term produced every row. Not the same algorithm re-derived five times — the same *value*, applied to five different F's, some with no closed-form inverse. Note the middle rows land on exact integers: when the crossing sits on the grid, the bracket says so exactly, which floating point could not promise.

Last post's √2 answer reappears — 181/128 — now produced by a machine that was not built for square roots. The specialist from Post 2 has become a corollary.

#### The inverse function comes free

Fix `F`, and let `y` vary instead: the same program is now a pointwise inverse solver wherever the bracket premises are supplied. For `F(x) = x³ + x` at `y = 10`, the solver returns

```
g(10) = 2,        and   2³ + 2 = 10   exactly.
```

The round trip is the check that matters — not "close to 10," but equal to 10, as rationals. It is not a global inverse-function theorem: it proves no injectivity, no total inverse, no inverse modulus. It is a callable pointwise inverse certificate, on a function nobody taught it.

#### The finiteness underneath

Now the promised point, because it outranks the demos.

The extracted solver takes an infinite input and terminates. It can therefore never have consumed all of F. Count what it actually did: at range K and resolution 2⁻ⁿ, it evaluated F at finitely many grid points, compared, and answered. Two functions that agree at those points get identical answers — the program *cannot tell them apart*. Its output depends only on a finite amount of information about its infinite input.

That property is called **continuity**, and this is the precise sense the series means by the word: a functional is continuous when every finite demand on its output is met by a finite probe of its input. The ε-δ definition from analysis is the metric shadow of this idea. Realizability forces it on us — an extracted term is a program, programs run in finite time, so every realizer that eats a function is continuous *by construction*. The theory of what extracted programs can be is a theory of continuous functionals, and that is not a metaphor; it is the standing invariant of the whole pipeline.

#### The triad

**Realizability:** `∀F` at function type promised a higher-type program — a functional — before the proof existed; the statement's shape fixed that the solver would take F as an argument.

**Extraction:** one derivation, one closed term, five certified equations and a pointwise inverse solver under bracket premises; the proof's ignorance of F became the program's generality.

**Continuity:** made explicit for the first time — the solver interrogates F at finitely many points, so it is a continuous functional, and every realizer at this type must be.

**Next post:** continuity stops being a property we observe and becomes *data we compute*. The ε-δ correspondence itself, extracted as a function — the modulus.

*Series: From Existence to Algorithm. Source links pinned to commit in the comments.*

---

# From Existence to Algorithm — Post 4
# A Function Is a Rule Plus a Modulus

---

## CAPTION

Every analysis course promises that for each ε there exists a δ. Almost none of them hand you the δ.

The δ was constructed inside the proof — it had to be — and then discarded the moment the theorem was stated with an existential. Realizability is, from one angle, the refusal to discard it: `∀n ∃M` has evidence of type ℕ → ℕ, so the extracted realizer *is* the ε-δ correspondence, as a function you can call.

```
∀f ∀j.  (∀x ∀y. |f(x) − f(y)| ≤ 2ʲ·|x − y|)  →  ∀n ∃M ∀x ∀y.
        |x − y| < 2⁻ᴹ  →  |f(x) − f(y)| < 2⁻ⁿ
```

Extracted modulus: M(n) = n + j. For f(x) = 2x, ask for output precision 2⁻⁵ and it answers: input step 2⁻⁶. Three symbols of program, and the entire computational content of the theorem is in your hand — and replacing them with M(n) = n makes the proof stop building.

Last post, continuity was something we *observed* — the solver could only probe its function finitely often. This post, continuity becomes something we *compute*. That is the whole move: in constructive analysis a function is not a rule. It is a rule **plus a modulus**, and a function that arrives without one is unusable.

Post 4 of 7. The honest edge — where the arithmetic between bound and modulus currently lives — is stated in the article, same as every post.

#Lean4 #ConstructiveAnalysis #ProofMining #FormalMethods

---

## ARTICLE

### A Function Is a Rule Plus a Modulus

Post 3 ended on an observation: the extracted solver, handed an infinite input, only ever asked it finitely many questions. Continuity, in the exact sense that matters for computation — finite demands met by finite probes.

But observing that a program is continuous and *knowing how continuous* are different states of knowledge. If I hand you f and say "it's continuous," you still cannot compute with it: to get f's value within 2⁻⁵, how finely must you know the input? Without an answer, every downstream computation stalls at its first approximation. The answer has a name — the **modulus of continuity** — and this post is about extracting it, which turns continuity from a property into a datum.

#### The small dishonesty in how analysis is taught

A proof of uniform continuity constructs a δ for each ε. It must — the ε-δ condition cannot be verified without exhibiting something. Then the theorem is stated:

> for every ε > 0 there exists δ > 0 such that …

and the construction vanishes into the existential. The information was produced and then thrown away at the moment of publication. Every later user must reopen the proof to recover it. Kohlenbach's proof-mining programme has spent two decades systematically recovering exactly this kind of discarded content from published analysis — that a proof knows more than its theorem states is not a curiosity, it is a research field.

Realizability makes the recovery automatic, because the interpretation of `∀n ∃M` is not "M exists" but a *function* n ↦ M. State the theorem, prove it constructively, and the modulus is not buried in the proof — the modulus **is** the extracted realizer.

#### The theorem, and the test

Work dyadically — "within 2⁻ⁿ" instead of "within ε" — so everything stays in ℕ and ℚ. Say f is 2ʲ-Lipschitz, stated as the honest algebraic bound:

```
uniContLipD :
  ∀f : ℚ → ℚ. ∀j.  (∀x ∀y.  |f(x) − f(y)| ≤ 2ʲ·|x − y|)  →
      ∀n. ∃M. ∀x ∀y.  |x − y| < 2⁻ᴹ  →  |f(x) − f(y)| < 2⁻ⁿ
```

First, the series' standing test: is there a term that would make this false? Yes — M must actually bound. Take f(x) = 2x and claim M = n: then x, y at distance just under 2⁻ⁿ give |f(x) − f(y)| up to nearly 2·2⁻ⁿ, violating the bound. Wrong moduli are refutable, so the existential has content. And note where `f` sits: a function variable again, Post 3's element carried forward — this is every 2ʲ-Lipschitz function at once, not one.

Note also what the hypothesis does *not* say. An earlier version of this theorem took as its premise the ε-δ statement itself, with the scale n + j already written into it — so the "proof" was ∃-introduction reading a number off the hypothesis, and the falsifiability test, applied honestly, rated it a read-out rather than a derivation. The premise above is the algebraic Lipschitz bound and nothing more. The modulus is not in it.

The informal proof is one line of arithmetic: Lipschitz gives |f(x) − f(y)| ≤ 2ʲ·|x − y|; make |x − y| < 2⁻⁽ⁿ⁺ʲ⁾ and the right side drops below 2⁻ⁿ. Take M = n + j.

Extraction reads the derivation and returns

```
λf. λj. λhyp. λn.  n + j
```

with the (computationally void) proof that n + j works alongside. Erase the void component and the extracted Haskell is:

```haskell
modulus :: Int -> Int -> Int
modulus j n = n + j
```

I will not dress this up: the realizer is three symbols. That is precisely why it belongs in the series. You can hold the *entire* computational content of a theorem in your head. And the mutation test is what makes those three symbols mean something: change the witness to M := n and the derivation no longer builds, because the step from the Lipschitz bound to the conclusion needs the input closeness at scale n + j and nothing coarser will feed it.

Run it: f(x) = 2x is 2¹-Lipschitz, so j = 1. Request output precision 2⁻⁵; the modulus answers M = 6. Check: |x − y| < 2⁻⁶ forces |2x − 2y| < 2⁻⁵. The δ you were promised, delivered as a return value.

#### Where the arithmetic lives

One thing to be exact about, because it is the honest edge of this post. The informal proof above has an arithmetic step — multiply by 2ʲ, cancel against 2⁻⁽ⁿ⁺ʲ⁾, chain a ≤ with a <. Inside the object language that whole step is currently a single rule: *from the Lipschitz bound and closeness at scale n + j, conclude closeness at scale n.* The derivation applies that rule once, so the modulus is derived from an honest premise, but the arithmetic between premise and modulus is admitted as one object-level inference rather than assembled from smaller conversion steps.

The axiom budget has to be said in two layers. The extracted theorem and realizer report `[propext, Quot.sound]`. The Lean proof validating the rational arithmetic behind the scale rule lives in the meta-level arithmetic layer and reports `[propext, Classical.choice, Quot.sound]`. That is not a classical leak into the extracted program, but it is also not "no axiom." Until the object-language rule base is decomposed further, the correct sentence is: the modulus is forced by one sound scale-conversion rule, not read off the hypothesis and not yet computed step by step inside `Deriv`.

#### Why the packaging matters

In constructive analysis a real function on an interval is not a rule; it is a **rule plus a modulus**, and the pair travels together or the object is unusable — no composition, no integration, no fixed-point iteration can begin until the modulus is in hand. `uniContLipD` is the adapter that turns raw Lipschitz information into the citizenship papers a function needs to enter the rest of the theory. Post 6 will ask for exactly this shape as a *witness* — a function handed over together with its certificate — and this theorem is what will certify it.

#### The gap, second sighting

Post 2 met the series' recurring arithmetic boundary as endpoint-colour premises for square roots; the full repository now discharges those premises in `QAnalysis`, but not by adding a new object-level derivation. Here the boundary appears as the scale-conversion rule above. The common theme is not one literal missing lemma, but a small object-language rational-arithmetic rule base being asked to support analysis. The kernel's axiom report is what keeps the bookkeeping honest: extracted derivations and running realizers print `[propext, Quot.sound]`, while the meta-level arithmetic discharges print their own, sometimes larger, footprint.

#### The triad

**Realizability:** `∀n ∃M` meant the theorem's evidence had type ℕ → ℕ before any proof existed — the ε-δ correspondence was destined to be a callable function.

**Extraction:** the callable function arrived: M(n) = n + j, forced from an honest Lipschitz bound — the wrong witness does not build — with the arithmetic between bound and modulus admitted as one sound scale-conversion rule.

**Continuity:** promoted from observed property to computed data — the modulus is continuity, quantified, and it is the piece of equipment every later post's function must carry to be used at all.

**Next post:** the modulus idea turns ninety degrees. Instead of *how finely must I know the input* — how long must I run the loop? A Banach-style contraction theorem, extracted, answers with the exit condition of your `while`.

*Series: From Existence to Algorithm. Source links pinned to commit in the comments.*

---

# From Existence to Algorithm — Post 5
# When to Stop

---

## CAPTION

A contraction theorem tells you the iterates settle down. It does not, by itself, hand you the stopping rule your program needs.

Every numerical programmer has felt that gap. The loop is two lines; the exit condition is folklore — a tolerance chosen by feel, a max-iterations guard just in case. The convergence *rate* is exactly what the classical statement withholds.

Constructively, the rate is the content:

```
∀T : ℚ→ℚ. ∀x₀. ∀k₀.
  (∀u v m.  close(m, u, v) → close(m+1, T u, T v))     -- T contracts by ½
  → close(k₀, x₀, T x₀)                               -- the first gap is bounded
  → ∀n ∃N ∀d.  close(n, x_{N+d}, x_{N+d+1})
```

Read the tail: not "close once," but from N on, *forever* — ∀d. A finite number certifying an infinite future. The extracted realizer is ℕ → ℕ: precision in, iteration count out. It is the exit condition of your while loop, derived by induction on the orbit — the contraction hypothesis applied at every single step.

Three operators, one program — T is a function variable, the element this series has been stacking since Post 3:

1 + y/2 from 1 → fixed point 2
3 + y/2 from 5 → fixed point 6
y/2 from 1 → fixed point 0

And the check that would catch a lie: replace the witness N with 0 and the proof no longer builds.

#Lean4 #NumericalAnalysis #ConstructiveMathematics #ProgramExtraction

---

## ARTICLE

### When to Stop

The series so far, as a ladder: Post 2 extracted a number witness. Post 3 let the theorem take a *function* as input. Post 4 turned continuity itself into extractable data — the modulus, "how finely must I know the input."

This post asks the same species of question in a new direction: not how finely, but **how long**. An iteration is an infinite process; a program must be finite. The bridge between them is again a modulus — this time a modulus of *convergence* — and a Banach-style contraction theorem is where it lives. The formal result here is not the whole classical fixed-point theorem: no completeness theorem, no constructed limit point, no uniqueness proof. It is the computational core the loop needs, a certified bound on when consecutive iterates are small forever. It is also the first post in the series where the proof is an honest-to-goodness induction, and where the object language had to grow a rule to finish it.

#### What the classical theorem withholds

Banach: a contraction on a complete space has a unique fixed point, and iterating from anywhere converges to it. It is the workhorse existence theorem of applied mathematics — ODE solvers, equilibrium arguments, iterative methods all stand on it.

And it is silent on the one question practice asks every single time: *when do I stop?* The classical proof knows the answer — the geometric decay is right there in the argument — but the theorem's statement discards it, exactly the discarding Post 4 diagnosed in the ε-δ tradition. So every implementation reinvents the rate as folklore: `while (err > tol && iter < MAX)`, with `tol` and `MAX` chosen by feel.

Constructively there is nowhere to hide the rate. In the fragment formalized here, the rate appears as a modulus for consecutive iterate gaps.

#### The theorem, and the quantifiers worth staring at

```
banachContractionD :
  ∀T : ℚ → ℚ. ∀x₀ : ℚ. ∀k₀ : ℕ.
    (∀u v : ℚ. ∀m : ℕ.  close(m, u, v) = 1  →  close(m+1, T u, T v) = 1)
    →  close(k₀, x₀, T x₀) = 1
    →  ∀n. ∃N. ∀d.  close(n, x_{N+d}, x_{N+d+1}) = 1
```

where `close(m, u, v) = 1` is the dyadic test |u − v| < 2⁻ᵐ and x₀, x₁ = T(x₀), x₂ = T(x₁), … is the orbit.

Three things to look at. First, `T` is a **function variable** — Post 3's element, load-bearing again. This is every ½-contraction, from every start, and the proof must work blind to T's formula.

Second, the **hypothesis is really a contraction**: if two points are within 2⁻ᵐ, their images are within 2⁻⁽ᵐ⁺¹⁾. Nothing about the orbit is assumed — only that T squeezes, plus one seed fact, that the first gap is bounded. Everything about the orbit must be *derived*. Apply the series' test: could the hypothesis already contain the conclusion? No — it speaks about arbitrary pairs u, v and never mentions iteration.

Third — the one to stare at — the tail: `∃N ∀d`. Not "some gap is eventually small," which would be cheap, but: from step N onward, **every** future gap is below 2⁻ⁿ. A single finite N is asked to certify an infinite future. Claim any N one step too early and a concrete d refutes you.

#### The proof is an induction, and the contraction is used at every step

The derivation proves a lemma first, by induction on m in the object language:

```
L(m) :   close(m + k₀, x_m, x_{m+1}) = 1
```

*Base.* m = 0: the seed, after unfolding x₀ and x₁ = T(x₀) through the recursor.

*Step.* Assume L(m). Instantiate the contraction hypothesis at u := x_m, v := x_{m+1}, scale m + k₀: the images T(x_m) = x_{m+1} and T(x_{m+1}) = x_{m+2} are within 2⁻⁽ᵐ⁺ᵏ⁰⁺¹⁾ — which is L(m+1) once the recursor unfolds one more time and (m + k₀) + 1 is rewritten as (m + 1) + k₀.

That is the geometric decay, *proved*, with the contraction hypothesis consumed once per step. Then the witness: N := n. From L at m := n + d you have closeness at scale n + d + k₀, which is at least n — so one more fact finishes it: closeness at a finer scale implies closeness at a coarser one.

That fact did not exist in the object language. Scale monotonicity of `close` was missing, and finishing this proof meant adding it: one object-level rule, with its soundness checked on the Lean side. I mention this because it is what the arithmetic boundary this series keeps naming actually looks like from inside — not a wall but a rule base that grows a line when a theorem needs one.

The realizer that falls out:

```
N : ℕ → ℕ,   N(n) = n        — precision in, iteration count out
```

The exit condition of your `while` loop, as the computational content of the contraction-iteration theorem. Not folklore. Derived — and this time the word is earned.

#### The check that would catch a lie

A stopping rule can fail politely. Overshoot by one and every test still passes — you merely iterate longer than needed, and no one notices the theorem went slack. Two checks guard against that.

The first is on the proof itself. Replace the witness N := n by N := 0 and the derivation **does not build**: the induction lemma at m := d gives closeness at scale d + k₀, and nothing bridges that to scale n. A vacuous theorem would accept any witness; this one accepts exactly the right one. That mutation test is the acceptance criterion for every theorem in this series, and it is what `#print axioms` cannot tell you.

The second is on the instance. Take T(y) = 1 + y/2 from x₀ = 1, whose orbit climbs toward 2:

```
x₀ = 1,  x₁ = 3/2,  x₂ = 7/4,  x₃ = 15/8,  x₄ = 31/16,  x₅ = 63/32
```

The contraction hypothesis is checked at the value level on sample pairs, and the seed gap is 1/2 — inside the theorem's domain. Request n = 4; the rule answers N = 4:

```
|x₄ − x₅| = 1/32  <  1/16      ✓
|x₃ − x₄| = 1/16  —  not  <  1/16      ✗, as required
```

One step early and the gap sits *exactly on* the boundary, where the strict inequality fails. The theorem certifies that N(n) = n *suffices* for every contraction; this computation shows it is also *least* for this one. Notice the verdict is only pronounceable in exact arithmetic: whether 1/16 < 1/16 is not a question you want floating point to adjudicate. Exact rationals are not a purism here. They are the instrument that makes sharpness checkable at all.

#### Three operators, one program

Because T is an argument, the same extracted term prices every ½-contraction whose seed gap is bounded. Kernel runs, exact rationals, premises checked first:

```
T(y) = 1 + y/2,  x₀ = 1     fixed point 2     stopping counts n = 0..8:   0,1,2,3,4,5,6,7,8
T(y) = 3 + y/2,  x₀ = 5     fixed point 6     stopping counts n = 0..6:   0,1,2,3,4,5,6
T(y) = y/2,      x₀ = 1     fixed point 0     stopping counts n = 0..5:   0,1,2,3,4,5
```

Three orbits, one program answering for all of them, each inside the domain the theorem actually covers. An earlier draft of this table started the second operator from 0 and the third from 4 — initial gaps 3 and 2, seeds the premise cannot admit — and printed the realizer's output anyway. The output was the same; the certification was not there. That is the difference between a program that runs and a theorem that covers the run, and it is the reason the premise checks now come before the table.

#### The triad

**Realizability:** `∀n ∃N ∀d` promised a function ℕ → ℕ whose output certifies an infinite tail — the statement's shape put the entire convergence rate into the evidence type.

**Extraction:** the rate arrived as a callable stopping rule, derived by an induction that spends the contraction hypothesis at every step; one term serves every ½-contraction because T entered as a function variable, and the while-loop's exit condition is now a corollary, sharp to the boundary and mutation-tested.

**Continuity:** the modulus turned ninety degrees — Post 4 measured fineness in *space* (input precision), this post measures it in *time* (iteration count). Both are the same discipline: an infinite process compressed into a finite, certified demand schedule.

**Next post:** the ladder's biggest step. So far every witness has been a number. Next, the witness is a *function* — an existential at arrow type, where what the proof must hand over is a function bundled with its own continuity certificate. The integral. Including, plainly, the one induction it is still missing.

*Series: From Existence to Algorithm. Source links pinned to commit in the comments.*

---

# From Existence to Algorithm — Post 6
# A Witness That Is a Function

---

## CAPTION

Every witness in this series so far has been a number. A grid index. A modulus. An iteration count.

This post's existential asks for something bigger:

```
∀f ∀j ∀N.  RiemannSum(f,N) is 2ʲ-Lipschitz  →
    ∃G : ℚ→ℚ.  ∀n ∃M ∀x ∀y.
        |x−y| < 2⁻ᴹ  →  |G(x)−G(y)| < 2⁻ⁿ
```

The ∃ sits at **arrow type**. The witness is not a value — it is a *function*, and not a bare one: a function delivered together with its own modulus of continuity. Rule plus modulus, one object. Which, if you've followed since Post 4, is exactly what a constructive analyst means by a real function.

The witness is now the concrete upper-limit Riemann-sum operator, G(x) = S(f, x/N, N) — the finite approximation to ∫₀ˣ f — and the machinery runs, in the kernel, on exact rationals:

∫₀ˣ 1 dt = x, exactly, every tested x
∫₀¹ t dt → 3/8, 7/16, 15/32 for N = 4, 8, 16 — that is (N−1)/2N → ½

And now the part that makes this post different: what is *proved* is not yet everything one would want to prove. The arrow witness is built from the integrator term. What is still assumed is its Lipschitz bound. The missing work is the internal derivation of that bound from usable hypotheses on the integrand — absolute values, division, and finite sums, assembled inside the object language instead of supplied as one premise.

#Lean4 #ConstructiveAnalysis #FormalMethods #ProgramExtraction

---

## ARTICLE

### A Witness That Is a Function

The ladder so far: a number witness (Post 2), a function *input* (Post 3), continuity as data (Post 4), a certificate for an infinite tail (Post 5). One rung remains that changes the type of the game rather than the difficulty: a function **output**. An existential whose witness is itself a function.

This is the rung where the series' three words stop being separate topics. The theorem's statement is an existence claim (realizability), its witness must be handed over as a program (extraction), and the thing handed over is a function that cannot be handed over without its modulus (continuity). All three, in one quantifier.

It is also the rung where I will show you a gap instead of hiding it.

#### The shape: ∃ at arrow type

```
∀f : ℚ → ℚ. ∀j. ∀N.
    RiemannSum(f,N) is 2ʲ-Lipschitz   →
    ∃G : ℚ → ℚ.   ∀n ∃M ∀x ∀y.  |x − y| < 2⁻ᴹ  →  |G(x) − G(y)| < 2⁻ⁿ
```

Read the existential's type. In Post 2, `∃k` asked for a natural number and realizability's evidence was ℕ-valued. Here `∃G` asks for an inhabitant of ℚ → ℚ, so the evidence is function-valued — and the clause after it demands that G come with a working modulus. The realizer of this statement is therefore a *pair*: a function, and the certificate that makes it usable. Post 4's slogan — a function is a rule plus a modulus — has been promoted from methodology to the literal shape of a witness.

That is the strongest structural form in this development, and it is worth saying why before touching integration at all. Constructive analysis cannot traffic in bare function-existence; "there is a G" with no modulus is as uncomputable as "there is a real number" with no approximations. An arrow-type existential done honestly forces the proof to construct the *pair*, and extraction then hands you an object you can immediately compute with, compose, iterate, integrate again. It is what a constructive analyst means by a real function, arriving as one certified package.

#### The witness: the finite upper-limit integral operator

The G this theorem hands over is the upper-limit Riemann-sum operator for f at N subdivisions:

```
G(x) = S(f, x/N, N)
```

built in the object language as an N-step Riemann sum — an honest System T citizen, not an imported oracle. It is the finite approximation to `∫₀ˣ f`, and it *runs*, in the kernel, against exact rationals:

```
∫₀ˣ 1 dt  =  x            exactly, at every tested x
G(0)      =  0            exactly

∫₀¹ t dt, N-step sums:
    N = 4      3/8      = 0.375
    N = 8      7/16     = 0.4375
    N = 16     15/32    = 0.46875
                              →  ½
```

The pattern is (N−1)/2N, marching on the true value ½ from below, every value an exact rational the kernel checked. Constant functions integrate exactly; the identity integrates to the textbook answer in the limit; the machinery computes.

Why should this upper-limit sum be uniformly continuous, with a modulus you could write down? Because the picture is one inequality: |G(x) − G(y)| is an accumulated area over a base of width |x − y|, and a usable bound on the integrand controls the height of that area. In the object language, however, turning that picture into a derivation requires absolute-value rules, rational division equations, and finite-sum bounds. Those are exactly the pieces not yet assembled internally here.

#### What is proved, and what is not — precisely

Here is the state of the formalization, drawn as a line.

**Proved:** the arrow-type theorem above — for every f, j, and N, if the concrete Riemann-sum function `S(f, x/N, N)` satisfies the 2ʲ-Lipschitz premise, the proof hands over that very function as G and packages it with the modulus M(n) = n + j. The existential at arrow type is discharged, kernel-checked, and it passes the series' falsifiability test: a G without a working modulus refutes the claimed M on concrete x, y.

**Not proved:** the internal derivation that this Riemann-sum function satisfies the Lipschitz premise from assumptions on the integrand. The witness is no longer supplied; it is the concrete System T term `riemannUpperSumClosed f N`. What remains supplied is the analytic bound on that term.

The distance between those two states is the strip/sum argument: compare the two upper-limit sums, control the number and size of the contributing strips, and bound the total difference. Formalizing that internally is unglamorous bookkeeping over finite sums, absolute values, and rational division. This is the third appearance of the series' arithmetic boundary: the object language can run the Riemann-sum program and can package a modulus from a Lipschitz premise, but it cannot yet derive that premise for the Riemann-sum term step by step.

Until that derivation lands, the correct sentence — and the one this series will keep using — is: **the finite Riemann-sum integral computes, its arrow witness is real, and its continuity certificate is conditional on the supplied Lipschitz premise.**

Why publish the gap? Because the alternative is worse in every direction. Round after round of this project's audit showed how easy it is to *look* certified — supply a premise, close by reflexivity, collect a theorem that any term satisfies. The falsifiability test from Post 2 exists because of those rounds. A development that states "here is the line, proved on this side, assumed on that side, these named rules between them" is making a checkable claim; a development that blurs the line is making an impression. The kernel's axiom report enforces the first posture, and the whole value of this pipeline is that it *can't* politely blur.

#### The triad

**Realizability:** the existential moved to arrow type, so evidence became a function bundled with its certificate — the interpretation itself dictated that "a real function" means the pair.

**Extraction:** the Riemann-sum integrator runs in the kernel on exact rationals, and the arrow-type theorem is discharged with that integrator as the witness; what extraction does *not* yet certify — the Lipschitz premise for that witness, derived internally rather than supplied — is stated plainly.

**Continuity:** no longer a property or even a datum, but the *content of the witness*: G is admitted to existence only together with its modulus, continuity as the price of being.

**Next post:** the finale, and the payoff for stacking function variables since Post 3. Two theorems from this series meet a differential equation neither was built for — one certifies where its steady state is, the other prices the convergence — and the fact that they compose at all is the argument that this is a small theory, not a pile of examples.

*Series: From Existence to Algorithm. Source links pinned to commit in the comments.*

---

# From Existence to Algorithm — Post 7
# The Composition: A Differential Equation Neither Theorem Was Built For

---

## CAPTION

The finale, and the moment this series was building toward.

Take the ODE ẏ = 1 + y/2 − y. Its steady state is wherever the dynamics stops moving — the fixed point of T(y) = 1 + y/2.

Now watch two earlier theorems meet it:

→ A fixed point satisfies T(y) = y, i.e. y/2 = 1 — a *crossing*. Post 3's solver, the one that never met its function, brackets it: **certified steady state = 2**. Not computed and hoped correct — located by a theorem quantifying over arbitrary F.

→ How expensive is the discrete approach? T is a ½-contraction, so Post 5's stopping rule prices the consecutive-step convergence: the iterates 1, 3/2, 7/4, 15/8, 31/16, … climb toward 2, and the extracted program says when every later gap is below the requested precision.

Neither theorem was built for differential equations. They compose anyway — *because both quantify over functions*. That is the property this series has been stacking since Post 3, and this is what it buys: not a pile of examples, but a small theory whose parts plug into each other.

Closing post: what this toolkit is, what it honestly isn't, the arithmetic boundary in three sightings, and what the kernel says when asked what the named extracted programs depend on.

#Lean4 #ConstructiveMathematics #FormalMethods #NumericalAnalysis

---

## ARTICLE

### The Composition: A Differential Equation Neither Theorem Was Built For

Every series needs a moment where the pieces stop being pieces. This is it.

The ladder so far, one element per rung: a number witness under a falsifiability test (Post 2); the function variable — proofs blind to their function (Post 3); continuity as extractable data (Post 4); a finite certificate for an infinite tail (Post 5); a witness that is itself a function-with-certificate (Post 6). Each post used the previous ones. But *using* is cheap — a textbook uses its earlier chapters. The claim that separates a theory from a pile of examples is stronger: that the parts compose on a problem none of them was designed for.

So here is a problem none of them was designed for.

#### A differential equation

```
ẏ = 1 + y/2 − y
```

A relaxation dynamics: y drifts until the right-hand side vanishes. Two questions any numerical analyst asks of it, in order: **where** is the steady state, and **how fast** do we reach it? Classically the answers are an existence claim and an asymptotic shrug. Watch what the extracted toolkit does instead — with the emphasis on the fact that *nothing new will be proved*. Every move below is an instantiation.

#### Existence, certified by the solver

Discretize it — forward Euler with unit step gives yₙ₊₁ = yₙ + (1 − yₙ/2) = 1 + yₙ/2, so the update map is T(y) = 1 + y/2. A steady state of the equation is a fixed point of T (for any step size, in fact — the fixed point of yₙ + Δt·(1 − yₙ/2) is 2 regardless of Δt). And a fixed point is an equation: T(y) = y, that is, y/2 = 1 — which is a *crossing*, precisely the shape Post 3's theorem eats. Instantiate `fnCrossingD` with F(x) = x·½ and target 1:

```
certified fixed point  =  2
```

Pause on what did the work. The solver was extracted from a proof about an abstract colouring — one-dimensional Sperner, a theorem that does not know what a differential equation is. It accepts F as a function variable, so "the dynamics of an ODE" is just another F to interrogate at finitely many points. The steady state is not computed and then trusted; it is **bracketed by a theorem**, the same one that answered x³ + x = 10 and x² = 2 in Post 3. Existence, with a certificate, from combinatorics.

#### Convergence, priced by the stopping rule

Where is settled; now how fast — and one precision about *what* is being timed. The rate below is the discrete scheme's convergence, the count of Euler steps, not the equation's continuous relaxation time; the steady state coincides exactly, the clock does not. The Euler steps from x₀ = 1:

```
1,  3/2,  7/4,  15/8,  31/16,  …   →   2
```

T is a ½-contraction — so Post 5's theorem applies verbatim — the contraction is checked at the value level on this very operator, the seed gap is 1/2 — and its extracted realizer prices the consecutive-step convergence: precision in, iteration count out, sharp at the boundary (the 1/16-exactly check from Post 5 was run on *this very operator*). Ask when all later update gaps fall below 2⁻ⁿ and the stopping rule answers before the loop starts. The while-loop's exit condition, again — but now in service of a differential equation the theorem never heard of.

#### Why they compose

Two theorems, one ODE, zero new proofs. The location of the steady state certified by one extracted program, the cost of reaching it by another. The reason this works is the single design decision this series has repeated since Post 3:

**both theorems quantify over functions.**

A theorem about *one* function is a fact; it composes with nothing. A theorem with F as a variable is an *interface* — anything of the right type plugs in, including the update map of a dynamics that didn't exist when the theorem was proved. And the extracted realizers inherit the interface: continuous functionals, probing their function arguments at finitely many points, indifferent to where those arguments came from. Composition is not a happy accident here. It is what function-variable quantification purchases, made visible.

That is the argument — the only argument that matters — that this development is a small theory rather than a pile of examples. Examples demonstrate. Interfaces *combine*.

#### What this is, and what it is not

Closing the series honestly means drawing the inventory line in both directions.

**What this is.** A small certified numerical toolkit, derived from proofs rather than written and then verified. Existence theorems whose statements can fail — the falsifiability test of Post 2, applied throughout — whose proofs therefore had to construct something, and whose extracted programs run in the kernel against exact rational arithmetic: a universal bracketed equation solver, moduli of continuity, a sharp stopping rule for every covered ½-contraction, a running Riemann-sum integrator, and today, their composition on an ODE. Several quantify over function variables, which is why they compose.

**What it is not.** A full development of analysis. No general completed real line in the object language used by these posts, no measure theory, no proof here that the contraction gaps equal distance to a completed fixed point. And one arithmetic boundary, tracked openly across the series in three sightings: Post 2's endpoint-colour premise is discharged in `QAnalysis` but not as a new object-level derivation; Post 4's modulus proof uses one scale-conversion rule; Post 6's Riemann-sum witness is built, but its Lipschitz premise is still assumed. One missing capability, three costs, all named. The next real move is a proof, not a demo: derive the Riemann-sum Lipschitz bound internally and the integral's continuity stops being conditional.

**And the audit.** The previous series ended by asking the kernel what the extracted programs depend on, and this one ends the same way, because it is the entire warrant for the word *certified*. The named extracted derivations and running realizers in this series — solver, moduli, stopping rule, arrow-type existential — answer `#print axioms` with the same short list:

```
[propext, Quot.sound]
```

Lean's two foundational axioms, which the rational model's proofs use — and nothing else at the extracted-program layer. The broader soundness and rational-arithmetic discharge layers print larger footprints, including `Classical.choice`, and the repository keeps that split explicit. Read the list above as what it is: the named executable evidence is choice-free, not axiomless and not a claim that every supporting analysis theorem has the same footprint.

#### The triad, one last time

**Realizability** was the constitution: every statement's logical shape fixed its evidence type in advance — number, modulus, stopping rule, function-with-certificate — so the programs were promised before the proofs existed.

**Extraction** kept every promise: the proofs, read at their evidence types, *became* the toolkit, and today two of its members solved a problem neither was written for.

**Continuity** was the physics underneath: realizers probe their infinite inputs finitely, moduli make that finiteness a datum, and composition works because every interface in sight is a continuous functional. It was never a side topic. It is why extracted analysis is possible at all.

From existence to algorithm: an existential that can fail, a proof that must therefore build, a kernel that checks the build, and programs that outlive the theorems they came from. That's the series.

*Series: From Existence to Algorithm — the analysis companion to "How a Proof Becomes a Program." All seven posts, source links pinned to commit, in the comments.*

---
