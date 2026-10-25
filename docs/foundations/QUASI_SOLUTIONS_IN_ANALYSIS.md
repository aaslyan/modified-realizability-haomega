# Quasi-solutions in analysis — a parked line of work

*Note of 2026-10-24, from a discussion with the author. To be resumed after the
closed-universe plan (`docs/CLOSED_UNIVERSE_PLAN.md`) is finished.*

**The question.** The 1997 dissertation (`DISSERTATION_1997.md`) shows that a
recursive equation can have *no* solution and yet a total recursive
**𝔍-quasi-solution**: the equation holds whenever its free variables range over
a restricted class 𝔍 (Theorem 1.3), and testing on a large enough class Σ*
already forces a genuine solution (Theorem 1.4). In analysis the free variables
are reals (times, parameters, initial data) and the unknowns are functions. Do
the same effects occur there — a differential equation with no solution but with
a quasi-solution relative to the computable reals — or does continuity rule
them out?

The idea behind it (the author's): **positive knowledge from the price of a
counterexample.** If every refutation of a candidate needs resources outside a
class C, then against any adversary bounded by C the candidate is as good as a
solution. The "Galois" view: test classes and surviving candidates form an
antitone pair (a Galois connection of the relation "candidate passes test"); the
*price of refutation* of a candidate is the least class containing a
counterexample.

## 1. Where continuity closes the door

If the data are continuous and the requirement is an **equation** — a residual
`u(x) = 0` for all `x` — the failure set `{x : u(x) ≠ 0}` is **open**. A nonempty
open set contains a rational point. So an equation that holds at every computable
real holds at every real: quasi-solutions relative to the computable reals are
genuine solutions. Every program extracted in this repository is continuous
(`extract_tracked`), so this covers all equational specifications here.

## 2. Where the door stays open

Theorem 1.3 places the failure on the infinite paths of a recursive tree: a
**closed** set with no recursive member. Analysis produces closed failure sets
whenever the requirement is a **strict inequality**, a nonvanishing condition or a
division.

- **Positivity.** There is a computable continuous `h` on `[0,1]` whose zero set is
  a nonempty closed (Π⁰₁) set with no computable point (the Kleene-tree
  construction moved to `[0,1]`; effectively closed sets are zero sets of
  computable functions). Then `∀x. h(x) > 0` is false, but true at every
  computable `x`.
- **A differential equation.** `y′ = 1/h(x)`, or any right-hand side singular
  exactly on that set: regular and solvable around every computable point, with
  no global solution. Every refutation needs a noncomputable point — Theorem 1.3
  in analysis.
- **Russian constructive analysis** (Markov school, ∀ over constructive reals) is
  this phenomenon. Zaslavsky–Tseitin singular coverings give functions defined
  and continuous at every constructive real of `[0,1]` that are unbounded, or not
  uniformly continuous. *Reference as recalled, to verify before citing:*
  I. D. Zaslavsky, G. S. Tseitin, "On singular coverings and properties of
  constructive functions connected with them", Trudy MIAN 67 (1962). Chapter 3,
  Example 1 of the dissertation ("the constructivist interpretation of ∀ achieves
  more") belongs here.

## 3. Theorem 1.4 in analysis is a basis theorem

The test class needed before quasi-solutions become solutions depends on the
complexity of the failure set:

| failure set | test class that suffices | result |
|---|---|---|
| open (equations) | rational / computable points | density |
| effectively closed (Π⁰₁) | low (Δ⁰₂) points; computable points do not suffice | low basis theorem (Jockusch–Soare) |
| Σ¹₁ | points recursive in Kleene's 𝒪 (hyperarithmetical points do not suffice) | Kleene / Gandy basis theorems |

The dissertation's Σ* is the top of this scale. Thesis: **the price of a
counterexample is fixed by the topological and descriptive shape of the failure
set.**

## 4. What to build when this is resumed

1. **Open refutation ⇒ computable tests suffice** — a Lean theorem in this
   setting, from the continuity of the extracts. Small; it fixes exactly where
   the door is closed.
2. **A quasi-solution in analysis** — a computable `h` with zero set free of
   computable points, and `y′ = 1/h` on it. Needs a Kleene-tree diagonalization
   against all partial recursive functions; Mathlib has `Nat.Partrec`/`Computable`.
   A real project.
3. **A test-restricted realizability** — a variant of `MR` in which ∀ over
   functions ranges over a class 𝔍 of tests; Example 1 of Chapter 3 becomes a
   theorem about the gap between the restricted and the full quantifier.

**Caution (the author's remark): 𝔍-quasi-solutions are probably not Markov's
constructive functions, and the conclusions may differ.** In the dissertation the
candidate `f*` is a fixed *total* function and only the *tests* are restricted.
A Markov-school constructive function acts on *codes* of constructive reals and
exists only on them; its theory has its own theorems (Tseitin's continuity
theorem, non-extendability via singular coverings). Section 2's last bullet and
item 3 should therefore be read as an analogy to be checked, not an
identification. Settling the relation between the three notions is itself a
question for this line of work: (a) total candidate, restricted tests; (b)
Markov functions on constructive reals; (c) Kleene–Kreisel continuous
functionals, the semantics of this repository's extracts.

Distinct from the existing `GaloisAdjunction.lean` / `GaloisAdequacy.lean`, which
relate *representations* to the *theorems* they support; this line relates *test
classes* to the *candidates* that survive them.
