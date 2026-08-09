# The Hydra project

A self-contained account of Phases H1–H9: the Kirby–Paris Hydra theorem,
proved twice — once inside the fragment, once in the metatheory — with a
program extracted from the first proof and a trace you can read.

docs/first-order/STATUS.md remains the authoritative per-phase record with the full
rationale and every flagged deviation; this file is the map.  Everything
below is checkable against the Lean source, and §7 reproduces it from a
clean build.

---

## 1. What is proved

**Inside the fragment** (`HydraTheorem.lean`, Phase H5):

```
hydraTheorem : Deriv [] (∀h ∃t. hydra(h, t) = 0)
```

A closed derivation of the fragment's own natural deduction.  The
quantifier ranges over all natural numbers, which by H1's bijection is all
finite rooted trees; `hydra(h,t)` is the state after `t` moves of the
Kirby–Paris battle from the tree coded `h`; and `= 0` is "the hydra is a
bare head", because the coding sends the dead hydra to `0` and nothing
else.  The witness is unbounded.

**In the metatheory** (`HydraGeneral.lean`, Phase H7):

```
hercules_wins : WellFounded PlayRel
```

The legal-move relation is well-founded: **every** play from **every**
hydra is finite — whatever head Hercules chops at each step, and however
many heads grow back.  With `play_stuck_iff_leaf` ("the only position with
no legal move is the bare head") this is the full "every hydra dies" half
of Kirby–Paris.

**As a program** (`HydraExtraction.lean`, Phase H6):

```
hydraBattleLength      : ℕ → ℕ
hydraBattleLength_spec : ∀ h, hydraSeqN h (hydraBattleLength h) = 0
```

Modified realizability turns the H5 derivation into a function, because
the realizer of an existential carries its witness.  The spec comes from
`soundness`, not from computation, so it holds at trees no evaluator will
reach.  Generic continuity applies with no per-derivation certificate, and
the extract has a class in `CtQ 2`.

### Why the theorem is proved twice

The fragment is first-order with one sort.  A strategy is a function
`ℕ → (which head)` and a schedule is a function `ℕ → ℕ`, so "for every
play" is **not expressible in it at any length**.  H5 therefore names one
battle — leftmost head, `s + 1` copies at step `s`, which is Kirby–Paris's
own schedule — and H7 proves the strategy-free statement where it can
live.  `hydraStep_play` closes the loop: the fragment's battle is one of
H7's plays, so the two results are about the same game.

---

## 2. What is assumed

Exactly one mathematical fact is imported into the fragment
(`Deriv.hordCutLt`, Phase H4):

> from `c ≠ 0`, `hord(hcut(n,c)) ≺ hord(c)` — a move on a live hydra
> strictly decreases its ordinal.

Its Lean twin is `olt_ordOfHydraN_step`, i.e. H3's `cutH_descends` read on
codes.  The schema follows the pattern Phase D5 established for the
Goodstein layer's `ordPredLt`: it is a property of **one** move symbol
relative to **one** ordinal symbol, it says nothing about the battle (no
sequence, no step counter, no schedule), and it quantifies over the
replication factor.

Three other schemas are added but assume nothing: `hydraZero`/`hydraSucc`
are the battle's recursion equations, and `hcutNum` is the move's numeral
graph — present for the same reason `bump` and `prec` have one, namely
that tree surgery through the decoding is course-of-values recursion
rather than a first-order equation schema.  Plus three congruences.

**The import is checked to be faithful.**  `hydra_descent_via_fragment`
reads `hordCutLt` back through `soundness` and recovers exactly H3's
theorem — not a weaker or differently-quantified statement.

**What is not claimed**: that the fragment proves `hordCutLt`.  Like the
Goodstein layer's three schemas it is an axiom of the object theory
justified by a Lean theorem.  Internalizing it would mean formalizing tree
surgery and Cantor normal forms inside an equations-only first-order
language — strictly harder than the Goodstein internalization that D5
scoped as research-scale and declined.  docs/internal/QUESTIONS.md item 13 records the
fork and the recommendation.

---

## 3. What is out of scope

**Independence from Peano arithmetic is not formalized and is not
claimed.**  Kirby–Paris has two halves — every hydra dies, and PA cannot
prove it — and only the first is here.  The second needs a model-theoretic
or proof-theoretic argument about PA itself (indicators, or the
`ε₀`-ordinal analysis), for which this development has no machinery.

Also not verified, and so not quoted anywhere: `Hydra(4) >` Graham's
number, and the `f_α` growth-rate bounds.

---

## 4. The phases

| Phase | File | What it delivers |
|---|---|---|
| H1 | `Hydra.lean` | Finite rooted trees as natural numbers, **both round trips proved** |
| H2 | `Hydra.lean` | The Kirby–Paris move `cutH`, the battle `hydraSeqN`, the published lengths |
| H3 | `Hydra.lean` | The ordinal assignment and **`cutH_descends`** |
| H4 | `HydraFragment.lean` | The three symbols and their schemas; the fragment computes battles |
| H5 | `HydraTheorem.lean` | **`hydraTheorem`** — termination as a closed derivation |
| H6 | `HydraExtraction.lean` | The extracted battle-length program, certified and running |
| H7 | `HydraGeneral.lean` | **`hercules_wins`** — every play, every strategy, every schedule |
| H8 | `HydraDisplay.lean` | The battle on trees (98 s → <1 s), and the trace |
| H9 | `HydraStrategies.lean` | A second strategy (rightmost head), covered by H7 for free |

### H1 — trees as numbers

A hydra is a mutual `Hydra`/`Forest` pair rather than the nested
`Hydra := List Hydra`, because the encode/decode proofs are mutual
structural recursions and nested inductives make those fight the recursor.
The coding goes through Phase C's hand-rolled triangular pairing — no new
coding primitive, and deliberately not Mathlib's `Nat.pair`, whose entire
lemma set is choice-dependent and whose `unpair` does not reduce in the
kernel.

    ⌜nil⌝ = 0    ⌜cons h f⌝ = ⟪⌜h⌝, ⌜f⌝⟫ + 1    ⌜node f⌝ = ⌜f⌝

Both round trips are proved (`encodeF_forestOf`, `hydraOf_encodeH`), which
is what makes "the fragment's `∀h` ranges over exactly the hydras" exact
rather than approximate, and what lets `= 0` serve as the termination
test with no side condition.

### H2 — the move, and pinning down *which* game

Chop a head; if its parent is not the root, the grandparent grows `n`
copies of the modified parent.  Two parameters are left to the caller
deliberately: which head (here: the leftmost) and how many copies.

There are two different games in circulation and they are widely
conflated.  The "simple" one attaches copies as bare leaves at the parent
and gives path-hydra battle lengths `1, 3, 11`.  Kirby–Paris is the
grandparent rule with the whole post-cut subtree copied, and gives
`1, 3, 37`.  **`37` is the discriminating number**, and since H8 it is
`#guard`ed at every build.

Convention pinned, since the literature shifts it: `hydraSeqN` grows
`s + 1` copies at step `s`, i.e. round numbering from 1 — the same as
Castéran's Coq development.  Note that our `cutH` takes the copy count as
a *parameter*, so the descent theorem covers adversarial replication; that
generalization belongs to the later literature and to Castéran, and must
not be attributed to Kirby–Paris 1982.

### H3 — the measure that falls while the tree grows

`ord(node [c₁,…,cₖ])` is the Cantor normal form of
`ω^{ord c₁} ⊕ … ⊕ ω^{ord cₖ}`, built on Phase C's notation codes via
`insertExp` (the CNF sum), with `nfB_ordOfHydra` proving it lands in
normal form — the precondition for any descent statement at all.

`cutH_descends`: every legal move strictly decreases it, at every
replication factor.  Three cases, which are `cutH`'s own:

* a head hanging off this node — `precB_insertExp_self`;
* a deeper cut with no regrowth here — `precB_insertExp_mono_exp`;
* a deeper cut where this node is the grandparent and `n` copies grow —
  `precB_insertIter_lt`, **which is insensitive to `n`**, so the case
  closes without ever looking at how many copies appeared.

Getting there required three order facts `Epsilon0.lean` had never needed,
because Goodstein's descent only ever compared notations built to be
related: trichotomy, transitivity, and asymmetry of `≺` on normal forms.

### H4 — into the fragment

Three symbols — `hcut n c` (one move), `hydra s t` (the battle), `hord c`
(the ordinal) — evaluated by H1–H3's functions.  This moved `Hydra.lean`
before `Syntax.lean` in the import chain, next to `OrdinalAssignment.lean`
and for the same reason: `Term.eval` mentions those functions, so they sit
inside `extract`.

That imposes a constraint, checked rather than assumed: **the definitions
must stay choice-free and kernel-computable.**  `#print axioms` on
`hydraStepN`, `hydraSeqN` and `ordOfHydraN` reports *does not depend on
any axioms*; had any of them acquired `Classical.choice`, every continuity
theorem's `[propext, Quot.sound]` budget would have broken at once.  (The
*proofs* in `Hydra.lean` are unconstrained — they reach only `soundness`,
whose budget allows choice.)

`hydraComputeDeriv` derives the numeral of every state of every concrete
battle, so the fragment computes `2 → 3 → 1 → 0` rather than only
reasoning about it.

### H5 — the theorem

`tiEps0` along `≺`, on

    φ(x) := ∀s. hord(hydra(h,s)) = x → ∃t. hydra(h,t) = 0

with `h` a parameter quantified only at the end.  Either the hydra is
already dead and `t := s` witnesses, or the next state's ordinal is `≺ x`
and the induction hypothesis supplies the witness.

This is `GoodsteinTheorem.lean` line for line, **including the naming
step**: the induction hypothesis cannot be instantiated at
`hord(hydra(h,s+1))`, because that term mentions `s`, which φ binds, and
the fragment's substitution is naive rather than capture-avoiding.  So the
derivation proves `∀z. z = hord(hydra(h,s+1)) → …` first and instantiates
at the *variable*.  That the D2 technique transferred unmodified is
evidence it is the right general device for naive-substitution calculi
rather than a Goodstein-specific trick.

The only Hydra-specific part is `hydraDescentDeriv` — three lines gluing
`hordCutLt` to the recursion equation `hydraSucc` by congruence of `hord`.

### H6 — the program

`derivBound hydraTheorem = 12`, the same as `goodsteinTheorem`'s, since
the derivations have the same shape.  `hydraBattleLength` reads the
witness off the realizer at that ambient level.  It runs at the small
trees (`0 → 0`, `1 → 1`, both cross-checked against `hydraSeqN` by `rfl`).

**Code 2 does not finish** (no output at 600 s).  The distinction matters
and is unambiguous: the answer is `3`, and `hydraSeqN` computes the battle
`2 → 3 → 1 → 0` instantly.  What is astronomical is only the extract's
re-evaluation count, for the cause Phase D4 diagnosed and did not fix —
every recursive value passes through two `dropR` transports and
`app₁`/`abs₁` duplicate their argument, so recursive calls are
re-evaluated exponentially often, with nothing memoized.  The Hydra layer
inherits that bottleneck and adds none of its own.

### H7 — every play

`Play n h h'` is the legal-move relation with nothing selecting which head
is chopped.  Each of its five constructors maps to one lemma H3 already
had, so the phase cost nothing new mathematically.

One observation it did add: the two "later sibling" constructors consume
`precB_insertExp_mono` — the *hard* lemma of H3, the one that needed
transitivity and asymmetry first, and the one `cutH_descends` never used.
Chopping the leftmost head is exactly the case where it can be avoided.
The effort H3 spent on it was not incidental; it is what the general
theorem runs on.

`play_two_choices` is the non-vacuity check: a hydra from which two
*different* legal moves lead to two *different* hydras at the same `n`,
the second being one `cutH` would never make.  Without it the relation
could have described only the leftmost strategy and `hercules_wins` would
have restated H3.

### H8 — running it, and seeing it

`battleLen` ran the battle on **codes** — decode, cut, re-encode, every
step — which made `Hydra(3) = 37` take ≈ 98 s.  The earlier diagnosis
blamed the pairing; that was wrong, and H2 had already made `tri`
constant-time and `unTri` logarithmic.  The real cause is that hydra codes
grow *doubly* exponentially (`⟪a,b⟫ ≈ (a+b)²/2`, so each nesting level
squares the magnitude) and this battle reaches 20-node trees.

`battleLenH` runs the same battle directly on trees: **98 s → under 1 s**,
with `battleLen_eq_battleLenH` proving the two agree at every fuel, stage
and code.  So all three published lengths are `#guard`ed at every build.

### H9 — a second strategy, for free

The test of whether H7 bought anything: a general theorem that cannot be
applied to a second instance without redoing the work is not general.

`cutRightF` chops the **rightmost** head instead of the leftmost, same
grandparent regrowth, same replication parameter.  `rightStep_play` shows
each of its moves is one of H7's plays, and then

    rightStep_descends := play_descends (rightStep_play …)

is the whole descent proof — one line, against H3's three-case induction
over the tree consuming three separate ordinal lemmas.  Termination
follows the same way, from `no_infinite_play`.

The two strategies are genuinely different: after three moves on the
4-node path the leftmost is at `(o o o o (o) (o))` and the rightmost at
`((o) (o) o o o o)` (`#guard`ed to differ).  The path hydras are the right
test precisely because they *start* as chains, where the strategies agree;
they diverge as soon as the first regrowth branches the tree — and both
still reach the bare head after exactly 37 moves, also `#guard`ed.

Stated carefully: strategy-independence of the battle *length* is a known
result and is **not proved here**.  What is proved is that both strategies
terminate; what is checked is that their lengths agree at the three
published instances.  docs/first-order/STATUS.md previously reported that agreement on the
authority of a research pass — the build now checks it.

---

## 5. The picture

`battleTrace` prints each state in bracket notation with its ordinal.  The
first ten of the thirty-eight states of the 4-node path, verbatim from the
build log:

```
(((o)))                    [ω^ω]
((o o))                    [ω^2]
((o) (o) (o))              [ω·3]
(o o o o (o) (o))          [ω·2 + 4]
(o o o (o) (o))            [ω·2 + 3]
(o o (o) (o))              [ω·2 + 2]
(o (o) (o))                [ω·2 + 1]
((o) (o))                  [ω·2]
(o o o o o o o o o (o))    [ω + 9]
(o o o o o o o o (o))      [ω + 8]
```

Read the columns against each other: the bracket string gets longer, the
ordinal gets smaller, on every line.  The same battle as node counts:

```
4, 4, 7, 9, 8, 7, 6, 5, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 20, 19, …, 2, 1
```

It peaks at 20 — five times its starting size — before it dies.  Note that
the *ordinal* codes stay tiny throughout while the *tree* codes explode,
which is exactly why nothing that only needs the tree should touch codes.

`descendsAlong` checks the descent step by step along this battle and is
`#guard`ed.  That is a demonstration, not a proof: the proofs are
`cutH_descends` (every hydra, every factor) and `hercules_wins` (every
play).  What it adds is that the thing proved and the thing computed are
visibly the same thing.

---

## 6. Axiom budgets

Checked at every build by embedded `#print axioms`.

```
'Realizability.hydraStepN'                       … does not depend on any axioms
'Realizability.hydraSeqN'                        … does not depend on any axioms
'Realizability.ordOfHydraN'                      … does not depend on any axioms
'Realizability.hydraOf_encodeH'                  … [propext, Quot.sound]
'Realizability.cutH_descends'                    … [propext, Quot.sound]
'Realizability.hydraTheorem'                     … [propext, Quot.sound]
'Realizability.hydra_descent_via_fragment'       … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_theorem_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_theorem_extract_continuous' … [propext, Quot.sound]
'Realizability.hydraBattleLength_spec'           … [propext, Classical.choice, Quot.sound]
'Realizability.hydra_extract_continuous'         … [propext, Quot.sound]
'Realizability.play_descends'                    … [propext, Quot.sound]
'Realizability.hercules_wins'                    … [propext, Quot.sound]
'Realizability.no_infinite_play'                 … [propext, Quot.sound]
'Realizability.play_stuck_iff_leaf'              … [propext]
'Realizability.hydraStep_play'                   … [propext]
'Realizability.battleLen_eq_battleLenH'          … [propext, Quot.sound]
'Realizability.play_two_choices'                 … does not depend on any axioms
'Realizability.rightStep_play'                   … [propext]
'Realizability.rightStep_descends'               … [propext, Quot.sound]
'Realizability.no_infinite_right_battle'         … [propext, Quot.sound]
```

Adding three symbols and seven rules to the fragment cost **nothing** in
axiom footprint, because the value-level functions are choice-free and the
schemas are contentless.  The whole H7 layer is `Classical`-free too.

---

## 7. Reproducing it

```bash
lake build     # prints every #print axioms result, every #eval, and runs every #guard
```

The `#guard`s fail the build if the battle lengths or the step-by-step
descent ever stop holding, so `Hydra(3) = 37` is verified rather than
asserted.  To check the headline claims individually:

```bash
cat > /tmp/hcheck.lean <<'EOF'
import Realizability.HydraExtraction
import Realizability.HydraGeneral
namespace Realizability

-- H5: the theorem, at exactly the claimed type
#check (hydraTheorem :
  Deriv [] (Formula.all 2 (Formula.ex 4
    (Formula.eq (Term.hydra (Term.var 2) (Term.var 4)) Term.zero))))

-- H7: the strategy-free statement
#check (hercules_wins : WellFounded PlayRel)

-- H4: the value-level functions are choice-free (they sit inside `extract`)
#print axioms hydraStepN
#print axioms hydraSeqN
#print axioms ordOfHydraN

-- H1/H3: the coding is a bijection; the descent is general
#print axioms hydraOf_encodeH
#print axioms cutH_descends

-- H4/H5/H6: the import is faithful, the theorem, the program
#print axioms hydra_descent_via_fragment
#print axioms hydraTheorem
#print axioms hydraBattleLength_spec

-- H6: the extracted function, running
#eval hydraBattleLength 0                     -- 0    (a few s)
#eval hydraBattleLength 1                     -- 1    (a few s)
-- #eval hydraBattleLength 2                  -- does NOT finish; see §4, H6
end Realizability
EOF
lake env lean /tmp/hcheck.lean
```

Lean *displays* `hydraTheorem : Deriv [] hydraGoal`, but the ascription in
the `#check` is the spelled-out `Formula.ex 4 (Formula.eq (Term.hydra …) …)`,
so what was checked is the unfolded type.

---

## 8. Sources

* Kirby & Paris, *Accessible independence results for Peano arithmetic*,
  Bull. LMS 14 (1982), 285–293.  A scan with a text layer is at
  `cs.tau.ac.il/~nachumd/term/Kirbyparis.pdf`.
* Castéran's Coq development, `rocq-community.org/hydra-battles/`.  Its
  §2.0.1 states the rule as "`h′` is replaced by `n + 1` copies of `h′`
  which share the same root", with the replication factor equal to the
  round index — the same rule as ours.
* Dershowitz & Moser, *The Hydra Battle Revisited*, which records
  explicitly that it shifts the factor by one relative to the original —
  which is why the convention is pinned above rather than assumed.

Citations name only what was actually checked.  The `f_α` growth-rate
bounds and `Hydra(4) >` Graham's number are asserted by the wikis and are
**not** verified here, so they are not used anywhere in the development.
