# HAomega fact dossier

**Scope:** the `HAomega/` library of `modified-realizability-haomega`,
branch `haomega`, at commit `e7f4483` (+ the fixes this dossier mandated).
**Standard:** every claim below traces to a build result or a direct source
read, tagged `[run]` (executed this audit, 2026-08-08), `[src]` (read from
source), or `[git]` (from history).  Where verification was not done, that
is stated.

---

## 1. The evaluation-wall contradiction — RESOLVED BY EXECUTION

`Fib.lean` simultaneously claimed a stack overflow "at about `n = 28`" and
guarded `fibExtracted 100` / `fibExtracted 1000`.  Direct evaluation `[run]`:

    fibExtracted 26 = 121393     (instant)
    fibExtracted 27 = 196418     (instant)
    fibExtracted 28 = 317811     (instant)
    fibExtracted 100 = 354224848179261915075
    fibExtracted 1000 % 1000000007 = 517691607

**There is no wall at any of these inputs.**  The resolution is *not* two
call paths: it is a stale comment.  `[src]` `fibStep` today uses the
primitive `.add` (interpreted by `Nat.add`); the overflow diagnosis described
an earlier `fibStep` built on `Tm.addT`, the *defined* unary addition
(`x + y` in `y` recursor steps, hence `Θ(fib n)` frames).  `[git]` both
versions are inside the squashed initial commit `c4a1efa`; the comment
predates the primitive-`+` change within that session and was left behind.
**Fix applied:** the comment is now a historical note stating current
verified behavior.

## 2. The Hydra fragment/metatheorem boundary — PARTIALLY closed since the
first audit pass

At the first pass (commit `3f2b422`): no declaration stated any
strategy-quantified theorem; `HAOMEGA.md`'s "dissolves" row was corrected to
"expressible, not derived."

**Since then** (`63d9e95`, same audit day): `HAomega/Hercules.lean` derives

    herculesD : ∀h. ∀f^(ℕ→ℕ). ∃t. play(f, h, t) = 0        [src, run]

where `play f h t` iterates `hcut` with **replication factor `f s` at step
`s`** — a genuine ∀ over strategies, unstatable first-order.  `[src]` two
design facts: `play` is a *term* (`recNat h (λs ih. hcut (f s) ih) t` — no
new primitive, no new eval/soundness/tracking cases), and the descent needs
*no new import* (`hordCutLt` was already term-general in its replication
argument).

**Precise remaining gap (as of the audit):** the head choice stayed the
value layer's (leftmost).  **Addendum (2026-08-09): the gap is closed.**
`HydraSurgery.lean` supplies the computable tree-surgery move (`moveF` /
`playAtN`, axiom-free — `cutH` with a position argument) with its descent
`olt_ordOfHydraN_playAt` = H7's `play_descends` on codes; the `hcutAt`
primitive and the `hordCutAtLt` schema thread it through all case sites; and
`HerculesAny.lean` derives `herculesAnyD : ∀h ∀f ∀g. ∃t. playAt(g,f,h,t) = 0`
at `[propext, Quot.sound]`.  `[run]`: `herculesAnyX` agrees with `herculesX`
(hence `hydraX`) at the leftmost head strategy `g = 0` on codes 0–2, and
distinct-head battles are certified terminal by the reference `playAtRef`;
745 jobs green.  `[run]` extract checks: `herculesX (·+1)` on codes 0–2 =
`[0,1,3]` (agrees with `hydraX` at the fragment's own strategy);
`herculesX (fun _ ↦ 1)/(fun _ ↦ 9)` on codes 0–1 = `[0,1,1]` with `playRef`
terminal certificates; `herculesX (fun _ ↦ 1) 2` **stack-overflows** — the
doubly-exponential tree coding, the same mechanism as `hydraX 4`/`7` in §5.
(The neighboring `bump`-row also overclaimed "definable in System T": the
numeral-graph *schemas* are gone, but the symbols were kept **primitive**
over the proven first-order value layer; fixed likewise.)

## 3. Theorem statements, verbatim `[src]`

`HAomega/Fib.lean`:

    def fibSpec : Formula [] (.arrow .nat (.prod .nat .unit)) :=
      .all .nat (.ex .nat (.eq (.var .here) (.app fibT (.var (.there .here)))))
    def fibDeriv : Deriv Ctx.nil fibSpec := by
      refine Deriv.allI ?_
      exact Deriv.exI (.app fibT (.var .here)) (Deriv.eqRefl _)

`HAomega/Goodstein.lean` (line 124):

    def goodsteinD {Γ as : List Ty} {Δ : Ctx Γ as} :
        Deriv Δ (.all .nat (.ex .nat
          (.eq (.good (.var (.there .here)) (.var .here)) .zero)))

`HAomega/Hydra.lean` (line 103):

    def hydraD {Γ as : List Ty} {Δ : Ctx Γ as} :
        Deriv Δ (.all .nat (.ex .nat
          (.eq (.hydra (.var (.there .here)) (.var .here)) .zero)))

Both `tiEps0` theorems are ∀∃ equations over the primitive symbols; neither
claims independence from PA, and `Hydra.lean` disclaims it explicitly.

## 4. Axiom footprints, run fresh `[run]`

    'HAomega.Tm.eval'               [propext, Quot.sound]
    'HAomega.extract'               (no axioms)
    'HAomega.soundness'             [propext, Classical.choice, Quot.sound]
    'HAomega.eval_tracked'          [propext, Quot.sound]
    'HAomega.extract_tracked'       [propext, Quot.sound]
    'HAomega.extract_continuous2'   [propext, Quot.sound]
    'HAomega.hiProgram_continuous'  [propext, Quot.sound]
    'HAomega.fibRealizer'           (no axioms)
    'HAomega.goodsteinD'            [propext, Quot.sound]
    'HAomega.goodsteinX'            [propext, Quot.sound]
    'HAomega.hydraD'                [propext, Quot.sound]
    'HAomega.hydraX'                [propext, Quot.sound]

Two corrections to earlier claims, both now fixed in `HAOMEGA.md`:

* **Continuity is `[propext, Quot.sound]`, not `[propext]`.**  The tighter
  footprint held before `tiRec`; its tracking case uses `oLt_wf`
  (well-foundedness), which brings `Quot.sound`.  Still **choice-free**,
  matching the first-order continuity invariant.
* **`soundness` carries `Classical.choice`.**  Introduced with the
  Goodstein/Hydra rules, whose cases discharge by `OrdinalAssignment` /
  `Hydra` value-layer *theorem proofs* (choice-using, per Mathlib), while
  the value-layer *definitions* stay choice-free — the same split, with the
  same footprint, as the first-order `soundness`.  Derivations and running
  extracts (`goodsteinD/X`, `hydraD/X`) remain choice-free.

## 5. Evaluation limits, measured `[run]`

* `goodsteinX`: `(0,1,3,5)` for `m = 0..3` in ~2 s total.  `m = 4`: no
  result within a 60 s timeout (no crash); the true stopping time is
  astronomical, so this is cost, not overflow.  First-order comparison: its
  certified extract evaluates only `m = 0,1` (session-verified previously).
* `hydraX`: `(0,1,3)` for codes `0..2` (guarded), and — beyond the guards —
  `hydraX 3 = 2`, `hydraX 5 = 4`, `hydraX 6 = 5`, each ≤1 s.  Codes `4`
  and `7`: **`Stack overflow detected. Aborting.` (exit 134)** within ~2 s.
  So the boundary is not a prefix of codes: it evaluates wherever the coded
  tree/battle stays shallow and dies by interpreter stack depth on codes 4
  and 7.  The overflow is in evaluating the value-layer tree coding, a
  different mechanism from the first-order wall (ambient-tower cost), which
  stopped that extract past code 1.

## 6. Hygiene `[run]`

* `lake build`: **743 jobs, success** (re-verified after
  `Hercules.lean`/`Sperner.lean` landed).  *Addendum 2026-08-09: 745 jobs
  after `HydraSurgery.lean`/`HerculesAny.lean`.*
* `wc -l HAomega/*.lean`: **5,454 lines** (23 files, after
  `Hercules.lean`/`Sperner.lean`; first-pass figure was 5,067/21).
  *Addendum 2026-08-09: 6,008 lines, 28 files.*
* `grep -rnw sorry HAomega/ --include=*.lean` → no matches (exit 1);
  same for `admit`.

## 7. `ShowAll.lean` / `EXTRACTED_HAOMEGA.md` `[src]/[run]`

`ShowAll.lean` names the realizers (`R1`–`R7` at audit time; `R1`–`R10`
since the Sperner/Hercules/any-head extensions), renders each three
ways (raw `pretty`, collapsed `pretty'`, Haskell `EmitHaskell.hsTm`) and
**writes `EXTRACTED_HAOMEGA.md` as a build side effect** (an `#eval
IO.FS.writeFile` — worth knowing: every build regenerates the file).  The
generated file has 7 sections, 72,658 bytes; collapsed sizes measured:
fib 109, fib-hi 118, pascal 792, hanoi 1,881, **gcd 13,936**, goodstein
1,088, hydra 1,059 chars.  Nothing in either file contradicts the facts
above; the Haskell views are labeled as uncertified translations in both.

## 8. Sperner 1D — added after the first pass `[src, run]`

    spernerD : ∀n ∀c^(ℕ→ℕ). c 0 = 0 → c n = 1 → ∃k. k < n ∧ c k ≠ c (k+1)

Colorings are function variables — no `look` symbol, no coding (`[src]`
`Sperner.lean`; the first-order S1 needed `look`, its one forced symbol).
Axioms `[run]`: `spernerD`, `spernerX` both `[propext, Quot.sound]`.

**Finding — the extract returns the *last* crossing** where first-order S1
returns the first: `[run]` measured witnesses on the five test colorings are
`[2, 1, 3, 2, 4]` (e.g. `[0,1,0,1] ↦ 2`, not `0`), each a certified
crossing.  Cause `[src]`: this proof's step decides `eqDec (c (m+1)) 0`
*before* consulting the invariant, so a fresh zero re-enters the left
disjunct and discards the crossing found; the first-order proof consults the
invariant first.  Same theorem, different proof, measurably different
program — recorded in `Sperner.lean`'s header as a demonstration that
extraction is faithful to proof structure.

## 9. Axiom footprints for the additions, run fresh `[run]`

    'HAomega.hercAuxD'   [propext, Quot.sound]
    'HAomega.herculesD'  [propext, Quot.sound]
    'HAomega.herculesX'  [propext, Quot.sound]
    'HAomega.spernerD'   [propext, Quot.sound]
    'HAomega.spernerX'   [propext, Quot.sound]

## 11. The typed ordinal layer (addendum, 2026-08-09)

`[src]` `HAomega/OrdCnf.lean` replaces the coded ε₀-notations with an
inductive type for the object language's new base type `.ord`:

    inductive Eps0 | zero | node : Eps0 → ℕ → Eps0 → Eps0     -- ω^e·(c+1) + r

Comparison `olt` and normal form `nf` are structural (pattern matching, no
decoding).  `toCode : Eps0 → ℕ` exists **only in proofs**: `toCode_olt` /
`toCode_nf` show the structural operations compute `precB` / `nfB`, and
`oLtE_wf` is the certified `oLt_wf` pulled back along it — so no new descent
argument, and no coding in any computation.  `ordE` mirrors `ordOf`
constructor for constructor (`toCode_ordE`), and the two new schemas
`ordEBump` / `ordEPredLt` are discharged by `ordE_bumpN` /
`oltE_ordE_of_lt`, themselves the first-order theorems read through
`toCode`. **No new mathematical import.**

`[run]` footprints: `ordE`, `Eps0.oltNE` — *no axioms*; `Eps0.oLtE_wf`,
`goodAuxOD`, `goodsteinOD`, `goodsteinOX` — `[propext, Quot.sound]`.

`[run]` `GoodsteinTyped.lean` re-proves Goodstein by `tiEps0O`:
`goodsteinOX 0..3 = [0,1,3,5]`, each certified terminal
(`goodN m (goodsteinOX m) = 0`), and **build-guarded equal to `goodsteinX`**
at every input evaluated. Inspection of the extract `[run]`: **0** occurrences
of coded `ord(`, coded `≺`, coded `tiRec[`; 2 × `ordᵒ(` and 1 × `tiRecᵒ[`.

`[run]` Representation size — the payoff, measured:

    n         code (decimal digits)   tree (nodes)
    10                3                   13
    1000          1,412                   67
    100000        1,782                   83

`[run]` **Not** a speed claim: 20 runs of `goodsteinX 3` took 9 ms against 7
ms for `goodsteinOX 3` (noise), and 50 structural comparisons at `n ≈ 10⁴`
and 50 coded ones both completed instantly when timed individually. An
earlier `foldl` benchmark that appeared to show a coded-side timeout **did
not reproduce** and is not claimed.

`[run]` Hygiene after the layer: `lake build` **747 jobs**, 6,664 lines,
30 files, zero `HAomega/` warnings.

## 12. The typed hydra layer (addendum, 2026-08-09)

`[src]` `HAomega/HydraTyped.lean` + `HAomega/HydraTree.lean` remove the last
coding from the Hydra pipeline.  `Realizability.Signature.Hydra` already had
hydras as an inductive `Hydra`/`Forest` pair and H7 already proved the descent
*about trees*; what was coded was only the `Tm.eval` interface.  Now:

* base type `.hyd` with `Ty.interp .hyd = Hydra`; symbols `cutᴴ` (`hydraStep`),
  `deadᴴ?` (`isLeafN`, ℕ-valued so the case split reuses the numeric `eqDec`),
  and `hordᴴ` — whose result type is **`.ord`**, so state and measure are both
  structural;
* `ordEOfHydra : Hydra → Eps0` mirrors `ordOfHydra` constructor for
  constructor; `Eps0.insert` is `insertExp` **with the fuel gone** (the coded
  version is fueled on `oR c < c`, an arithmetic fact about the decoding;
  structurally it is plain recursion);
* `toCode_insert` / `toCode_ordEOfHydra` align the two, and the descent
  `oltE_ordEOfHydra_step` is H7's `play_descends ∘ hydraStep_play` with **no
  coding round trip** (the coded `olt_ordOfHydraN_step` needs
  `hydraOf_encodeH`);
* **one** new rule, `hordCutLtH`, against the coded version's three — the
  battle is a *term* (`hplayT`, `recNat`-based, as in `Hercules.lean`), so the
  recursor's own conversion rules replace `convHydraZero`/`convHydraSucc`.

`[run]` footprints: `ordEOfHydra`, `Eps0.insert`, `isLeafN` — *no axioms*;
`hydAuxHD`, `hydraHD`, `hydraHX` — `[propext, Quot.sound]`.

`[run]` **The wall moves — the headline.**  Extract inspection: **0**
occurrences of coded `hcut(`, `hydra(`, `hord `, `≺`, `tiRec[`; 7 × `cutᴴ(`,
2 × `hordᴴ `, 1 × `tiRecᵒ[`.  Battle lengths from trees:

    hydra code   0   1   2   3    4    5   6    7
    hydraHX      0   1   3   2   37    4   5   13
    hydraX       0   1   3   2   ✗overflow  ✗overflow   (codes 4, 7)

Code 4 is the hydra whose **published Kirby–Paris length is 37** — the
extracted program computes it where the coded extract cannot take a step.
Both witnesses are guarded terminal (`isLeafN (hplayRef …) = 0`), and a
guard runs the program on a tree written out directly, with no code involved.

`[run]` Hygiene after the layer: `lake build` **749 jobs**, 7,130 lines,
32 files, 44 rules, zero `HAomega/` warnings; `EXTRACTED_HAOMEGA.md` renders
twelve realizers.

`[src]` **Still coded:** Hanoi's move sequences (`hcons` lists). Nothing else.

## 10. Fixes applied by this audit

1. `Fib.lean`: stale wall-diagnosis comment → historical note with the
   verified current behavior.
2. `HAOMEGA.md`: Hydra "dissolves" row → "expressible, not derived";
   `bump`-row "definable" → "schemas gone, symbols primitive"; the Status
   section rewritten to the then-current, evidence-backed state (741 jobs and
   seven case studies at the time of that audit; 743 and nine after
   Sperner/Hercules landed — §8/§9; 745 and ten after the any-head
   closure); "What is next" refreshed.
