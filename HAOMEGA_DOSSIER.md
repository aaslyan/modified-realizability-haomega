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

## 2. The Hydra fragment/metatheorem boundary — NOT DISSOLVED

`[src]` grep over `HAomega/*.lean` for `hercules`/`strategy`/`Play`: the
only hits are prose in `Hydra.lean`'s header, which says the general theorem
"is not derived here."  **No declaration states or proves the
all-strategies theorem.**  What HA^ω changed is *expressibility*: the
statement is now writable (function variables exist).  `HAOMEGA.md`'s
"dissolves — quantify over strategies directly" overclaimed; **fix
applied** — the row now says "statement expressible; not derived."
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

* `lake build`: **741 jobs, success** (after the fixes below: re-verified).
* `wc -l HAomega/*.lean`: **5,067 lines** (21 files).
* `grep -rnw sorry HAomega/ --include=*.lean` → no matches (exit 1);
  same for `admit`.

## 7. `ShowAll.lean` / `EXTRACTED_HAOMEGA.md` `[src]/[run]`

`ShowAll.lean` names all seven realizers (`R1`–`R7`), renders each three
ways (raw `pretty`, collapsed `pretty'`, Haskell `EmitHaskell.hsTm`) and
**writes `EXTRACTED_HAOMEGA.md` as a build side effect** (an `#eval
IO.FS.writeFile` — worth knowing: every build regenerates the file).  The
generated file has 7 sections, 72,658 bytes; collapsed sizes measured:
fib 109, fib-hi 118, pascal 792, hanoi 1,881, **gcd 13,936**, goodstein
1,088, hydra 1,059 chars.  Nothing in either file contradicts the facts
above; the Haskell views are labeled as uncertified translations in both.

## 8. Fixes applied by this audit

1. `Fib.lean`: stale wall-diagnosis comment → historical note with the
   verified current behavior.
2. `HAOMEGA.md`: Hydra "dissolves" row → "expressible, not derived";
   `bump`-row "definable" → "schemas gone, symbols primitive"; the Status
   section rewritten to current, evidence-backed state (741 jobs, footprints
   above, all seven case studies); "What is next" refreshed.
