# HAomega remediation and research plan

## 1. Fix documentation drift

Update `docs/haomega/HAOMEGA.md`, `docs/haomega/HAOMEGA_PROGRAMS.md`, and relevant source comments so the public story matches the code:

- Current build count: 743 jobs.
- Current `HAomega/` size: 5,454 Lean lines.
- `HAomega/` imports the first-order value layers, not "nothing" from `Realizability`.
- `herculesD` derives the replication-strategy theorem; the any-head Hercules theorem is still not derived.
- The gcd full specification is complete.
- The Sperner extract returns the last crossing, not the first.

## 2. Fix the extracted artifact

Extend `HAomega/ShowAll.lean` from seven to nine rendered realizers:

- add `spernerD`;
- add `herculesD`;
- regenerate `EXTRACTED_HAOMEGA.md`;
- update README/paper wording only after the artifact actually renders all nine.

## 3. Clean code-level comments

Correct stale comments in:

- `HAomega/Sperner.lean`: "first-crossing search" -> "last-crossing search";
- `HAomega/Realizability.lean`: "28 rules" -> "39 rules";
- `HAomega/Continuity.lean`: "11 constructors" -> the current constructor count, or a neutral "one case per `Tm` constructor".

## 4. Run verification

After edits, run:

```bash
lake build
rg -n "six|seven extracted|741|5067|first-crossing|28 rules|11 constructors|imports nothing" .
```

Then check that any remaining matches are intentional historical notes rather than current claims.

## 5. Paper pass

Update `paper/act8-haomega.tex` after code and docs are aligned:

- clarify that Goodstein/Hydra still use primitive symbols backed by the first-order value layer;
- clarify "full HA^omega" as finite-type arithmetic plus `tiEps0`/matching `tiRec`, with imported value primitives;
- ensure the "three-view artifact" claim says nine realizers only after `ShowAll.lean` emits nine.

## 6. Quality cleanup

Optionally clean linter warnings, especially unused simp arguments and no-op `deriv_norm` calls. This is not mathematically urgent, but it improves audit confidence.

## 7. Research track

Prioritize:

- fully general any-head Hercules via typed hydra/tree surgery and descent;
- typed Goodstein/Hydra value layers instead of coded first-order primitives;
- certified semantics for emitted Haskell;
- stronger continuity artifacts, especially automatic associates/moduli for extracted type-2 programs;
- reusable proof-authoring tactics for HA^omega derivations.
