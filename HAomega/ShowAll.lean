/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Hydra
import HAomega.GcdTheorem
import HAomega.Sperner
import HAomega.HerculesAny
import HAomega.GoodsteinTyped
import HAomega.HydraTree
import HAomega.HerculesTree

/-!
# Every extracted program, in three views

For each of the thirteen case studies this module renders the realizer three
ways and writes `EXTRACTED_HAOMEGA.md`:

1. **the high-level object** — the raw extracted realizer, the element of the
   modified-realizability interpretation, with its contentless (`unit`-typed)
   certificate components visible;
2. **the collapsed functional program** — the same term with contentless
   parts elided: what remains is exactly the computational content;
3. **Haskell** — the same term emitted as Haskell source (an uncertified
   translation; the certified artifact is the `Tm`).

The three views are three renderings of *one* certified object per theorem —
nothing is re-proved or re-extracted between them.
-/

namespace HAomega

def R1 := fibRealizer
def R2 := hiRealizer
def R3 := pasRealizer
def R4 := extractClosed hanoiDeriv
def R5 := extractClosed (gcdTheoremD (Γ := []) (Δ := Ctx.nil))
def R6 := extractClosed (goodsteinD (Γ := []) (Δ := Ctx.nil))
def R7 := extractClosed (hydraD (Γ := []) (Δ := Ctx.nil))
def R8 := extractClosed (spernerD (Γ := []) (Δ := Ctx.nil))
def R9 := extractClosed (herculesD (Γ := []) (Δ := Ctx.nil))
def R10 := extractClosed (herculesAnyD (Γ := []) (Δ := Ctx.nil))
def R11 := extractClosed (goodsteinOD (Γ := []) (Δ := Ctx.nil))
def R12 := extractClosed (hydraHD (Γ := []) (Δ := Ctx.nil))
def R13 := extractClosed (herculesTD (Γ := []) (Δ := Ctx.nil))

private def section' (title thm ty : String)
    {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) : String :=
  "## " ++ title ++ "\n\n" ++
  "Theorem: `" ++ thm ++ "`  \n" ++
  "Realizer type: `" ++ ty ++ "`\n\n" ++
  "**1. High-level extracted object** (raw realizer; `★` = erased certificate):\n\n" ++
  "```\n" ++ t.pretty 0 ++ "\n```\n\n" ++
  "**2. Collapsed functional program** (contentless parts elided):\n\n" ++
  "```\n" ++ t.pretty' 0 ++ "\n```\n\n" ++
  "**3. Haskell** (generated translation, not the certified artifact):\n\n" ++
  "```haskell\n" ++ EmitHaskell.hsTm t 0 ++ "\n```\n\n"

def showAll : String :=
  "# The thirteen extracted programs of the HA^ω development\n\n" ++
  "Each section shows one certified realizer in three renderings.  The\n" ++
  "certified object is the System T term; soundness certifies it realizes\n" ++
  "its theorem, continuity that it denotes a continuous functional.\n\n" ++
  section' "1. Fibonacci" "∀n. ∃y. y = fib n" "N → (N × 1)" R1 ++
  section' "2. Fibonacci at type 2" "∀f^(ℕ→ℕ). ∃y. y = fib (f (f 0))"
    "(N → N) → (N × 1)" R2 ++
  section' "3. Pascal mod 2 (proof-computed)" "∀n ∀k. pas n k = 1 ∨ pas n k = 0"
    "N → (N → (N × (1 × 1)))" R3 ++
  section' "4. Tower of Hanoi" "∀n. ∃len ∃moves^(ℕ→ℕ). len = … ∧ moves = …"
    "N → (N × ((N → N) × (1 × 1)))" R4 ++
  section' "5. gcd (full specification, proof-computed)"
    "∀a ∀b. ∃g. g∣a ∧ g∣b ∧ ∀d. d∣a → d∣b → d∣g"
    "N → (N → (N × ((N × 1) × ((N × 1) × (N → ((N × 1) → ((N × 1) → (N × 1))))))))" R5 ++
  section' "6. Goodstein (TI(ε₀))" "∀m. ∃t. good(m, t) = 0" "N → (N × 1)" R6 ++
  section' "7. Kirby–Paris Hydra (TI(ε₀))" "∀h. ∃t. hydra(h, t) = 0" "N → (N × 1)" R7 ++
  section' "8. Sperner 1D (last-crossing scan)"
    "∀n ∀c^(ℕ→ℕ). c 0 = 0 → c n = 1 → ∃k. k < n ∧ c k ≠ c (k+1)"
    "N → ((N → N) → (1 → (1 → (N × ((N × 1) × (1 → 1))))))" R8 ++
  section' "9. Hercules (strategy-quantified Hydra)"
    "∀h ∀f^(ℕ→ℕ). ∃t. play(f, h, t) = 0"
    "N → ((N → N) → (N × 1))" R9 ++
  section' "10. Hercules, any head (the fully general game)"
    "∀h ∀f^(ℕ→ℕ) ∀g^(ℕ→ℕ). ∃t. playAt(g, f, h, t) = 0"
    "N → ((N → N) → ((N → N) → (N × 1)))" R10 ++
  section' "11. Goodstein over the typed ordinals (TI(ε₀) on notations)"
    "∀m. ∃t. good(m, t) = 0   — §6's statement, proved on structural ordinals"
    "N → (N × 1)" R11 ++
  section' "12. Kirby–Paris on trees (nothing encoded)"
    "∀h^hyd. ∃t. deadᴴ?(play(h, t)) = 0   — §7's theorem with tree states and notation measures"
    "H → (N × 1)" R12 ++
  section' "13. Hercules, any head, on trees (nothing encoded anywhere)"
    "∀h^hyd ∀f^(ℕ→ℕ) ∀g^(ℕ→ℕ). ∃t. deadᴴ?(playAt(g, f, h, t)) = 0"
    "H → ((N → N) → ((N → N) → (N × 1)))" R13

-- **Coverage of the certified-emission fragment** (`HsSemantics.hsOf_correct`):
-- exactly the programs that do not use transfinite recursion, for which the
-- emitter has never produced running code.
#guard [hsSupported R1, hsSupported R2, hsSupported R3, hsSupported R4,
        hsSupported R5, hsSupported R6, hsSupported R7, hsSupported R8,
        hsSupported R9, hsSupported R10, hsSupported R11, hsSupported R12,
        hsSupported R13]
  == [true, true, true, true, true, false, false, true,
      false, false, false, false, false]

#eval IO.FS.writeFile "EXTRACTED_HAOMEGA.md" showAll
#eval IO.println ("written: " ++ toString showAll.length ++ " chars")

end HAomega
