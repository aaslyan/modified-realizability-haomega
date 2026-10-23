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
import HAomega.SquareRoot
import HAomega.UniformContinuity
import HAomega.ClosedFourierODE
import HAomega.PicardExpSolve
import HAomega.QuadBlowupSolve
import HAomega.RiccatiSolve
import HAomega.DuffingSolve
import HAomega.PolyODESystem

/-!
# Every extracted program, in three views

For each of the thirty-one case studies this module renders the realizer three
ways and writes `EXTRACTED_HAOMEGA.md`:

1. **the high-level object** — the raw extracted realizer, the element of the
   modified-realizability interpretation, with its contentless (`unit`-typed)
   certificate components visible;
2. **the collapsed functional program** — the same term with contentless
   parts elided: what remains is exactly the computational content;
3. **Haskell** — the same term emitted as Haskell source (via the certified
   translation `hsOf`, whose operational semantics soundness is proved in
   `HsSemantics.hsOf_correct`).

Each program's title labels where its computational content comes from:
**proof-computed** (the program's recursion is assembled by extraction from
`Deriv.ind`, `tiEps0` or case analysis, on a specification that names no
algorithm); **explicit witness, derived correctness** (the specification names
no algorithm, but the proof writes the witness term at `exI` and the induction
or scaling rules only certify it, so they contribute no computation); or
**witness-style** (the theorem statement names the target term and the proof
supplies it to `exI`, alongside any equational certificates).

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
def R14 := extractClosed (sqrtApproxD (Γ := []) (Δ := Ctx.nil))
def R15 := extractClosed (uniContD (Γ := []) (Δ := Ctx.nil))
def R16 := extractClosed ftcAntiderivD
def R17 := extractClosed jetMulD
def R18 := extractClosed jetEvalPolyD
def R19 := extractClosed (jetCauchyModulusGenuineD (Γ := []) (Δ := Ctx.nil))
def R20 := extractClosed (jetContModulusD (Γ := []) (Δ := Ctx.nil))
def R21 := extractClosed (jetDiffModulusD (Γ := []) (Δ := Ctx.nil))
def R22 := extractClosed picardJetIterD
def R23 := extractClosed riccatiPicardD
def R24 := extractClosed quadBlowupPicardD
def R25 := extractClosed duffingPicardD
def R26 := extractClosed newtonJetInvD
def R27 := extractClosed picardExpSolveD
def R28 := extractClosed quadBlowupSolveD
def R29 := extractClosed riccatiSolveD
def R30 := extractClosed duffingSolveD
def R31 := extractClosed (genSolve2D tmZeroJet tmConstOneJet .varV (.sub (.const tmZeroJet) .varU))

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
  "# The thirty-one extracted programs of the HA^ω development\n\n" ++
  "Each section shows one certified realizer in three renderings.  The\n" ++
  "certified object is the System T term; soundness certifies it realizes\n" ++
  "its theorem, continuity that it denotes a continuous functional.\n" ++
  "Each section title records where the computational witness comes from:\n" ++
  "**proof-computed** (the recursion is assembled by extraction from induction,\n" ++
  "`tiEps0` or case splits, on a specification that names no algorithm);\n" ++
  "**explicit witness, derived correctness** (the specification names no\n" ++
  "algorithm, but the proof writes the witness at `exI` and the induction or\n" ++
  "scaling rules only certify it); or **witness-style** (the theorem statement\n" ++
  "names the target term and the proof supplies it to `exI`).\n\n" ++
  section' "1. Fibonacci (witness-style)" "∀n. ∃y. y = fib n" "N → (N × 1)" R1 ++
  section' "2. Fibonacci at type 2 (witness-style)" "∀f^(ℕ→ℕ). ∃y. y = fib (f (f 0))"
    "(N → N) → (N × 1)" R2 ++
  section' "3. Pascal mod 2 (proof-computed)" "∀n ∀k. pas n k = 1 ∨ pas n k = 0"
    "N → (N → (N × (1 × 1)))" R3 ++
  section' "4. Tower of Hanoi (witness-style)" "∀n. ∃len ∃moves^(ℕ→ℕ). len = … ∧ moves = …"
    "N → (N × ((N → N) × (1 × 1)))" R4 ++
  section' "5. gcd (full specification, proof-computed)"
    "∀a ∀b. ∃g. g∣a ∧ g∣b ∧ ∀d. d∣a → d∣b → d∣g"
    "N → (N → (N × ((N × 1) × ((N × 1) × (N → ((N × 1) → ((N × 1) → (N × 1))))))))" R5 ++
  section' "6. Goodstein (TI(ε₀), proof-computed)" "∀m. ∃t. good(m, t) = 0" "N → (N × 1)" R6 ++
  section' "7. Kirby–Paris Hydra (TI(ε₀), proof-computed)" "∀h. ∃t. hydra(h, t) = 0" "N → (N × 1)" R7 ++
  section' "8. Sperner 1D (last-crossing scan, proof-computed)"
    "∀n ∀c^(ℕ→ℕ). c 0 = 0 → c n = 1 → ∃k. k < n ∧ c k ≠ c (k+1)"
    "N → ((N → N) → (1 → (1 → (N × ((N × 1) × (1 → 1))))))" R8 ++
  section' "9. Hercules (strategy-quantified Hydra, proof-computed)"
    "∀h ∀f^(ℕ→ℕ). ∃t. play(f, h, t) = 0"
    "N → ((N → N) → (N × 1))" R9 ++
  section' "10. Hercules, any head (the fully general game, proof-computed)"
    "∀h ∀f^(ℕ→ℕ) ∀g^(ℕ→ℕ). ∃t. playAt(g, f, h, t) = 0"
    "N → ((N → N) → ((N → N) → (N × 1)))" R10 ++
  section' "11. Goodstein over the typed ordinals (TI(ε₀) on notations, proof-computed)"
    "∀m. ∃t. good(m, t) = 0   — §6's statement, proved on structural ordinals"
    "N → (N × 1)" R11 ++
  section' "12. Kirby–Paris on trees (nothing encoded, proof-computed)"
    "∀h^hyd. ∃t. deadᴴ?(play(h, t)) = 0   — §7's theorem with tree states and notation measures"
    "H → (N × 1)" R12 ++
  section' "13. Hercules, any head, on trees (nothing encoded anywhere, proof-computed)"
    "∀h^hyd ∀f^(ℕ→ℕ) ∀g^(ℕ→ℕ). ∃t. deadᴴ?(playAt(g, f, h, t)) = 0"
    "H → ((N → N) → ((N → N) → (N × 1)))" R13 ++
  section' "14. Square roots by approximation (the discrete IVT, applied, proof-computed)"
    "∀q^ℚ ∀n ∀K. col(0)=0 → col(K)=1 → ∃k. k<K ∧ col(k) ≠ col(k+1)"
    "Q → (N → (N → (1 → (1 → (N × ((N × 1) × (1 → 1)))))))" R14 ++
  section' "15. Uniform continuity — the realizer is the modulus (explicit witness, derived correctness)"
    "∀f^(ℚ→ℚ) ∀j. Lipschitz(f,j) → ∀n ∃M ∀x∀y. close(M,x,y) → close(n, f x, f y)"
    "(Q → Q) → (N → ((Q → (Q → (N → (1 → 1)))) → (N → (N × (Q → (Q → (1 → 1)))))))" R15 ++
  section' "16. Formal antiderivative & termwise FTC1 (witness-style antiderivative; cancellation D(I c)(n) - c(n) = 0 derived)"
    "∀c^(ℕ→ℚ). ∃F^(ℕ→ℚ). F(0) = 0 ∧ ∀n. D(F)(n) - c(n) = 0"
    "(N → Q) → ((N → Q) × (1 × (N → 1)))" R16 ++
  section' "17. Cauchy product convolution of formal power series (witness-style)"
    "∀a^(ℕ→ℚ) ∀b^(ℕ→ℚ). ∃c^(ℕ→ℚ). c = cauchyConv(a, b)"
    "(N → Q) → ((N → Q) → ((N → Q) × 1))" R17 ++
  section' "18. Taylor polynomial evaluator (witness-style)"
    "∀c^(ℕ→ℚ) ∀m ∀x^ℚ. ∃y^ℚ. y = Σ_{j<m} c_j · x^j"
    "(N → Q) → (N → (Q → (Q × 1)))" R18 ++
  section' "19. Jet E₁ Cauchy convergence modulus, tail bound by geometric series induction (explicit witness, derived correctness)"
    "∀c^(ℕ→ℚ) ∀B ∀x^ℚ. (∀n. |S_n(x)-S_{n+1}(x)| < 2^(B+3)·(2^-(n+1)-2^-(n+2))) → QArithLaws → ∀k ∃N ∀d₁ ∀d₂. close(k, S_{N+d₁}(x), S_{N+d₁+d₂+1}(x))"
    "(N → Q) → (N → (Q → ((N → 1) → (1 → (N → (N × (N → (N → 1))))))))" R19 ++
  section' "20. Jet E₁ uniform continuity modulus (explicit witness, derived correctness)"
    "∀c^(ℕ→ℚ) ∀B₁ ∀x^ℚ ∀y^ℚ. (∀m. |S_m(x)-S_m(y)| ≤ 2^(B₁+1)·|x-y|) → ∀k ∃ω ∀m. close(ω,x,y) → close(k, S_m(x), S_m(y))"
    "(N → Q) → (N → (Q → (Q → ((N → 1) → (N → (N × (N → (1 → 1))))))))" R20 ++
  section' "21. Jet E₁ uniform differentiability modulus (explicit witness, derived correctness)"
    "∀c^(ℕ→ℚ) ∀B₂ ∀x^ℚ ∀h^ℚ. (∀m. |DQ_h(S_m,x)-S_m(Dc,x)| ≤ 2^(B₂+1)·|h|) → ∀k ∃δ ∀m. close(δ,h,0) → close(k, DQ_h(S_m,x), S_m(Dc,x))"
    "(N → Q) → (N → (Q → (Q → ((N → 1) → (N → (N × (N → (1 → 1))))))))" R21 ++
  section' "22. Order-1 Picard jet iteration for y' = y (witness-style)"
    "∀k. ∃Y^(ℕ→ℚ). Y = P^k(Y_0)"
    "N → ((N → Q) × 1)" R22 ++
  section' "23. Nonlinear Riccati ODE y' = 1 + y² Picard jet iteration (witness-style)"
    "∀k. ∃Y^(ℕ→ℚ). Y = P_Ric^k(Y_0)"
    "N → ((N → Q) × 1)" R23 ++
  section' "24. Nonlinear quadratic blow-up ODE y' = y² Picard jet iteration (witness-style)"
    "∀k. ∃Y^(ℕ→ℚ). Y = P_Blowup^k(Y_0)"
    "N → ((N → Q) × 1)" R24 ++
  section' "25. 2D coupled nonlinear Duffing oscillator Picard jet iteration (witness-style)"
    "∀k. ∃W^((ℕ→ℚ)×(ℕ→ℚ)). W = P_Duf^k(W_0)"
    "N → (((N → Q) × (N → Q)) × 1)" R25 ++
  section' "26. Quadratic Newton–Schulz multiplicative jet inverter (witness-style)"
    "∀F^(ℕ→ℚ) ∀k. ∃Y^(ℕ→ℚ). Y = N_F^k(1)"
    "(N → Q) → (N → ((N → Q) × 1))" R26 ++
  section' "27. Jet solver for y' = y from an algorithm-free specification (proof-computed)"
    "∀k. ∃Y^(ℕ→ℚ). ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)    (P(Y) = 1 + ∫Y)"
    "N → ((N → Q) × (N → (N → (1 → 1))))" R27 ++
  section' "28. Jet solver for the nonlinear y' = y² from an algorithm-free specification (proof-computed)"
    "∀k. ∃Y^(ℕ→ℚ). ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)    (P(Y) = 1 + ∫(Y·Y))"
    "N → ((N → Q) × (N → (N → (1 → 1))))" R28 ++
  section' "29. Jet solver for the Riccati equation y' = 1 + y² (tan) from an algorithm-free specification (proof-computed)"
    "∀k. ∃Y^(ℕ→ℚ). ∀i ∀d. i + succ d = k → P(Y)(i) = Y(i)    (P(Y) = ∫(1 + Y·Y))"
    "N → ((N → Q) × (N → (N → (1 → 1))))" R29 ++
  section' "30. Jet solver for the Duffing system u' = v, v' = -u - u² from an algorithm-free specification (proof-computed)"
    "∀k. ∃W^((ℕ→ℚ)×(ℕ→ℚ)). ∀i ∀d. i + succ d = k → P(W)₁(i) = W₁(i) ∧ P(W)₂(i) = W₂(i)    (P(u,v) = (1 + ∫v, ∫(0 - u - u·u)))"
    "N → (((N → Q) × (N → Q)) × (N → (N → (1 → (1 × 1)))))" R30 ++
  section' "31. Sine and cosine as the general two-variable solver at u' = v, v' = -u (proof-computed)"
    "∀k. ∃W. ∀i ∀d. i + succ d = k → P(W)₁(i) = W₁(i) ∧ P(W)₂(i) = W₂(i)    (P(u,v) = (0 + ∫v, 1 + ∫(0 - u)))"
    "N → (((N → Q) × (N → Q)) × (N → (N → (1 → (1 × 1)))))" R31

-- **Coverage of the certified-emission theorem** (`HsSemantics.hsOf_correct`):
-- all thirty-one programs are supported by the certified emitter!
#guard [hsSupported R1, hsSupported R2, hsSupported R3, hsSupported R4,
        hsSupported R5, hsSupported R6, hsSupported R7, hsSupported R8,
        hsSupported R9, hsSupported R10, hsSupported R11, hsSupported R12,
        hsSupported R13, hsSupported R14, hsSupported R15, hsSupported R16,
        hsSupported R17, hsSupported R18, hsSupported R19, hsSupported R20,
        hsSupported R21, hsSupported R22, hsSupported R23, hsSupported R24,
        hsSupported R25, hsSupported R26, hsSupported R27, hsSupported R28, hsSupported R29, hsSupported R30, hsSupported R31]
  == List.replicate 31 true

#eval IO.FS.writeFile "EXTRACTED_HAOMEGA.md" showAll
#eval IO.println ("written: " ++ toString showAll.length ++ " chars")

end HAomega
