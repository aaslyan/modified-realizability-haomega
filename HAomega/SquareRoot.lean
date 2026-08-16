/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Sperner
import HAomega.NumericsDemo

/-!
# Square roots by approximation — the first analysis theorem

    sqrtApproxD : ∀q^rat ∀n ∀K.
        colour(q,n,0) = 0 → colour(q,n,K) = 1 →
        ∃k. k < K ∧ colour(q,n,k) ≠ colour(q,n,k+1)

where `colour(q,n,k)` is `q < (k·2⁻ⁿ)²` as a `0`/`1` test. A crossing is a `k`
with `(k·2⁻ⁿ)² ≤ q < ((k+1)·2⁻ⁿ)²`: the largest multiple of `2⁻ⁿ` whose square
does not exceed `q`, which is `√q` to precision `2⁻ⁿ`. The extracted program
is a root-finding search, and it runs.

## Why this is a corollary rather than a new development

Sperner's lemma in one dimension **is** the discrete intermediate value
theorem, and this is that theorem applied to squaring. That reading is
available here for a specific reason: `spernerD` quantifies over the colouring
as a *function variable*, so its proof knows nothing about what the colouring
computes. All the rational arithmetic therefore sits inside an argument the
derivation never inspects, and the theorem needs **no arithmetic rules at
all** — which is why it can be stated and proved now, before `Deriv` has any
conversion equations for `Q`.

That is worth being precise about, because it is also the honest limit. What
is proved is: *given* a bound `K` whose scaled square exceeds `q`, the search
finds the crossing. Producing such a `K` from `q` is an Archimedean argument
about the rationals, and that genuinely does need the arithmetic rule base.
The hypothesis is discharged by the caller — at every input below, by
computation.

## What the extract does

Because the colouring here is monotone — `0 … 0 1 … 1` — the first and last
crossings coincide, so the fingerprint difference recorded for Sperner in
Act X does not arise: both proofs of Sperner would give the same root here.
The distinction needs a colouring that oscillates, and squaring does not.
-/

namespace HAomega

/-- `(k · 2⁻ⁿ)²` — the scaled square, as an object term.  In a context whose
first three variables are `k`, `K`, `n`, `q`. -/
def scaledSq {Γ : List Ty} :
    Tm (.nat :: .nat :: .nat :: .rat :: Γ) .rat :=
  let step : Tm (.nat :: .nat :: .nat :: .rat :: Γ) .rat :=
    .qmul (.qnat (.var .here))
      (.dtoq (.app dpow2 (.var (.there (.there .here)))))
  .qmul step step

/-- The colouring: `1` once the scaled square passes `q`, `0` before.  Its
crossing is the approximation.  A term in a context `K, n, q`. -/
def sqColour {Γ : List Ty} :
    Tm (.nat :: .nat :: .rat :: Γ) (.arrow .nat .nat) :=
  .lam (.qlt (.var (.there (.there (.there .here)))) scaledSq)

/-- The context after the three binders and the two premises. -/
abbrev sqCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .rat :: Γ) (.unit :: .unit :: as) :=
  .cons (.eq (.app sqColour (.var .here)) (.succ .zero))
    (.cons (.eq (.app sqColour .zero) .zero) (((Δ.wk).wk).wk))

/-- **Square roots to any precision, from the discrete intermediate value
theorem.**  Given a bound whose scaled square exceeds `q`, there is a crossing
below it, and the crossing is `√q` to within `2⁻ⁿ`. -/
def sqrtApproxD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .rat (.all .nat (.all .nat
      (.imp (.eq (.app sqColour .zero) .zero)
      (.imp (.eq (.app sqColour (.var .here)) (.succ .zero))
        (.ex .nat (.and
          (.ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here))
            (.var (.there (.there .here)))))
          ((Formula.eq (.app (sqColour (Γ := Γ)).wk (.var .here))
            (.app (sqColour (Γ := Γ)).wk (.succ (.var .here)))).neg)))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))))
  -- instantiate the discrete IVT at the bound and at this colouring
  have s1 := Deriv.allE (τ := .nat) (.var .here) (spernerD (Δ := sqCtx Γ Δ))
  deriv_norm at s1
  have s2 := Deriv.allE (τ := .arrow .nat .nat) sqColour s1
  deriv_norm at s2
  exact Deriv.impE (Deriv.impE s2 (Deriv.wk Deriv.ax)) Deriv.ax

/-- **The extracted root-finding search.** -/
def sqrtApproxX (q : Q) (n K : Nat) : Nat :=
  ((((((extractClosed (sqrtApproxD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    q) n) K) () ()).1

/-- The same colouring at the value level, for stating what the guards check. -/
def sqColourVal (q : Q) (n k : Nat) : Nat :=
  Q.ltN q (Q.mul (Q.mul (Q.ofNat k) (D.toQ (D.pow2neg n)))
                 (Q.mul (Q.ofNat k) (D.toQ (D.pow2neg n))))

/-- The approximation as a rational: `k · 2⁻ⁿ`. -/
def sqrtApprox (q : Q) (n K : Nat) : Q :=
  Q.mul (Q.ofNat (sqrtApproxX q n K)) (D.toQ (D.pow2neg n))

-- **It computes square roots.**  `√2` to `2⁻⁴` and `2⁻⁸`, `√9` exactly, and
-- `√(1/4)`.
#guard sqrtApproxX (Q.ofNat 2) 4 32 == 22
#guard sqrtApproxX (Q.ofNat 2) 8 512 == 362
#guard sqrtApproxX (Q.ofNat 9) 0 4 == 3
#guard sqrtApproxX (Q.of 1 4) 4 32 == 8
-- read as rationals: 22/16 = 11/8, 362/256 = 181/128, and the exact ones
#guard sqrtApprox (Q.ofNat 2) 4 32 == Q.of 11 8
#guard sqrtApprox (Q.ofNat 2) 8 512 == Q.of 181 128
#guard sqrtApprox (Q.ofNat 9) 0 4 == Q.ofNat 3
#guard sqrtApprox (Q.of 1 4) 4 32 == Q.of 1 2

-- **And the witness really brackets the root**: the colouring is `0` at the
-- crossing and `1` just past it, which is `(k·2⁻ⁿ)² ≤ q < ((k+1)·2⁻ⁿ)²`.
-- This is what soundness guarantees at every input; the guard checks the
-- corner the build can run.
#guard (List.range 6).all fun n ↦
  (let K := 2 * Nat.rec 1 (fun _ ih ↦ 2 * ih) n
   let k := sqrtApproxX (Q.ofNat 2) n K
   sqColourVal (Q.ofNat 2) n k == 0 && sqColourVal (Q.ofNat 2) n (k + 1) == 1)

#print axioms sqrtApproxD
#print axioms sqrtApproxX

/-! ## 2. Target C1: Cube Roots by Discrete IVT / Sperner -/

/-- `(k · 2⁻ⁿ)³` — the scaled cube, as an object term. -/
def scaledCube {Γ : List Ty} :
    Tm (.nat :: .nat :: .nat :: .rat :: Γ) .rat :=
  let step : Tm (.nat :: .nat :: .nat :: .rat :: Γ) .rat :=
    .qmul (.qnat (.var .here))
      (.dtoq (.app dpow2 (.var (.there (.there .here)))))
  .qmul step (.qmul step step)

/-- The cube colouring: `1` once the scaled cube passes `q`, `0` before. -/
def cubeColour {Γ : List Ty} :
    Tm (.nat :: .nat :: .rat :: Γ) (.arrow .nat .nat) :=
  .lam (.qlt (.var (.there (.there (.there .here)))) scaledCube)

/-- The context for cube root extraction. -/
abbrev cubeCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .rat :: Γ) (.unit :: .unit :: as) :=
  .cons (.eq (.app cubeColour (.var .here)) (.succ .zero))
    (.cons (.eq (.app cubeColour .zero) .zero) (((Δ.wk).wk).wk))

/-- **Theorem (Target C1: Cube Roots by Discrete IVT / Sperner)**:
    Given a bound whose scaled cube exceeds `q`, there is a crossing
    below it, and the crossing is `∛q` to within precision `2⁻ⁿ`. -/
def cubeApproxD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .rat (.all .nat (.all .nat
      (.imp (.eq (.app cubeColour .zero) .zero)
      (.imp (.eq (.app cubeColour (.var .here)) (.succ .zero))
        (.ex .nat (.and
          (.ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here))
            (.var (.there (.there .here)))))
          ((Formula.eq (.app (cubeColour (Γ := Γ)).wk (.var .here))
            (.app (cubeColour (Γ := Γ)).wk (.succ (.var .here)))).neg)))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))))
  have s1 := Deriv.allE (τ := .nat) (.var .here) (spernerD (Δ := cubeCtx Γ Δ))
  deriv_norm at s1
  have s2 := Deriv.allE (τ := .arrow .nat .nat) cubeColour s1
  deriv_norm at s2
  exact Deriv.impE (Deriv.impE s2 (Deriv.wk Deriv.ax)) Deriv.ax

/-- **The extracted cube-root search.** -/
def cubeApproxX (q : Q) (n K : Nat) : Nat :=
  ((((((extractClosed (cubeApproxD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    q) n) K) () ()).1

/-- The cube-root approximation as a rational: `k · 2⁻ⁿ`. -/
def cubeApprox (q : Q) (n K : Nat) : Q :=
  Q.mul (Q.ofNat (cubeApproxX q n K)) (D.toQ (D.pow2neg n))

-- **It computes cube roots**: ∛2 to 2⁻⁴ and 2⁻⁸, ∛8 = 2, ∛27 = 3, ∛(1/8) = 1/2.
#guard cubeApproxX (Q.ofNat 2) 4 32 == 20
#guard cubeApproxX (Q.ofNat 2) 8 512 == 322
#guard cubeApproxX (Q.ofNat 8) 0 4 == 2
#guard cubeApproxX (Q.ofNat 27) 0 5 == 3
#guard cubeApproxX (Q.of 1 8) 4 32 == 8

-- Read as rationals:
#guard cubeApprox (Q.ofNat 2) 4 32 == Q.of 5 4
#guard cubeApprox (Q.ofNat 2) 8 512 == Q.of 161 128
#guard cubeApprox (Q.ofNat 8) 0 4 == Q.ofNat 2
#guard cubeApprox (Q.ofNat 27) 0 5 == Q.ofNat 3
#guard cubeApprox (Q.of 1 8) 4 32 == Q.of 1 2

#print axioms cubeApproxD
#print axioms cubeApproxX

/-! ## 3. Targets C2 & C4: General Monotone Root and Inverse Function Extraction -/

/-- Scaled argument `k · 2⁻ⁿ` for an arbitrary function `F`. -/
def fnScaledArg {Γ : List Ty} :
    Tm (.nat :: .nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) .rat :=
  .qmul (.qnat (.var .here))
    (.dtoq (.app dpow2 (.var (.there (.there .here)))))

/-- Colouring for general root/inverse search: `1` once `F(k · 2⁻ⁿ)` exceeds `y`, `0` before. -/
def fnCrossingColour {Γ : List Ty} :
    Tm (.nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) (.arrow .nat .nat) :=
  .lam (.qlt (.var (.there (.there (.there .here))))
    (.app (.var (.there (.there (.there (.there .here))))) fnScaledArg))

/-- Context for general function crossing extraction. -/
abbrev fnCrossingCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .rat :: (.arrow .rat .rat) :: Γ) (.unit :: .unit :: as) :=
  .cons (.eq (.app fnCrossingColour (.var .here)) (.succ .zero))
    (.cons (.eq (.app fnCrossingColour .zero) .zero) ((((Δ.wk).wk).wk).wk))

/-- **Theorem (Targets C2 & C4: General Constructive Root & Inverse Function Extraction)**:
    For ANY computable function $F : \mathbb{Q} \to \mathbb{Q}$ and target value $y \in \mathbb{Q}$,
    given a bracket $[0, K \cdot 2^{-n}]$ across which $F$ crosses $y$,
    constructs a certified crossing $k < K$ isolating the solution $F(x) = y$
    (and hence computing the inverse $x = F^{-1}(y)$) to precision $2^{-n}$. -/
def fnCrossingD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all (.arrow .rat .rat) (.all .rat (.all .nat (.all .nat
      (.imp (.eq (.app fnCrossingColour .zero) .zero)
      (.imp (.eq (.app fnCrossingColour (.var .here)) (.succ .zero))
        (.ex .nat (.and
          (.ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here))
            (.var (.there (.there .here)))))
          ((Formula.eq (.app (fnCrossingColour (Γ := Γ)).wk (.var .here))
            (.app (fnCrossingColour (Γ := Γ)).wk (.succ (.var .here)))).neg))))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_)))))
  have s1 := Deriv.allE (τ := .nat) (.var .here) (spernerD (Δ := fnCrossingCtx Γ Δ))
  deriv_norm at s1
  have s2 := Deriv.allE (τ := .arrow .nat .nat) fnCrossingColour s1
  deriv_norm at s2
  exact Deriv.impE (Deriv.impE s2 (Deriv.wk Deriv.ax)) Deriv.ax

/-- **The extracted general root and inverse function solver.** -/
def fnCrossingX (F : Q → Q) (y : Q) (n K : Nat) : Nat :=
  (((((((extractClosed (fnCrossingD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    F) y) n) K) () ()).1

/-- The isolated root/inverse point as a rational: `k · 2⁻ⁿ`. -/
def fnCrossingSol (F : Q → Q) (y : Q) (n K : Nat) : Q :=
  Q.mul (Q.ofNat (fnCrossingX F y n K)) (D.toQ (D.pow2neg n))

-- 1. Fourth root: P(x) = x⁴, solving x⁴ = 2 (x ≈ 1.1892, 19/16 = 1.1875):
#guard fnCrossingX (fun x ↦ Q.mul (Q.mul x x) (Q.mul x x)) (Q.ofNat 2) 4 32 == 19
#guard fnCrossingSol (fun x ↦ Q.mul (Q.mul x x) (Q.mul x x)) (Q.ofNat 2) 4 32 == Q.of 19 16

-- 2. Affine inverse: F(x) = 2x + 1, solving 2x + 1 = 5 (x = 2):
#guard fnCrossingX (fun x ↦ Q.add (Q.mul (Q.ofNat 2) x) (Q.ofNat 1)) (Q.ofNat 5) 0 5 == 2
#guard fnCrossingSol (fun x ↦ Q.add (Q.mul (Q.ofNat 2) x) (Q.ofNat 1)) (Q.ofNat 5) 0 5 == Q.ofNat 2

-- 3. Cubic polynomial inverse: F(x) = x³ + x, solving x³ + x = 10 (x = 2):
#guard fnCrossingX (fun x ↦ Q.add (Q.mul x (Q.mul x x)) x) (Q.ofNat 10) 0 5 == 2
#guard fnCrossingSol (fun x ↦ Q.add (Q.mul x (Q.mul x x)) x) (Q.ofNat 10) 0 5 == Q.ofNat 2

-- 4. Fifth root: P(x) = x⁵, solving x⁵ = 32 (x = 2):
#guard fnCrossingX (fun x ↦ Q.mul x (Q.mul (Q.mul x x) (Q.mul x x))) (Q.ofNat 32) 0 5 == 2
#guard fnCrossingSol (fun x ↦ Q.mul x (Q.mul (Q.mul x x) (Q.mul x x))) (Q.ofNat 32) 0 5 == Q.ofNat 2

#print axioms fnCrossingD
#print axioms fnCrossingX

end HAomega
