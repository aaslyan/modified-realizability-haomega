/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SquareRoot

/-!
# Target A: Certified 2-D Implicit Curve Plotter via Sperner's Discrete IVT

`fnCrossingD` is a genuinely non-tautological higher-type theorem (`∀F : ℚ → ℚ`),
concluding a certified bracket across which `F` crosses a target value `y`.

For any implicit curve $\Phi(x, y) = 0$, we can fix $x$ and solve for $y$:
that level-set solution is a crossing certified by `fnCrossingD`.
Sweeping $x$ across a grid yields a 2-D curve where **every plotted point carries
a certified rational bracket**.
-/

namespace HAomega

/-! ## 1. The Certified Unit Circle: $x^2 + y^2 = 1 \iff y^2 = 1 - x^2$ -/

/-- For a fixed $x \in [0, 1]$, the certified $y \ge 0$ with $y^2 \approx 1 - x^2$,
    isolated to precision $2^{-n}$ by the discrete IVT crossing theorem. -/
def circleY (x : Q) (n K : Nat) : Q :=
  fnCrossingSol (fun y ↦ Q.mul y y) (Q.sub (Q.ofNat 1) (Q.mul x x)) n K

/-- The index $k$ of the certified interval $[k \cdot 2^{-n}, (k+1) \cdot 2^{-n})$ for circle $y$. -/
def circleYIndex (x : Q) (n K : Nat) : Nat :=
  fnCrossingX (fun y ↦ Q.mul y y) (Q.sub (Q.ofNat 1) (Q.mul x x)) n K

/-- Compute a list of certified $(x, y)$ points along the upper quarter-circle. -/
def circlePoints (n K steps : Nat) : List (Q × Q) :=
  (List.range (steps + 1)).map fun i ↦
    let x := Q.of i steps
    (x, circleY x n K)

/-! ## 2. The Certified Ellipse: $x^2/4 + y^2 = 1 \iff y^2 = 1 - x^2/4$ -/

/-- For a fixed $x \in [0, 2]$, the certified $y \ge 0$ on the ellipse $x^2/4 + y^2 = 1$. -/
def ellipseY (x : Q) (n K : Nat) : Q :=
  fnCrossingSol (fun y ↦ Q.mul y y) (Q.sub (Q.ofNat 1) (Q.div (Q.mul x x) (Q.ofNat 4))) n K

/-! ## 3. The Certified Cubic Algebraic Curve: $y^3 + y = x$ -/

/-- For a fixed $x \ge 0$, the certified unique real root $y$ of $y^3 + y = x$. -/
def cubicCurveY (x : Q) (n K : Nat) : Q :=
  fnCrossingSol (fun y ↦ Q.add (Q.mul y (Q.mul y y)) y) x n K

/-! ## 4. ASCII Terminal Plotter for Certified Curves -/

/-- Render the certified quarter-circle points into an ASCII grid of size `(gridSize+1) × (gridSize+1)`. -/
def renderCircleAscii (gridSize : Nat) (n K : Nat) : String :=
  let rows := (List.range (gridSize + 1)).reverse.map fun r ↦
    let yTarget := Q.of r gridSize
    let rowChars := (List.range (gridSize + 1)).map fun c ↦
      let x := Q.of c gridSize
      let yComputed := circleY x n K
      let diff := Q.abs (Q.sub yComputed yTarget)
      if Q.ltN diff (Q.of 1 (2 * gridSize)) == 1 then '#' else '.'
    String.ofList rowChars
  String.intercalate "\n" rows

/-! ## 5. Kernel-Verified Guarantees for Certified Curve Points -/

-- A. Circle Axis Intercepts:
#guard circleY (Q.ofNat 0) 4 32 == Q.of 1 1  -- (0, 1) exact
#guard circleY (Q.ofNat 1) 4 32 == Q.of 0 1  -- (1, 0) exact

-- B. The Discriminating Pythagorean Point (3/5, 4/5):
-- (3/5)² + y² = 1 ⟹ y = 4/5 = 0.8
#guard circleY (Q.of 3 5) 8 512 == Q.of 51 64 -- At n=8: k=204, 204/256 = 51/64 = 0.796875 <= 4/5 < 0.80078125
#guard circleYIndex (Q.of 3 5) 4 32 == 12      -- 12/16 = 3/4 <= 4/5 < 13/16
#guard circleY (Q.of 4 5) 8 512 == Q.of 153 256 -- (4/5, 3/5 = 0.6): k=153, 153/256 = 0.59765625 <= 3/5 < 0.6015625

-- C. Ellipse Semi-Axes and Rational Point:
#guard ellipseY (Q.ofNat 0) 4 32 == Q.of 1 1  -- (0, 1) minor axis
#guard ellipseY (Q.ofNat 2) 4 32 == Q.of 0 1  -- (2, 0) major axis

-- D. Cubic Curve Integer Points:
#guard cubicCurveY (Q.ofNat 0) 4 32 == Q.of 0 1   -- 0³ + 0 = 0
#guard cubicCurveY (Q.ofNat 2) 4 32 == Q.of 1 1   -- 1³ + 1 = 2 (K=32: bracket up to 2, F(2)=10 > 2)
#guard cubicCurveY (Q.ofNat 10) 4 64 == Q.of 2 1  -- 2³ + 2 = 10 (K=64: bracket up to 4, F(4)=68 > 10)
#guard cubicCurveY (Q.ofNat 30) 4 64 == Q.of 3 1  -- 3³ + 3 = 30 (K=64: bracket up to 4, F(4)=68 > 30)

-- E. Monotonicity of Upper Circle: y strictly decreases as x strictly increases:
#guard (
  let y0 := circleY (Q.of 0 4) 6 128
  let y1 := circleY (Q.of 1 4) 6 128
  let y2 := circleY (Q.of 2 4) 6 128
  let y3 := circleY (Q.of 3 4) 6 128
  let y4 := circleY (Q.of 4 4) 6 128
  Q.ltN y1 y0 == 1 && Q.ltN y2 y1 == 1 && Q.ltN y3 y2 == 1 && Q.ltN y4 y3 == 1
)

-- F. Bracket Invariant at Every Swept Circle Point: y² ≤ 1 - x² < (y + 2⁻ⁿ)²
#guard (
  (List.range 5).all fun i ↦
    let x := Q.of i 4
    let target := Q.sub (Q.ofNat 1) (Q.mul x x)
    let y := circleY x 6 128
    let yUpper := Q.add y (D.toQ (D.pow2neg 6))
    let ySq := Q.mul y y
    let yUpperSq := Q.mul yUpper yUpper
    (Q.ltN target ySq == 0) && (Q.ltN target yUpperSq == 1)
)

end HAomega
