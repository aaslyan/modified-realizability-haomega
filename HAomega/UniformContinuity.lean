/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SquareRoot

/-!
# Uniform continuity, and the modulus as the realizer

    uniContD : ∀f^(ℚ→ℚ) ∀j.
        (∀x ∀y ∀m. close(m+j, x, y) → close(m, f x, f y))
        → ∀n ∃M ∀x ∀y. close(M, x, y) → close(n, f x, f y)

where `close(k, x, y)` is the test `|x − y| < 2⁻ᵏ`. Read the realizer type of
the conclusion:
\[
  \forall n\,\exists M.\ \dots \quad\rightsquigarrow\quad \Nat \to \Nat \times
  (\dots)
\]
The first component of the extracted pair, as a function of `n`, **is the
modulus of continuity**. That is not an analogy or an encoding: it is what the
modified-realizability type assignment sends `∀n ∃M` to, and it is why this
framework meets constructive analysis without an adapter.

## Why the Lipschitz bound is a hypothesis

The content of uniform continuity for a *specific* `f` is an arithmetic
implication, and `Deriv` still has no conversion equations for `Q`. Rather
than guess at a rule base, this theorem takes the scaling as a premise: `f`
contracts the dyadic scale by `j`, whatever `f` is. What is then proved is the
general fact — *every such `f` is uniformly continuous, with modulus
`M = n + j`* — and the extracted program computes that modulus.

This is the same posture the square-root theorem takes toward its bound `K`,
and it is honest in the same way: the hypothesis is discharged by the caller,
by computation, at the instances guarded below. Discharging it *inside* the
object language is what the arithmetic rule base is for, and that remains the
next real piece of work.

## What is genuinely gained over the square root

The square-root theorem needed no rules because Sperner never inspects its
colouring. Here the function is a variable too — but the extracted object is
no longer a witness found by search, it is a **function of the precision**.
That is the step from "extraction produces a number" to "extraction produces
an approximation procedure's parameter", which is the transition the analysis
roadmap exists to make.
-/

namespace HAomega

-- `qabsT` and `qclose` are defined in `Syntax.lean`.

/-! ## Keeping the elaborator off the helper terms

`qclose`, `qabsT` and the precision sequence are **closed** terms, so renaming
and substitution are the identity on them.  Without saying so, every
`Formula.wk` in a derivation traverses their whole bodies, and the elaborator
symbolically executes a `recNat` for nothing — the blow-up
`PascalTheorem.lean`'s header records.  One `rfl` lemma each, tagged into the
normalizer, replaces the traversal with a rewrite. -/

@[derivNorm] theorem qabsT_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (qabsT (Γ := Γ)).rename ρ = qabsT := rfl
@[derivNorm] theorem qabsT_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (qabsT (Γ := Γ)).subst s = qabsT := rfl
@[derivNorm] theorem qclose_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (qclose (Γ := Γ)).rename ρ = qclose := rfl
@[derivNorm] theorem qclose_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (qclose (Γ := Γ)).subst s = qclose := rfl
@[derivNorm] theorem dpow2_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (dpow2 (Γ := Γ)).rename ρ = dpow2 := rfl
@[derivNorm] theorem dpow2_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (dpow2 (Γ := Γ)).subst s = dpow2 := rfl
@[derivNorm] theorem qpow2_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (qpow2 (Γ := Γ)).rename ρ = qpow2 := rfl
@[derivNorm] theorem qpow2_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (qpow2 (Γ := Γ)).subst s = qpow2 := rfl

/-- Genuine Lipschitz bound premise: $\forall x \forall y. \; |f(x) - f(y)| \le 2^j |x - y|$.
    Stated as $\text{qlt}(2^j \cdot |x - y|, |f(x) - f(y)|) = 0$. -/
abbrev ucLipBound (Γ : List Ty) : Formula (.nat :: .arrow .rat .rat :: Γ) (.arrow .rat (.arrow .rat .unit)) :=
  let ctxTy : List Ty := .nat :: .arrow .rat .rat :: Γ
  let f_var : Tm ctxTy (.arrow .rat .rat) := .var (.there .here)
  let j_var : Tm ctxTy .nat := .var .here
  .all .rat (.all .rat
    (.eq (.qlt (.qmul (.app qpow2pos (j_var.wk.wk)) (.app qabsT (.qsub (.var (.there .here)) (.var .here))))
               (.app qabsT (.qsub (.app (f_var.wk.wk) (.var (.there .here)))
                                  (.app (f_var.wk.wk) (.var .here)))))
         .zero))

/-- Conclusion of uniform continuity: $\forall n, \exists M, \forall x, \forall y. \; \text{close}(M, x, y) = 1 \implies \text{close}(n, f x, f y) = 1$. -/
abbrev ucConcl (Γ : List Ty) : Formula (.nat :: .arrow .rat .rat :: Γ)
    (.arrow .nat (.prod .nat (.arrow .rat (.arrow .rat (.arrow .unit .unit))))) :=
  .all .nat (.ex .nat (.all .rat (.all .rat
    (.imp (.eq (.app (.app (.app qclose (.var (.there (.there .here)))) (.var (.there .here))) (.var .here)) (.succ .zero))
      (.eq (.app (.app (.app qclose (.var (.there (.there (.there .here)))))
        (.app (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there .here))))
        (.app (.var (.there (.there (.there (.there (.there .here)))))) (.var .here))) (.succ .zero))))))

/-- Context at the innermost point of `uniContLipD`. -/
abbrev ucLipCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.rat :: .rat :: .nat :: .nat :: .arrow .rat .rat :: Γ)
      (.unit :: (.arrow .rat (.arrow .rat .unit)) :: as) :=
  let ctxTy : List Ty := .rat :: .rat :: .nat :: .nat :: .arrow .rat .rat :: Γ
  let j : Tm ctxTy .nat := .var (.there (.there (.there .here)))
  let n : Tm ctxTy .nat := .var (.there (.there .here))
  let x : Tm ctxTy .rat := .var (.there .here)
  let y : Tm ctxTy .rat := .var .here
  .cons (.eq (.app (.app (.app qclose (.add n j)) x) y) (.succ .zero))
    (.cons ((((ucLipBound Γ).wk).wk).wk) (((((Δ.wk).wk).wk).wk).wk))

/-- **Theorem (Uniform Continuity from Lipschitz Bound)**:
    For EVERY function $f : \mathbb{Q} \to \mathbb{Q}$ satisfying the genuine Lipschitz bound
    $|f(x) - f(y)| \le 2^j |x - y|$, derives that $f$ is uniformly continuous with modulus
    $M(n) = n + j$, using the scale conversion rule `convQLipScale`. -/
def uniContLipD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all (.arrow .rat .rat) (.all .nat (.imp (ucLipBound Γ) (ucConcl Γ)))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI (Deriv.allI ?_)))
  -- Extracted modulus witness: M(n) = n + j
  refine Deriv.exI (.add (.var .here) (.var (.there .here))) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  let ctxTy : List Ty := .rat :: .rat :: .nat :: .nat :: .arrow .rat .rat :: Γ
  let f : Tm ctxTy (.arrow .rat .rat) := .var (.there (.there (.there (.there .here))))
  let j : Tm ctxTy .nat := .var (.there (.there (.there .here)))
  let n : Tm ctxTy .nat := .var (.there (.there .here))
  let x : Tm ctxTy .rat := .var (.there .here)
  let y : Tm ctxTy .rat := .var .here
  have hPremise : Deriv (ucLipCtx Γ Δ) ((((ucLipBound Γ).wk).wk).wk) := Deriv.wk Deriv.ax
  have h1 := Deriv.allE (τ := .rat) x hPremise
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .rat) y h1
  deriv_norm at h2
  -- h2 : qlt (2^j * |x - y|, |f x - f y|) = 0
  have hClose : Deriv (ucLipCtx Γ Δ) (.eq (.app (.app (.app qclose (.add n j)) x) y) (.succ .zero)) := Deriv.ax
  exact Deriv.convQLipScale n j x y (.app f x) (.app f y) h2 hClose

-- MUTATION (does not build): Replacing witness `M = n + j` with `M = n` fails to build because
-- `convQLipScale` strictly requires input precision `n + j` to cancel the `2^j` Lipschitz expansion factor.

/-- Backward-compatibility alias for `uniContLipD`. -/
abbrev uniContD {Γ as : List Ty} {Δ : Ctx Γ as} := @uniContLipD Γ as Δ

/-- **The extracted modulus of continuity.**  Feed the realizer a function, a
scale `j`, a (contentless) realizer of the Lipschitz premise, and a precision
`n`; the first component of the resulting pair is the modulus. -/
def uniModulus (f : Q → Q) (j n : Nat) : Nat :=
  ((((extractClosed (uniContLipD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    f j (fun _ _ ↦ ())) n).1

/-- `close` at the value level, for checking the premise at instances. -/
def closeVal (k : Nat) (x y : Q) : Nat :=
  Q.ltN (let d := Q.sub x y; if d.num < 0 then Q.sub (Q.ofNat 0) d else d)
    (D.toQ (D.pow2neg k))

-- **The extracted program is the modulus.**  Doubling contracts the dyadic
-- scale by one, so its modulus is `n + 1`; a translation is an isometry, so
-- its modulus is `n`.  These are the answers the roadmap predicts.
#guard (List.range 6).map (uniModulus (fun q ↦ Q.add q q) 1)
  == [1, 2, 3, 4, 5, 6]
#guard (List.range 6).map (uniModulus (fun q ↦ Q.add q (Q.ofNat 1)) 0)
  == [0, 1, 2, 3, 4, 5]
#guard (List.range 4).map (uniModulus (fun q ↦ Q.add (Q.add q q) (Q.add q q)) 2)
  == [2, 3, 4, 5]

-- **The Lipschitz premise, verified at instances by value-level computation.**
#guard (List.range 5).all fun n ↦
  (List.range 8).all fun i ↦
    (let x := Q.of 1 3
     let y := Q.add x (D.toQ (D.pow2neg (n + 2 + i)))
     closeVal (n + 1) x y == 0 ||
       closeVal n (Q.add x x) (Q.add y y) == 1)

#print axioms uniContLipD
#print axioms uniContD
#print axioms uniModulus

end HAomega
