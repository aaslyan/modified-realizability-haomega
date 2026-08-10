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

/-- `|z|` as an object term: the sign test drives a `recNat` used as a
conditional, which is how the extractor already compiles `∨`-elimination.
Absolute value is therefore *definable* — it is not a primitive. -/
def qabsT {Γ : List Ty} : Tm Γ (.arrow .rat .rat) :=
  .lam (.recNat (.var .here)
    (.lam (.lam (.qsub (.qnat .zero) (.var (.there (.there .here))))))
    (.qlt (.var .here) (.qnat .zero)))

/-- `close k x y` — the test `|x − y| < 2⁻ᵏ`, as a `0`/`1` numeral. -/
def qclose {Γ : List Ty} :
    Tm Γ (.arrow .nat (.arrow .rat (.arrow .rat .nat))) :=
  .lam (.lam (.lam
    (.qlt (.app qabsT (.qsub (.var (.there .here)) (.var .here)))
      (.app qpow2 (.var (.there (.there .here)))))))

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

/-- The Lipschitz premise: `f` contracts the dyadic scale by `j`. -/
abbrev ucLip (Γ : List Ty) : Formula (.nat :: .arrow .rat .rat :: Γ) (.arrow .rat (.arrow .rat (.arrow .nat (.arrow .unit .unit)))) :=
  (.all .rat (.all .rat (.all .nat (.imp (.eq (.app (.app (.app qclose (.add (.var .here) (.var (.there (.there (.there .here)))))) (.var (.there (.there .here)))) (.var (.there .here))) (.succ .zero)) (.eq (.app (.app (.app qclose (.var .here)) (.app (.var (.there (.there (.there (.there .here))))) (.var (.there (.there .here))))) (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here)))) (.succ .zero))))))

/-- The context at the point the premise is used. -/
abbrev ucCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.rat :: .rat :: .nat :: .nat :: .arrow .rat .rat :: Γ)
      (.unit :: (.arrow .rat (.arrow .rat (.arrow .nat (.arrow .unit .unit)))) :: as) :=
  .cons (.eq (.app (.app (.app qclose (.add (.var (.there (.there .here))) (.var (.there (.there (.there .here)))))) (.var (.there .here))) (.var .here)) (.succ .zero)) (.cons ((((ucLip Γ).wk).wk).wk) (((((Δ.wk).wk).wk).wk).wk))

/-- **Every `2ʲ`-contracting map is uniformly continuous, with modulus
`M = n + j`.**  The first component of the extracted realizer, as a function
of the precision `n`, *is* that modulus. -/
def uniContD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all (.arrow .rat .rat) (.all .nat (.imp (.all .rat (.all .rat (.all .nat (.imp (.eq (.app (.app (.app qclose (.add (.var .here) (.var (.there (.there (.there .here)))))) (.var (.there (.there .here)))) (.var (.there .here))) (.succ .zero)) (.eq (.app (.app (.app qclose (.var .here)) (.app (.var (.there (.there (.there (.there .here))))) (.var (.there (.there .here))))) (.app (.var (.there (.there (.there (.there .here))))) (.var (.there .here)))) (.succ .zero)))))) (.all .nat (.ex .nat (.all .rat (.all .rat (.imp (.eq (.app (.app (.app qclose (.var (.there (.there .here)))) (.var (.there .here))) (.var .here)) (.succ .zero)) (.eq (.app (.app (.app qclose (.var (.there (.there (.there .here))))) (.app (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there .here)))) (.app (.var (.there (.there (.there (.there (.there .here)))))) (.var .here))) (.succ .zero)))))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI (Deriv.allI ?_)))
  refine Deriv.exI (.add (.var .here) (.var (.there .here))) ?_
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  have hH : Deriv (ucCtx Γ Δ) ((((ucLip Γ).wk).wk).wk) := Deriv.wk Deriv.ax
  have h1 := Deriv.allE (τ := .rat) (.var (.there .here)) hH
  deriv_norm at h1
  have h2 := Deriv.allE (τ := .rat) (.var .here) h1
  deriv_norm at h2
  have h3 := Deriv.allE (τ := .nat) (.var (.there (.there .here))) h2
  deriv_norm at h3
  exact Deriv.impE h3 Deriv.ax

/-- **The extracted modulus of continuity.**  Feed the realizer a function, a
scale `j`, a (contentless) realizer of the Lipschitz premise, and a precision
`n`; the first component of the resulting pair is the modulus. -/
def uniModulus (f : Q → Q) (j n : Nat) : Nat :=
  ((((extractClosed (uniContD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    f j (fun _ _ _ _ ↦ ())) n).1

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

-- **The Lipschitz premise, discharged by computation at instances** — this is
-- the part a derivation cannot yet do, and the caller does instead.  For
-- doubling at scale `j = 1`: whenever `x` and `y` are within `2⁻⁽ⁿ⁺¹⁾`, their
-- doubles are within `2⁻ⁿ`.
#guard (List.range 5).all fun n ↦
  (List.range 8).all fun i ↦
    (let x := Q.of 1 3
     let y := Q.add x (D.toQ (D.pow2neg (n + 2 + i)))
     closeVal (n + 1) x y == 0 ||
       closeVal n (Q.add x x) (Q.add y y) == 1)

#print axioms uniContD
#print axioms uniModulus

end HAomega
