/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.RootOperator

/-!
# Definite integrals and the pointwise Newton–Leibniz formula

Room 2 of the closed universe (`docs/CLOSED_UNIVERSE_PLAN.md` §0.1). The
antiderivative of an expression is again an expression, `UExpr.integ e`, with
the same certified disk (`radiusParams`), so the definite integral is two
certified evaluations of it:

    ∫ₐᵇ f  :=  (∫f)(b) − (∫f)(a)          (UExpr.defIntegral, choice-free)

* `defIntegral_spec`: the result is within `2⁻ᵏ` of `S_N(∫f)(b) − S_N(∫f)(a)` for
  every `N` past the modulus — the certificate, from `approx_spec`.
* `evalPoly_integ_deriv`: `S_{N+1}(∫ f′)(x) = S_{N+1}(f)(x) − f(0)` for every `N`,
  from FTC2 on coefficients. So
* `newtonLeibniz`: `∫ₐᵇ f′` is within `2⁻ᵏ` of `S_N(f)(b) − S_N(f)(a)` — the
  Newton–Leibniz formula, as a certified computation.

Scope: as for every evaluation here, `a, b` lie in the certified disk of the
integrand — for `f′` that is the disk of `f′`, which differentiation halves.
-/

namespace HAomega

/-- **The definite integral** `∫ₐᵇ e`, to precision `2⁻ᵏ`. -/
def UExpr.defIntegral (e : UExpr) (a b : Q) (k : Nat) : Q :=
  Q.sub ((UExpr.integ e).approx b (k + 1)) ((UExpr.integ e).approx a (k + 1))

/-- **Its certificate.** -/
theorem UExpr.defIntegral_spec (e : UExpr) (h : e.Defined) (a b : Q)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ (e.radiusParams.2 + 1))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ (e.radiusParams.2 + 1)) (k d : Nat) :
    |((Jet.evalPoly ⟨(UExpr.integ e).eval⟩ ((k + 1) + (e.radiusParams.1 + 3) + d) b).val
        - (Jet.evalPoly ⟨(UExpr.integ e).eval⟩ ((k + 1) + (e.radiusParams.1 + 3) + d) a).val)
      - (e.defIntegral a b k).val| < 1 / (2 : Rat) ^ k := by
  have hI : (UExpr.integ e).Defined := h
  have hp : (UExpr.integ e).radiusParams = e.radiusParams := rfl
  have spec := fun (x : Q) (hx : |x.val| ≤ 1 / (2 : Rat) ^ (e.radiusParams.2 + 1)) ↦ by
    have := (UExpr.integ e).approx_spec hI x (by rw [hp]; exact hx) (k + 1) d
    rwa [extractedJetCauchyModulusComputed_eq, hp] at this
  have sa := spec a ha
  have sb := spec b hb
  unfold UExpr.defIntegral
  rw [Q.val_sub]
  have h2 : (1 : Rat) / 2 ^ (k + 1) + 1 / 2 ^ (k + 1) = 1 / 2 ^ k := by
    rw [pow_succ]; field_simp; ring
  rw [abs_lt] at sa sb ⊢
  constructor <;> linarith [sa.1, sa.2, sb.1, sb.2]

/-- **FTC2 on partial sums**: `S_{N+1}(∫ f′)(x) = S_{N+1}(f)(x) − f(0)`. -/
theorem evalPoly_integ_deriv (e : UExpr) (x : Q) : ∀ N : Nat,
    (Jet.evalPoly ⟨(UExpr.integ (UExpr.deriv e)).eval⟩ (N + 1) x).val
      = (Jet.evalPoly ⟨e.eval⟩ (N + 1) x).val - (e.eval 0).val
  | 0 => by
    rw [Jet.evalPoly_one, Jet.evalPoly_one]
    show (Q.zero).val = _
    rw [Q.val_zero]; ring
  | N + 1 => by
    rw [Jet.evalPoly_succ _ (N + 1), evalPoly_integ_deriv e x N, Jet.evalPoly_succ ⟨e.eval⟩ (N + 1)]
    have hc : ((UExpr.integ (UExpr.deriv e)).eval (N + 1)).val = (e.eval (N + 1)).val := by
      show (Q.div (Q.mul (Q.ofNat (N + 1)) (e.eval (N + 1))) (Q.ofNat (N + 1))).val = _
      rw [Q.val_div_all, Q.val_mul, Q.val_ofNat]
      have : ((N + 1 : Nat) : Rat) ≠ 0 := by positivity
      field_simp
    show _ + ((UExpr.integ (UExpr.deriv e)).eval (N + 1)).val * x.val ^ (N + 1) = _
    rw [hc]; ring

/-- **The Newton–Leibniz formula, certified**: `∫ₐᵇ f′` computed by
`defIntegral` is within `2⁻ᵏ` of `S_N(f)(b) − S_N(f)(a)` for every `N` past the
modulus. -/
theorem UExpr.newtonLeibniz (e : UExpr) (h : e.Defined) (a b : Q)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ ((UExpr.deriv e).radiusParams.2 + 1))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ ((UExpr.deriv e).radiusParams.2 + 1)) (k d : Nat) :
    |((Jet.evalPoly ⟨e.eval⟩ ((k + 1) + ((UExpr.deriv e).radiusParams.1 + 3) + d) b).val
        - (Jet.evalPoly ⟨e.eval⟩ ((k + 1) + ((UExpr.deriv e).radiusParams.1 + 3) + d) a).val)
      - ((UExpr.deriv e).defIntegral a b k).val| < 1 / (2 : Rat) ^ k := by
  have s := (UExpr.deriv e).defIntegral_spec h a b ha hb k d
  have hN : (k + 1) + ((UExpr.deriv e).radiusParams.1 + 3) + d
      = (k + ((UExpr.deriv e).radiusParams.1 + 3) + d) + 1 := by omega
  rw [hN] at s ⊢
  rw [evalPoly_integ_deriv e b, evalPoly_integ_deriv e a] at s
  have : ((Jet.evalPoly ⟨e.eval⟩ (k + ((UExpr.deriv e).radiusParams.1 + 3) + d + 1) b).val - (e.eval 0).val
      - ((Jet.evalPoly ⟨e.eval⟩ (k + ((UExpr.deriv e).radiusParams.1 + 3) + d + 1) a).val - (e.eval 0).val))
      = (Jet.evalPoly ⟨e.eval⟩ (k + ((UExpr.deriv e).radiusParams.1 + 3) + d + 1) b).val
        - (Jet.evalPoly ⟨e.eval⟩ (k + ((UExpr.deriv e).radiusParams.1 + 3) + d + 1) a).val := by ring
  rwa [this] at s

/-! ## Examples

`∫₀^{1/2} cos = sin(1/2)` on the disk `|x| ≤ 1/2` of `cos`, and the
Newton–Leibniz formula for `exp` on `[0, 1/4]` (the disk of `exp′`):
`∫₀^{1/4} exp′ = e^{1/4} − 1`. At `k = 30` the certificate is `2⁻³⁰`; checked
against floating point. -/

#guard UExpr.cos.radiusParams = (0, 0)
#guard (UExpr.deriv .exp).radiusParams = (1, 1)
#guard (let r := UExpr.cos.defIntegral ⟨0, 0⟩ ⟨1, 1⟩ 30
        (Float.ofInt r.num / Float.ofNat r.den - Float.sin 0.5).abs < 1e-8)
#guard (let r := (UExpr.deriv .exp).defIntegral ⟨0, 0⟩ ⟨1, 3⟩ 30
        (Float.ofInt r.num / Float.ofNat r.den - (Float.exp 0.25 - 1)).abs < 1e-8)

#print axioms UExpr.defIntegral
#print axioms UExpr.defIntegral_spec
#print axioms UExpr.newtonLeibniz

end HAomega
