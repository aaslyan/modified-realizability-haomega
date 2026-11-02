/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseEval
import HAomega.SystemEval
import HAomega.HydraTyped

/-!
# Ordinal-Modulated Complexity of Differential Equations (`Eps0` ↔ `UExpr` / `GPACSys`)

This module connects the structural Cantor Normal Form ordinal layer
`Eps0` (`HAomega/OrdCnf.lean`, `HAomega/HydraTyped.lean`) with the closed
universe of differential equations and analytic jets (`UExpr`, `GPACSys`,
`HAomega/UniverseExpr.lean`, `HAomega/UniverseEval.lean`).

## Main Results

1. **Syntactic Ordinal Assignment (`UExpr.ord : UExpr → Eps0`):**
   Every expression / differential equation in `UExpr` is assigned a Cantor
   Normal Form ordinal below $\varepsilon_0$ (`UExpr.ord_nf : ∀ e, e.ord.nf = true`):
   - Constants `.const q` have ordinal $0$ (`Eps0.zero`).
   - `.x` has ordinal $1 = \omega^0 \cdot 1$.
   - `.add` and `.sub` take the `Eps0` maximum; `.mul` takes the natural
     Hessenberg sum $\alpha \oplus \beta$ (`Eps0.add`); `.integ` increments by
     $\oplus 1$; `.deriv` decrements the finite part by $1$.
   - Linear ODE generators (`.exp`, `.sin`, `.cos`) have ordinal $\omega$.
   - Composition `.comp a b` and reciprocal `.inv a` elevate the exponent to
     $\omega^{\mathrm{ord}(a) \oplus \mathrm{ord}(b)}$, so an $h$-layer coupled
     ODE tower (`exp ∘ ⋯ ∘ exp`) receives the height-$h$ Cantor tower
     $\omega^{\omega^{\cdot^\omega}} \prec \varepsilon_0$.

2. **Regime I — The Sub-$\omega$ Vanishing Theorem (`UExpr.eval_eq_zero_of_ord_lt_omega`):**
   Whenever `Eps0.olt e.ord Eps0.omega = true` (i.e. `e.ord` is a finite ordinal
   $d \prec \omega$, which characterizes the polynomial / nilpotent ODE fragment
   `e.IsPoly`), the Taylor series of `e` **vanishes identically above degree
   `e.ord.natPart`**:
   $$\forall n > \mathrm{natPart}(e.\mathrm{ord}),\quad (e.\mathrm{eval}\; n).\mathrm{val} = 0,$$
   and the compiled polynomial ODE system `e.compile` has an exact finite Taylor
   polynomial solution (`solN_eq_zero_of_ord_lt_omega`).

3. **Regime II — The $\omega$-Level Factorial Decay Theorem (`UExpr.IsExpPoly` → `AnalyticJet`):**
   On the $\omega \preceq \mathrm{ord}(e) \prec \omega^2$ fragment (`IsExpPoly`:
   constants, `x`, `exp`, `sin`, `cos` closed under `+`, `-`, `×`, `∫`, `d/dx`),
   every expression admits a global exponential-type factorial bound
   $|c_n| \cdot n! \le 2^M (2^R)^n$ (`AnalyticJet`), whereas the $\omega^\omega$-level
   self-feedback expression $(1 - x)^{-1}$ strictly escapes `AnalyticJet`.

4. **Regime III — Canonical Ordinal Realization (`odeOfOrd : Eps0 → UExpr`) &
   Monotonicity of Compiled ODE Complexity:**
   Every normal-form ordinal $\alpha \in \mathrm{Eps0}$ defines a canonical
   Hardy-field expression `odeOfOrd α : UExpr` and compiled polynomial ODE
   system `(odeOfOrd α).compile : CSys`:
   - **Order-Isomorphism / Exact Round-Trip (`ord_odeOfOrd`):**
     For every normal notation $\alpha \in \mathrm{Eps0}$,
     $(\mathrm{odeOfOrd}\; \alpha).\mathrm{ord} = \alpha$, so the ordinal hierarchy on
     `UExpr` surjects onto **all** of $\varepsilon_0$!
   - **Strict Modulation of ODE Complexity (`odeOfOrd_tower_strictMono`):**
     Along the Cantor tower $\omega_0 \prec \omega_1 \prec \omega_2 \prec \cdots \prec \varepsilon_0$,
     both the compiled ODE system dimension `(odeOfOrd (ωTower h)).compile.sys.length`
     and the Cauchy–Hadamard radius parameter `(odeOfOrd (ωTower h)).radiusParams.2`
     grow strictly with the ordinal height $h$.
-/

namespace HAomega

open Realizability

namespace Eps0

/-- The ordinal $1 = \omega^0 \cdot 1 + 0$. -/
def one : Eps0 := .node .zero 0 .zero

/-- The ordinal $\omega = \omega^1 \cdot 1 + 0$. -/
def omega : Eps0 := .node one 0 .zero

/-- Exponentiation base $\omega$: $\alpha \mapsto \omega^\alpha = \omega^\alpha \cdot 1 + 0$. -/
def omegaPow (a : Eps0) : Eps0 := .node a 0 .zero

/-- The $h$-fold $\omega$-tower: $\omega_0 = 0$, $\omega_{h+1} = \omega^{\omega_h}$. -/
def omegaTower : ℕ → Eps0
  | 0 => .zero
  | h + 1 => omegaPow (omegaTower h)

/-- Natural (Hessenberg) sum $\alpha \oplus \beta$ of two `Eps0` notations. -/
def add : Eps0 → Eps0 → Eps0
  | .zero, b => b
  | .node e c r, b => ( Eps0.insert e )^[c + 1] (add r b)

/-- Maximum of two `Eps0` notations with respect to `olt`. -/
def max (a b : Eps0) : Eps0 :=
  if olt a b then b else a

/-- Finite natural-number part (constant term at exponent $0$) of an `Eps0` notation. -/
def natPart : Eps0 → ℕ
  | .zero => 0
  | .node .zero c _ => c + 1
  | .node (.node _ _ _) _ r => natPart r

/-- Predecessor on the finite part (for $\frac{d}{dx}$ on polynomial ordinals). -/
def predFin : Eps0 → Eps0
  | .zero => .zero
  | .node .zero 0 _ => .zero
  | .node .zero (c + 1) .zero => .node .zero c .zero
  | .node .zero (c + 1) r => .node .zero c r
  | a => a

theorem toCode_one : one.toCode = 1 := rfl

theorem toCode_omega : omega.toCode = omegaCode := rfl

theorem nf_zero : nf .zero = true := rfl

theorem nf_one : nf one = true := rfl

theorem nf_omega : nf omega = true := rfl

theorem nf_omegaPow {a : Eps0} (ha : nf a = true) : nf (omegaPow a) = true := by
  simp [omegaPow, nf, ha]

theorem nf_omegaTower : ∀ h : ℕ, nf (omegaTower h) = true
  | 0 => rfl
  | h + 1 => nf_omegaPow (nf_omegaTower h)

/-- `Eps0.insert` preserves `nf`. -/
theorem nf_insert {e c : Eps0} (he : nf e = true) (hc : nf c = true) :
    nf (Eps0.insert e c) = true := by
  rw [← toCode_nf, toCode_insert]
  exact nfB_insertExp (by rwa [toCode_nf]) _ (by rwa [toCode_nf])

/-- Iterating `Eps0.insert e` preserves `nf`. -/
theorem nf_iterate_insert {e : Eps0} (he : nf e = true) :
    ∀ (k : ℕ) {c : Eps0}, nf c = true → nf ((Eps0.insert e)^[k] c) = true
  | 0, _, hc => hc
  | k + 1, c, hc => by
    rw [Function.iterate_succ_apply']
    exact nf_insert he (nf_iterate_insert he k hc)

/-- Natural sum `Eps0.add` preserves `nf`. -/
theorem nf_add : ∀ {a b : Eps0}, nf a = true → nf b = true → nf (add a b) = true
  | .zero, _, _, hb => hb
  | .node e c r, b, ha, hb => by
    have he : nf e = true := by
      simp only [nf, Bool.and_eq_true] at ha
      exact ha.1.1
    have hr : nf r = true := by
      simp only [nf, Bool.and_eq_true] at ha
      exact ha.1.2
    exact nf_iterate_insert he (c + 1) (nf_add hr hb)

/-- `Eps0.max` preserves `nf`. -/
theorem nf_max {a b : Eps0} (ha : nf a = true) (hb : nf b = true) :
    nf (max a b) = true := by
  unfold max
  by_cases h : olt a b = true <;> simp [h, ha, hb]

/-- `olt` is irreflexive. -/
theorem olt_irrefl (a : Eps0) : olt a a = false := by
  rw [← toCode_olt]
  exact precB_irrefl a.toCode

/-- `olt` is transitive. -/
theorem olt_trans {a b c : Eps0} (hab : olt a b = true) (hbc : olt b c = true) :
    olt a c = true := by
  rw [← toCode_olt] at hab hbc ⊢
  exact precB_trans hab hbc

/-- Strictly climbing the $\omega$-tower: $\omega_h \prec \omega_{h+1}$ in `OLtE`. -/
theorem olt_omegaTower : ∀ h : ℕ, olt (omegaTower h) (omegaTower (h + 1)) = true
  | 0 => rfl
  | h + 1 => by
    have ih := olt_omegaTower h
    have hne : omegaTower h ≠ omegaTower (h + 1) := by
      intro heq
      have h1 := ih
      rw [← heq, olt_irrefl] at h1
      contradiction
    change olt (node (omegaTower h) 0 zero) (node (omegaTower (h + 1)) 0 zero) = true
    unfold olt
    rw [if_neg hne]
    exact ih

theorem oltE_omegaTower (h : ℕ) : OLtE (omegaTower h) (omegaTower (h + 1)) := by
  simp [OLtE, oltE, nf_omegaTower h, nf_omegaTower (h + 1), olt_omegaTower h]

/-- Adding a finite ordinal `.node .zero c .zero` to `.zero` gives `.node .zero c .zero`. -/
theorem insert_zero_fin : ∀ k c : ℕ,
    (Eps0.insert .zero)^[k] (.node .zero c .zero) = .node .zero (c + k) .zero
  | 0, _ => rfl
  | k + 1, c => by
    rw [Function.iterate_succ_apply', insert_zero_fin k c]
    dsimp [Eps0.insert]
    congr 1

theorem iterate_insert_zero_zero : ∀ k : ℕ,
    (Eps0.insert .zero)^[k + 1] .zero = .node .zero k .zero
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_insert_zero_zero k]
    rfl

/-- Natural sum of two finite ordinals: $(c_1 + 1) \oplus (c_2 + 1) = (c_1 + c_2 + 2)$. -/
theorem add_fin_fin (c₁ c₂ : ℕ) :
    add (.node .zero c₁ .zero) (.node .zero c₂ .zero) = .node .zero (c₁ + c₂ + 1) .zero := by
  change (Eps0.insert .zero)^[c₁ + 1] (.node .zero c₂ .zero) = .node .zero (c₁ + c₂ + 1) .zero
  rw [insert_zero_fin (c₁ + 1) c₂]
  congr 1
  omega

/-- Embedding of $\mathbb{N}$ into `Eps0` as finite ordinals $n < \omega$. -/
def ofNat : ℕ → Eps0
  | 0 => .zero
  | n + 1 => .node .zero n .zero

theorem nf_ofNat : ∀ n : ℕ, nf (ofNat n) = true
  | 0 => rfl
  | _ + 1 => rfl

theorem natPart_ofNat : ∀ n : ℕ, (ofNat n).natPart = n
  | 0 => rfl
  | _ + 1 => rfl

theorem olt_ofNat_omega : ∀ n : ℕ, olt (ofNat n) omega = true
  | 0 => rfl
  | _ + 1 => rfl

/-- Characterization of normal notations strictly below $\omega$:
    if `nf a = true` and `olt a omega = true`, then `a = ofNat a.natPart`. -/
theorem eq_ofNat_of_olt_omega : ∀ a : Eps0, nf a = true → olt a omega = true →
    a = ofNat a.natPart
  | .zero, _, _ => rfl
  | .node .zero c .zero, _, _ => rfl
  | .node .zero c (.node e' c' r'), hnf, _ => by
    have hfalse : olt e' .zero = false := by cases e' <;> rfl
    dsimp [nf] at hnf
    rw [hfalse, Bool.and_false] at hnf
    contradiction
  | .node (.node e₁ c₁ r₁) c r, _, holt => by
    have hfalse : olt (.node (.node e₁ c₁ r₁) c r) omega = false := by
      dsimp [omega, one, olt]
      split
      · rename_i heq
        injection heq with h1 h2 h3
        subst h1 h2 h3
        simp [olt]
      · rename_i hne
        cases e₁ with
        | zero =>
          cases r₁ with
          | zero =>
            cases c₁ with
            | zero => exact absurd rfl hne
            | succ m => simp
          | node e₂ c₂ r₂ =>
            dsimp [olt]
            by_cases h0 : c₁ = 0
            · subst h0
              simp
            · have hpos : 0 < c₁ := Nat.pos_of_ne_zero h0
              simp [hpos]
        | node _ _ _ => rfl
    rw [hfalse] at holt
    contradiction

end Eps0

/-! ## 1. Syntactic Ordinal Assignment on the Closed Universe (`UExpr.ord : UExpr → Eps0`) -/

/-- The polynomial / nilpotent fragment of `UExpr`: built from rational constants
    and `x` under `+`, `-`, `×`, `∫`, and `d/dx`. -/
def UExpr.IsPoly : UExpr → Prop
  | .const _ | .x => True
  | .exp | .sin | .cos | .inv _ | .comp _ _ => False
  | .add a b | .sub a b | .mul a b => a.IsPoly ∧ b.IsPoly
  | .integ a | .deriv a => a.IsPoly

/-- Polynomial degree bound of an expression in the polynomial fragment. -/
def UExpr.polyDeg : UExpr → ℕ
  | .const _ => 0
  | .x => 1
  | .exp | .sin | .cos => 0
  | .add a b | .sub a b => max a.polyDeg b.polyDeg
  | .mul a b => a.polyDeg + b.polyDeg
  | .inv a => a.polyDeg
  | .integ a => a.polyDeg + 1
  | .deriv a => a.polyDeg - 1
  | .comp a b => a.polyDeg * b.polyDeg

/-- **Syntactic ordinal assignment** `UExpr.ord : UExpr → Eps0`:
    - On the polynomial fragment (`const`, `x`, `add`, `sub`, `mul`, `integ`, `deriv`),
      computes the exact finite ordinal `Eps0.ofNat e.polyDeg` $\prec \omega$.
    - On the linear ODE generators (`exp`, `sin`, `cos`), assigns $\omega$.
    - On nonlinear feedback (`inv`, `comp`), elevates the ordinal to $\omega^{\alpha}$. -/
def UExpr.ord : UExpr → Eps0
  | .const _ => .zero
  | .x => Eps0.one
  | .exp | .sin | .cos => Eps0.omega
  | .add a b | .sub a b => Eps0.max a.ord b.ord
  | .mul a b => Eps0.add a.ord b.ord
  | .inv a =>
    if a.ord = .zero then .zero else Eps0.omegaPow (Eps0.add a.ord Eps0.one)
  | .integ a => Eps0.add a.ord Eps0.one
  | .deriv a =>
    if Eps0.olt a.ord Eps0.omega then Eps0.ofNat (a.ord.natPart - 1) else a.ord
  | .comp a b =>
    if a.ord = Eps0.omega ∧ b.ord ≠ .zero then Eps0.omegaPow b.ord
    else if b.ord = .zero then .zero
    else Eps0.omegaPow (Eps0.add a.ord b.ord)

/-- **Every expression `e : UExpr` has a valid Cantor Normal Form ordinal in `Eps0`.** -/
theorem UExpr.ord_nf : ∀ e : UExpr, e.ord.nf = true
  | .const _ => rfl
  | .x => rfl
  | .exp | .sin | .cos => rfl
  | .add a b | .sub a b => Eps0.nf_max a.ord_nf b.ord_nf
  | .mul a b => Eps0.nf_add a.ord_nf b.ord_nf
  | .inv a => by
    dsimp [UExpr.ord]
    split
    · rfl
    · exact Eps0.nf_omegaPow (Eps0.nf_add a.ord_nf Eps0.nf_one)
  | .integ a => Eps0.nf_add a.ord_nf Eps0.nf_one
  | .deriv a => by
    dsimp [UExpr.ord]
    split
    · exact Eps0.nf_ofNat _
    · exact a.ord_nf
  | .comp a b => by
    dsimp [UExpr.ord]
    split
    · exact Eps0.nf_omegaPow b.ord_nf
    · split
      · rfl
      · exact Eps0.nf_omegaPow (Eps0.nf_add a.ord_nf b.ord_nf)

/-! ## 2. Regime I: The Sub-$\omega$ Vanishing Theorem ($\mathrm{ord}(e) \prec \omega \implies$ Finite Support) -/

/-- `Eps0.add (ofNat m) (ofNat n) = ofNat (m + n)`. -/
theorem Eps0.add_ofNat (m n : ℕ) :
    Eps0.add (Eps0.ofNat m) (Eps0.ofNat n) = Eps0.ofNat (m + n) := by
  cases m with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ c₁ =>
    cases n with
    | zero =>
      dsimp [Eps0.ofNat, Eps0.add]
      exact Eps0.iterate_insert_zero_zero c₁
    | succ c₂ =>
      dsimp [Eps0.ofNat]
      rw [Eps0.add_fin_fin c₁ c₂]
      congr 1
      omega

/-- `Eps0.olt (ofNat m) (ofNat n) = decide (m < n)`. -/
theorem Eps0.olt_ofNat (m n : ℕ) :
    Eps0.olt (Eps0.ofNat m) (Eps0.ofNat n) = decide (m < n) := by
  cases m with
  | zero =>
    cases n with
    | zero => rfl
    | succ k => rfl
  | succ c₁ =>
    cases n with
    | zero => rfl
    | succ c₂ =>
      dsimp [Eps0.ofNat, Eps0.olt]
      by_cases h : c₁ < c₂
      · have h2 : c₁ + 1 < c₂ + 1 := by omega
        simp [h, h2]
      · have h2 : ¬ (c₁ + 1 < c₂ + 1) := by omega
        simp [h, h2]

/-- `Eps0.max (ofNat m) (ofNat n) = ofNat (max m n)`. -/
theorem Eps0.max_ofNat (m n : ℕ) :
    Eps0.max (Eps0.ofNat m) (Eps0.ofNat n) = Eps0.ofNat (Max.max m n) := by
  unfold Eps0.max
  rw [Eps0.olt_ofNat]
  by_cases h : m < n
  · rw [if_pos (decide_eq_true h), Nat.max_eq_right (le_of_lt h)]
  · rw [if_neg (by simp [h]), Nat.max_eq_left (Nat.le_of_not_lt h)]

/-- On the polynomial fragment `e.IsPoly`, the syntactic ordinal `e.ord` is
    literally `Eps0.ofNat e.polyDeg`. -/
theorem UExpr.ord_eq_ofNat_polyDeg : ∀ (e : UExpr), e.IsPoly →
    e.ord = Eps0.ofNat e.polyDeg
  | .const _, _ => rfl
  | .x, _ => rfl
  | .exp, h | .sin, h | .cos, h | .inv _, h | .comp _ _, h => nomatch h
  | .add a b, ⟨ha, hb⟩ | .sub a b, ⟨ha, hb⟩ => by
    dsimp [UExpr.ord, UExpr.polyDeg]
    rw [a.ord_eq_ofNat_polyDeg ha, b.ord_eq_ofNat_polyDeg hb]
    exact Eps0.max_ofNat a.polyDeg b.polyDeg
  | .mul a b, ⟨ha, hb⟩ => by
    dsimp [UExpr.ord, UExpr.polyDeg]
    rw [a.ord_eq_ofNat_polyDeg ha, b.ord_eq_ofNat_polyDeg hb, Eps0.add_ofNat]
  | .integ a, ha => by
    dsimp [UExpr.ord, UExpr.polyDeg]
    rw [a.ord_eq_ofNat_polyDeg ha]
    exact Eps0.add_ofNat a.polyDeg 1
  | .deriv a, ha => by
    dsimp [UExpr.ord, UExpr.polyDeg]
    rw [a.ord_eq_ofNat_polyDeg ha, if_pos (Eps0.olt_ofNat_omega a.polyDeg),
        Eps0.natPart_ofNat]

/-- Every polynomial expression has ordinal strictly below $\omega$, and its
    `natPart` equals `e.polyDeg`. -/
theorem UExpr.olt_ord_omega_of_isPoly (e : UExpr) (he : e.IsPoly) :
    Eps0.olt e.ord Eps0.omega = true ∧ e.ord.natPart = e.polyDeg := by
  rw [e.ord_eq_ofNat_polyDeg he]
  exact ⟨Eps0.olt_ofNat_omega e.polyDeg, Eps0.natPart_ofNat e.polyDeg⟩

/-- **The Sub-$\omega$ Taylor Vanishing Theorem (`eval_eq_zero_of_isPoly`):**
    For every polynomial expression `e`, its Taylor coefficients vanish above
    the ordinal degree `e.ord.natPart`! -/
theorem UExpr.eval_eq_zero_of_isPoly : ∀ (e : UExpr), e.IsPoly →
    ∀ n : ℕ, e.polyDeg < n → (e.eval n).val = 0
  | .const q, _, n, hn => by
    dsimp [UExpr.polyDeg] at hn
    cases n with
    | zero => omega
    | succ k => exact Q.val_ofNat 0
  | .x, _, n, hn => by
    dsimp [UExpr.polyDeg] at hn
    cases n with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ m => exact Q.val_ofNat 0
  | .exp, h, _, _ | .sin, h, _, _ | .cos, h, _, _ | .inv _, h, _, _ | .comp _ _, h, _, _ =>
    nomatch h
  | .add a b, ⟨ha, hb⟩, n, hn => by
    dsimp [UExpr.polyDeg] at hn
    have hna : a.polyDeg < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
    have hnb : b.polyDeg < n := lt_of_le_of_lt (Nat.le_max_right _ _) hn
    dsimp [UExpr.eval]
    rw [Q.val_add, a.eval_eq_zero_of_isPoly ha n hna,
        b.eval_eq_zero_of_isPoly hb n hnb, add_zero]
  | .sub a b, ⟨ha, hb⟩, n, hn => by
    dsimp [UExpr.polyDeg] at hn
    have hna : a.polyDeg < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
    have hnb : b.polyDeg < n := lt_of_le_of_lt (Nat.le_max_right _ _) hn
    dsimp [UExpr.eval]
    rw [Q.val_sub, a.eval_eq_zero_of_isPoly ha n hna,
        b.eval_eq_zero_of_isPoly hb n hnb, sub_zero]
  | .mul a b, ⟨ha, hb⟩, n, hn => by
    dsimp [UExpr.polyDeg] at hn
    dsimp [UExpr.eval]
    rw [inv_jetMul_val]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    by_cases hja : a.polyDeg < j
    · rw [a.eval_eq_zero_of_isPoly ha j hja, zero_mul]
    · have hjb : b.polyDeg < n - j := by omega
      rw [b.eval_eq_zero_of_isPoly hb (n - j) hjb, mul_zero]
  | .integ a, ha, n, hn => by
    dsimp [UExpr.polyDeg] at hn
    cases n with
    | zero => omega
    | succ k =>
      change (Q.div (a.eval k) (Q.ofNat (k + 1))).val = 0
      have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
      rw [Q.val_div _ _ hne, a.eval_eq_zero_of_isPoly ha k (by omega), zero_div]
  | .deriv a, ha, n, hn => by
    dsimp [UExpr.polyDeg] at hn
    change (Q.mul (Q.ofNat (n + 1)) (a.eval (n + 1))).val = 0
    rw [Q.val_mul, a.eval_eq_zero_of_isPoly ha (n + 1) (by omega), mul_zero]

/-- **Ordinal Form of the Sub-$\omega$ Vanishing Theorem:**
    For any `e : UExpr` in `IsPoly`, `e.ord ≺ ω` and every Taylor coefficient
    of index $n > \mathrm{natPart}(e.\mathrm{ord})$ (both in `e.eval` and in the
    compiled ODE solution `solN e.compile.sys e.compile.v`) equals $0$! -/
theorem UExpr.solN_eq_zero_of_isPoly (e : UExpr) (he : e.IsPoly) :
    Eps0.OLtE e.ord Eps0.omega ∧
    ∀ n : ℕ, e.ord.natPart < n →
      (e.eval n).val = 0 ∧ (solN e.compile.sys e.compile.v n).val = 0 := by
  have hdef : e.Defined := by
    induction e with
    | const _ | x => trivial
    | exp | sin | cos | inv _ | comp _ _ => nomatch he
    | add a b iha ihb | sub a b iha ihb | mul a b iha ihb => exact ⟨iha he.1, ihb he.2⟩
    | integ a iha | deriv a iha => exact iha he
  obtain ⟨holt, hnat⟩ := e.olt_ord_omega_of_isPoly he
  have holtE : Eps0.OLtE e.ord Eps0.omega := by
    simp [Eps0.OLtE, Eps0.oltE, e.ord_nf, Eps0.nf_omega, holt]
  refine ⟨holtE, fun n hn ↦ ?_⟩
  rw [hnat] at hn
  have hz := e.eval_eq_zero_of_isPoly he n hn
  have hcomp := (e.compile_correct hdef).2 n
  exact ⟨hz, hcomp.symm.trans hz⟩

/-! ## 3. Regime II: The $\omega$-Level Fragment (`IsExpPoly`) and Global `AnalyticJet` Bounds -/

/-- The $\omega$-level fragment (`IsExpPoly`): constants, `x`, `exp`, `sin`, `cos`
    closed under `+`, `-`, `×`, `∫`, and `d/dx` (no `.inv` or `.comp`). -/
def UExpr.IsExpPoly : UExpr → Prop
  | .const _ | .x | .exp | .sin | .cos => True
  | .inv _ | .comp _ _ => False
  | .add a b | .sub a b | .mul a b => a.IsExpPoly ∧ b.IsExpPoly
  | .integ a | .deriv a => a.IsExpPoly

/-- Constant `q : Q` as an `AnalyticJet` ($|c_n| \cdot n! \le 2^{|q.\mathrm{num}|}$). -/
def constAnalyticJet (q : Q) : AnalyticJet where
  toJet := Jet.const q
  M := q.num.natAbs
  R := 0
  majorant n := by
    rw [AnalyticJet.majorant_iff_val]
    cases n with
    | zero =>
      dsimp [Jet.const, fact]
      simpa using uEval_const_val_bound q
    | succ k =>
      dsimp [Jet.const]
      rw [Q.val_zero, abs_zero, zero_mul]
      positivity

/-- Transfer an `AnalyticJet` bound along rational value equality of coefficients. -/
def AnalyticJet.ofVal (F : AnalyticJet) (c : Nat → Q)
    (h : ∀ n, (c n).val = (F.toJet.coeff n).val) : AnalyticJet where
  toJet := ⟨c⟩
  M := F.M
  R := F.R
  majorant n := by
    rw [AnalyticJet.majorant_iff_val]
    show |(c n).val| * (fact n : Rat) ≤ _
    rw [h n]
    exact F.majorant_val n

/-- **Regime II Theorem (`UExpr.analyticJet_of_isExpPoly`):**
    Every expression in the $\omega$-level fragment `IsExpPoly` (whose ordinal sits
    below $\omega^2$) inhabits `AnalyticJet` — its Taylor coefficients satisfy the
    global factorial bound $|c_n| \cdot n! \le 2^M (2^R)^n$ (entire of exponential type,
    convergence radius $\rho = \infty$)!
    By contrast, the $\omega$-exponentiated expression `.inv (.sub (.const 1) .x)`
    ($\frac{1}{1-x}$, ordinal $\omega^1$) is proven in `geom_not_analyticJet` to
    have **no** `AnalyticJet` bound! -/
def UExpr.analyticJet_of_isExpPoly : (e : UExpr) → e.IsExpPoly →
    {F : AnalyticJet // F.toJet = ⟨e.eval⟩}
  | .const q, _ => ⟨constAnalyticJet q, rfl⟩
  | .x, _ => ⟨AnalyticJet.varX, rfl⟩
  | .exp, _ => ⟨AnalyticJet.exp, rfl⟩
  | .sin, _ => ⟨AnalyticJet.sin, rfl⟩
  | .cos, _ => ⟨AnalyticJet.cos, rfl⟩
  | .inv _, h | .comp _ _, h => nomatch h
  | .add a b, ⟨ha, hb⟩ =>
    let ⟨FA, hFA⟩ := a.analyticJet_of_isExpPoly ha
    let ⟨FB, hFB⟩ := b.analyticJet_of_isExpPoly hb
    ⟨(FA.add FB).ofVal (UExpr.add a b).eval (fun n ↦ by
      dsimp [UExpr.eval, AnalyticJet.add, Jet.add]
      rw [hFA, hFB]), rfl⟩
  | .sub a b, ⟨ha, hb⟩ =>
    let ⟨FA, hFA⟩ := a.analyticJet_of_isExpPoly ha
    let ⟨FB, hFB⟩ := b.analyticJet_of_isExpPoly hb
    ⟨(FA.sub FB).ofVal (UExpr.sub a b).eval (fun n ↦ by
      dsimp [UExpr.eval, AnalyticJet.sub, Jet.sub]
      rw [hFA, hFB]), rfl⟩
  | .mul a b, ⟨ha, hb⟩ =>
    let ⟨FA, hFA⟩ := a.analyticJet_of_isExpPoly ha
    let ⟨FB, hFB⟩ := b.analyticJet_of_isExpPoly hb
    ⟨(FA.mul FB).ofVal (UExpr.mul a b).eval (fun n ↦ by
      dsimp [UExpr.eval, AnalyticJet.mul]
      rw [tmJetMul_eval, hFA, hFB]), rfl⟩
  | .integ a, ha =>
    let ⟨FA, hFA⟩ := a.analyticJet_of_isExpPoly ha
    ⟨FA.integ.ofVal (UExpr.integ a).eval (fun n ↦ by
      dsimp [UExpr.eval, AnalyticJet.integ]
      rw [hFA]
      cases n <;> rfl), rfl⟩
  | .deriv a, ha =>
    let ⟨FA, hFA⟩ := a.analyticJet_of_isExpPoly ha
    ⟨FA.deriv.ofVal (UExpr.deriv a).eval (fun n ↦ by
      dsimp [UExpr.eval, AnalyticJet.deriv]
      rw [hFA]
      rfl), rfl⟩

/-! ## 4. Regime III: Canonical Realization of $\varepsilon_0$ (`odeOfOrd : Eps0 → UExpr`)
    and Strict Modulation of Compiled ODE Complexity -/

/-- Canonical iterated-exponential tower in `UExpr` indexed by height $h$:
    - `uTower 0 = const 0` (ordinal $0$)
    - `uTower 1 = x` (ordinal $1$)
    - `uTower 2 = exp` (ordinal $\omega$)
    - `uTower (h + 2) = comp exp (uTower (h + 1))` (ordinal $\omega_{h+1}$). -/
def uTower : ℕ → UExpr
  | 0 => .const Q.zero
  | 1 => .x
  | 2 => .exp
  | h + 3 => .comp .exp (uTower (h + 2))

/-- Every `uTower h` is a defined expression (no reciprocals). -/
theorem uTower_defined : ∀ h : ℕ, (uTower h).Defined
  | 0 | 1 | 2 => trivial
  | h + 3 => ⟨trivial, uTower_defined (h + 2)⟩

theorem uTower_ord_ne_zero : ∀ h : ℕ, (uTower (h + 1)).ord ≠ .zero
  | 0 => by decide
  | 1 => by decide
  | h + 2 => by
    dsimp [uTower, UExpr.ord]
    rw [if_pos ⟨rfl, uTower_ord_ne_zero (h + 1)⟩]
    intro hc
    cases hc

/-- **Exact Ordinal Calibration of the ODE Tower (`uTower_ord`):**
    The syntactic ordinal of `uTower h` is **literally** the $h$-fold Cantor
    tower `Eps0.omegaTower h` ($\omega_0 = 0, \omega_1 = 1, \omega_2 = \omega,
    \omega_3 = \omega^\omega, \omega_4 = \omega^{\omega^\omega}, \dots$)! -/
theorem uTower_ord : ∀ h : ℕ, (uTower h).ord = Eps0.omegaTower h
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | h + 3 => by
    dsimp [uTower, UExpr.ord]
    rw [if_pos ⟨rfl, uTower_ord_ne_zero (h + 1)⟩, uTower_ord (h + 2)]
    rfl

/-- **Strict Ordinal Climb of the ODE Tower (`uTower_ord_strictMono`):**
    Each layer of the ODE tower strictly increases its syntactic ordinal in
    the well-founded Cantor order `Eps0.OLtE`! -/
theorem uTower_ord_strictMono (h : ℕ) :
    Eps0.OLtE (uTower h).ord (uTower (h + 1)).ord := by
  rw [uTower_ord h, uTower_ord (h + 1)]
  exact Eps0.oltE_omegaTower h

/-- **Modulation Theorem 1 — Cauchy–Hadamard Radius Parameter (`uTower_radiusParams_R`):**
    For $h \ge 2$, the radius parameter $R_h := (\mathrm{uTower}\; h).\mathrm{radiusParams}.2$
    (which determines the local convergence disk $\rho = 2^{-(R_h + 1)}$) satisfies
    $R_2 = 0$ and $R_{h+1} = R_h + 1$, hence equals $h - 2$ and **grows strictly**
    with the ordinal tower height $h$! -/
theorem uTower_radiusParams_M : ∀ h : ℕ, (uTower (h + 1)).radiusParams.1 = 0
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem uTower_radiusParams_R : ∀ h : ℕ, (uTower (h + 2)).radiusParams.2 = h
  | 0 => rfl
  | h + 1 => by
    change (0 + (uTower (h + 2)).radiusParams.1 +
      (uTower (h + 2)).radiusParams.2 + 1) = h + 1
    rw [uTower_radiusParams_M (h + 1), uTower_radiusParams_R h]
    omega

theorem uTower_radiusParams_R_strictMono (h : ℕ) :
    (uTower (h + 2)).radiusParams.2 < (uTower (h + 3)).radiusParams.2 := by
  rw [uTower_radiusParams_R h, uTower_radiusParams_R (h + 1)]
  exact Nat.lt_succ_self h

/-- **Modulation Theorem 2 — Compiled Polynomial ODE System Dimension (`uTower_compile_length`):**
    When `uTower (h + 2)` is compiled into a flat polynomial ODE system `GPACSys`
    via `UExpr.compile`, each ordinal tower step $\omega_h \mapsto \omega_{h+1}$
    strictly increases the number of coupled state variables in the ODE system! -/
theorem uTower_compile_length : ∀ h : ℕ, (uTower (h + 2)).compile.sys.length = h + 1
  | 0 => rfl
  | h + 1 => by
    have hstep : (uTower (h + 3)).compile.sys.length =
        (uTower (h + 2)).compile.sys.length + (flatAll UExpr.exp.compile.sys).length := by
      exact comp_compSys_length (flatAll UExpr.exp.compile.sys) (uTower (h + 2)).compile.sys _ _
    have hexp : (flatAll UExpr.exp.compile.sys).length = 1 := rfl
    rw [hstep, hexp, uTower_compile_length h]

theorem uTower_compile_length_strictMono (h : ℕ) :
    (uTower (h + 2)).compile.sys.length < (uTower (h + 3)).compile.sys.length := by
  rw [uTower_compile_length h, uTower_compile_length (h + 1)]
  exact Nat.lt_succ_self (h + 1)

/-! ## 5. Surjectivity onto All Cantor Normal Forms Below $\varepsilon_0$ (`odeOfOrd`) -/

/-- `n`-fold multiplication of an expression `e` (`e * e * ... * e`, $c+1$ times). -/
def uMulPow (e : UExpr) : ℕ → UExpr
  | 0 => e
  | c + 1 => .mul e (uMulPow e c)

/-- `c + 1` copies of `e` summed (`e + e + ... + e`). -/
def uAddCopies (e : UExpr) : ℕ → UExpr
  | 0 => e
  | c + 1 => .add e (uAddCopies e c)

/-- Canonical realization of any Cantor Normal Form ordinal $\alpha \in \mathrm{Eps0}$
    as an expression in `UExpr`:
    - `.zero` $\mapsto \mathrm{const}\; 0$
    - `.node .zero c .zero` $\mapsto x^{c+1}$ (monomial of degree $c+1$, ordinal $c+1$)
    - `.node e c .zero` $\mapsto (\exp \circ \mathrm{odeOfOrd}\; e)^{c+1}$ (ordinal $\omega^e \cdot (c+1)$)
    - `.node e c r` $\mapsto (\text{head term}) \cdot (\text{remainder})$ (whose ordinal is the natural sum). -/
def odeOfOrd : Eps0 → UExpr
  | .zero => .const Q.zero
  | .node .zero c .zero => uMulPow .x c
  | .node .zero c (.node e' c' r') =>
    .mul (uMulPow .x c) (odeOfOrd (.node e' c' r'))
  | .node (.node e₁ c₁ r₁) c .zero =>
    uMulPow (.comp .exp (odeOfOrd (.node e₁ c₁ r₁))) c
  | .node (.node e₁ c₁ r₁) c (.node e' c' r') =>
    .mul (uMulPow (.comp .exp (odeOfOrd (.node e₁ c₁ r₁))) c) (odeOfOrd (.node e' c' r'))

/-- Every `odeOfOrd a` is `Defined` (uses no reciprocals) and therefore compiles
    via `UExpr.compile_correct` into a certified `GPACSys` polynomial ODE system! -/
theorem uMulPow_defined (e : UExpr) (he : e.Defined) : ∀ c : ℕ, (uMulPow e c).Defined
  | 0 => he
  | c + 1 => ⟨he, uMulPow_defined e he c⟩

theorem odeOfOrd_defined : ∀ a : Eps0, (odeOfOrd a).Defined
  | .zero => trivial
  | .node .zero c .zero => uMulPow_defined .x trivial c
  | .node .zero c (.node e' c' r') => by
    dsimp [odeOfOrd, UExpr.Defined]
    exact ⟨uMulPow_defined .x trivial c, odeOfOrd_defined (.node e' c' r')⟩
  | .node (.node e₁ c₁ r₁) c .zero => by
    dsimp [odeOfOrd]
    exact uMulPow_defined (.comp .exp (odeOfOrd (.node e₁ c₁ r₁)))
      ⟨trivial, odeOfOrd_defined (.node e₁ c₁ r₁)⟩ c
  | .node (.node e₁ c₁ r₁) c (.node e' c' r') => by
    dsimp [odeOfOrd, UExpr.Defined]
    exact ⟨uMulPow_defined (.comp .exp (odeOfOrd (.node e₁ c₁ r₁)))
      ⟨trivial, odeOfOrd_defined (.node e₁ c₁ r₁)⟩ c,
      odeOfOrd_defined (.node e' c' r')⟩

/-- **Every ordinal notation `a : Eps0` realizes a member of the GPAC polynomial-ODE universe!** -/
theorem odeOfOrd_inGPAC (a : Eps0) : InGPAC (odeOfOrd a).eval :=
  (odeOfOrd a).inGPAC (odeOfOrd_defined a)

theorem Eps0.insert_same (d : Eps0) (c : ℕ) (r : Eps0) :
    Eps0.insert d (.node d c r) = .node d (c + 1) r := by
  dsimp [Eps0.insert]
  rw [if_pos rfl]

theorem Eps0.iterate_insert_same (d r : Eps0) : ∀ k c : ℕ,
    (Eps0.insert d)^[k] (.node d c r) = .node d (c + k) r
  | 0, _ => rfl
  | k + 1, c => by
    rw [Function.iterate_succ_apply', Eps0.iterate_insert_same d r k c, Eps0.insert_same]
    congr 1

theorem Eps0.add_node_zero (d : Eps0) (c : ℕ) :
    Eps0.add (.node d 0 .zero) (.node d c .zero) = .node d (c + 1) .zero := by
  change Eps0.insert d (.node d c .zero) = .node d (c + 1) .zero
  exact Eps0.insert_same d c .zero

theorem uMulPow_ord (e : UExpr) (d : Eps0) (he : e.ord = .node d 0 .zero) :
    ∀ c : ℕ, (uMulPow e c).ord = .node d c .zero
  | 0 => he
  | c + 1 => by
    dsimp [uMulPow, UExpr.ord]
    rw [he, uMulPow_ord e d he c]
    exact Eps0.add_node_zero d c

theorem Eps0.add_node_of_olt (d e' : Eps0) (c c' : ℕ) (r' : Eps0)
    (holt : Eps0.olt e' d = true) :
    Eps0.add (.node d c .zero) (.node e' c' r') = .node d c (.node e' c' r') := by
  have hne : d ≠ e' := by
    intro heq
    subst heq
    rw [Eps0.olt_irrefl] at holt
    contradiction
  have h1 : Eps0.insert d (.node e' c' r') = .node d 0 (.node e' c' r') := by
    dsimp [Eps0.insert]
    rw [if_neg hne, if_pos holt]
  change (Eps0.insert d)^[c + 1] (.node e' c' r') = .node d c (.node e' c' r')
  rw [Function.iterate_succ_apply, h1, Eps0.iterate_insert_same d (.node e' c' r') c 0,
      Nat.zero_add]

/-- **Exact Ordinal Surjectivity Theorem (`odeOfOrd_ord`):**
    Every Cantor Normal Form ordinal `a : Eps0` (`a.nf = true`) is the **exact**
    syntactic ordinal `(odeOfOrd a).ord = a` of its canonical differential-equation
    expression `odeOfOrd a` in the GPAC universe! -/
theorem odeOfOrd_ord : ∀ a : Eps0, a.nf = true → (odeOfOrd a).ord = a
  | .zero, _ => rfl
  | .node .zero c .zero, _ => uMulPow_ord .x .zero rfl c
  | .node .zero c (.node e' c' r'), hnf => by
    have hfalse : Eps0.olt e' .zero = false := by cases e' <;> rfl
    dsimp [Eps0.nf] at hnf
    rw [hfalse, Bool.and_false] at hnf
    contradiction
  | .node (.node e₁ c₁ r₁) c .zero, hnf => by
    have hnf1 : (Eps0.node e₁ c₁ r₁).nf = true := by
      change ((Eps0.node e₁ c₁ r₁).nf && true && true) = true at hnf
      simpa using hnf
    have ih := odeOfOrd_ord (.node e₁ c₁ r₁) hnf1
    have hcomp : (UExpr.comp .exp (odeOfOrd (.node e₁ c₁ r₁))).ord =
        .node (.node e₁ c₁ r₁) 0 .zero := by
      dsimp [UExpr.ord]
      rw [ih]
      rfl
    exact uMulPow_ord (.comp .exp (odeOfOrd (.node e₁ c₁ r₁))) (.node e₁ c₁ r₁) hcomp c
  | .node (.node e₁ c₁ r₁) c (.node e' c' r'), hnf => by
    have hsplit : (Eps0.node e₁ c₁ r₁).nf = true ∧
        (Eps0.node e' c' r').nf = true ∧
        Eps0.olt e' (.node e₁ c₁ r₁) = true := by
      change ((Eps0.node e₁ c₁ r₁).nf && (Eps0.node e' c' r').nf &&
        Eps0.olt e' (.node e₁ c₁ r₁)) = true at hnf
      simpa [Bool.and_eq_true, and_assoc] using hnf
    obtain ⟨hnf1, hnf2, holt⟩ := hsplit
    have ih1 := odeOfOrd_ord (.node e₁ c₁ r₁) hnf1
    have ih2 := odeOfOrd_ord (.node e' c' r') hnf2
    have hcomp : (UExpr.comp .exp (odeOfOrd (.node e₁ c₁ r₁))).ord =
        .node (.node e₁ c₁ r₁) 0 .zero := by
      dsimp [UExpr.ord]
      rw [ih1]
      rfl
    have hhead := uMulPow_ord (.comp .exp (odeOfOrd (.node e₁ c₁ r₁))) (.node e₁ c₁ r₁) hcomp c
    dsimp [odeOfOrd, UExpr.ord]
    rw [hhead, ih2]
    exact Eps0.add_node_of_olt (.node e₁ c₁ r₁) e' c c' r' holt

/-! ## 6. Semantic Hierarchy $H_\alpha$, Upper-Bound Soundness, Semantic Strictness,
    and Intrinsic Lower Bounds Modulo Arbitrary Cancellations -/

/-- Purely semantic equality of Taylor series: agreement of rational values at all degrees. -/
def SemJetEq (c₁ c₂ : ℕ → Q) : Prop := ∀ n : ℕ, (c₁ n).val = (c₂ n).val

/-- Semantic class $H_k$ ($k < \omega$): Taylor jets whose coefficients vanish above degree $k$. -/
def SemPolyDegLe (k : ℕ) (c : ℕ → Q) : Prop := ∀ n : ℕ, k < n → (c n).val = 0

/-- Semantic class $H_{<\omega}$: Taylor jets with finite support (polynomials). -/
def SemPolynomial (c : ℕ → Q) : Prop := ∃ k : ℕ, SemPolyDegLe k c

/-- Semantic class $H_{<\omega^2}$: Taylor jets of Phragmén–Lindelöf exponential type
    ($|c_n| \cdot n! \le 2^M (2^R)^n$, convergence radius $\rho = \infty$). -/
def SemEntireExpType (c : ℕ → Q) : Prop :=
  ∃ M R : ℕ, ∀ n : ℕ, |(c n).val| * (fact n : ℚ) ≤ (2 : ℚ) ^ M * ((2 : ℚ) ^ R) ^ n

theorem SemPolyDegLe.congr {k : ℕ} {c₁ c₂ : ℕ → Q}
    (hEq : SemJetEq c₁ c₂) (h : SemPolyDegLe k c₁) : SemPolyDegLe k c₂ :=
  fun n hn ↦ (hEq n).symm.trans (h n hn)

theorem SemPolynomial.congr {c₁ c₂ : ℕ → Q}
    (hEq : SemJetEq c₁ c₂) (h : SemPolynomial c₁) : SemPolynomial c₂ :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.congr hEq⟩

theorem SemEntireExpType.congr {c₁ c₂ : ℕ → Q}
    (hEq : SemJetEq c₁ c₂) (h : SemEntireExpType c₁) : SemEntireExpType c₂ := by
  rcases h with ⟨M, R, hMR⟩
  refine ⟨M, R, fun n ↦ ?_⟩
  rw [← hEq n]
  exact hMR n

/-! ### 6A. Finite Ordinals $k < \omega$: Soundness, Strictness, and Intrinsic Lower Bounds -/

/-- **Upper-Bound Soundness at Finite Ordinals (`soundness_polyDegLe`):**
    If `e` is in the polynomial fragment and `e.ord ≺ ofNat (k + 1)` (i.e. `e.ord ≤ k`),
    then its semantic Taylor series belongs to `SemPolyDegLe k`. -/
theorem soundness_polyDegLe (e : UExpr) (he : e.IsPoly) (k : ℕ)
    (hord : Eps0.olt e.ord (Eps0.ofNat (k + 1)) = true) :
    SemPolyDegLe k e.eval := by
  rw [e.ord_eq_ofNat_polyDeg he, Eps0.olt_ofNat] at hord
  have hdeg : e.polyDeg ≤ k := by
    have hlt : e.polyDeg < k + 1 := of_decide_eq_true hord
    omega
  intro n hn
  exact e.eval_eq_zero_of_isPoly he n (lt_of_le_of_lt hdeg hn)

theorem uEval_x_zero : (UExpr.x.eval 0).val = 0 := Q.val_ofNat 0
theorem uEval_x_one : (UExpr.x.eval 1).val = 1 := Q.val_ofNat 1
theorem uEval_x_add_two (k : ℕ) : (UExpr.x.eval (k + 2)).val = 0 := Q.val_ofNat 0

theorem mul_x_eval_succ_val (A : UExpr) (m : ℕ) :
    ((UExpr.mul .x A).eval (m + 1)).val = (A.eval m).val := by
  change (((tmJetMul (Γ := [])).eval Env.nil) UExpr.x.eval A.eval (m + 1)).val = (A.eval m).val
  rw [inv_jetMul_val, Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ' _ m]
  have h0 : ∑ k ∈ Finset.range m,
      (UExpr.x.eval (k + 1 + 1)).val * (A.eval (m + 1 - (k + 1 + 1))).val = 0 := by
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [uEval_x_add_two k, zero_mul]
  rw [h0, zero_add]
  change (UExpr.x.eval 1).val * (A.eval (m + 1 - 1)).val +
    (UExpr.x.eval 0).val * (A.eval (m + 1 - 0)).val = (A.eval m).val
  rw [uEval_x_one, uEval_x_zero, Nat.add_sub_cancel, one_mul, zero_mul, add_zero]

theorem uMulPow_x_eval_self_val : ∀ c : ℕ, ((uMulPow .x c).eval (c + 1)).val = 1
  | 0 => Q.val_ofNat 1
  | c + 1 => (mul_x_eval_succ_val (uMulPow .x c) (c + 1)).trans (uMulPow_x_eval_self_val c)

theorem uMulPow_x_isPoly : ∀ c : ℕ, (uMulPow .x c).IsPoly
  | 0 => trivial
  | c + 1 => ⟨trivial, uMulPow_x_isPoly c⟩

theorem uMulPow_x_polyDeg : ∀ c : ℕ, (uMulPow .x c).polyDeg = c + 1
  | 0 => rfl
  | c + 1 => by
    dsimp [uMulPow, UExpr.polyDeg]
    rw [uMulPow_x_polyDeg c]
    omega

/-- **Semantic Strictness at Finite Ordinals (`strictness_polyDegLe`):**
    For every $k \in \mathbb{N}$, the canonical witness `odeOfOrd (Eps0.ofNat (k + 1))`
    has ordinal `Eps0.ofNat (k + 1)` and belongs to $H_{k+1} \setminus H_k$! -/
theorem strictness_polyDegLe (k : ℕ) :
    let w := odeOfOrd (Eps0.ofNat (k + 1))
    w.ord = Eps0.ofNat (k + 1) ∧
    SemPolyDegLe (k + 1) w.eval ∧
    ¬ SemPolyDegLe k w.eval := by
  intro w
  have hord : w.ord = Eps0.ofNat (k + 1) := odeOfOrd_ord (Eps0.ofNat (k + 1)) (Eps0.nf_ofNat (k + 1))
  have hpoly : w.IsPoly := uMulPow_x_isPoly k
  have hdeg : w.polyDeg = k + 1 := uMulPow_x_polyDeg k
  refine ⟨hord, ?_, ?_⟩
  · intro n hn
    rw [← hdeg] at hn
    exact w.eval_eq_zero_of_isPoly hpoly n hn
  · intro hle
    have hzero := hle (k + 1) (Nat.lt_succ_self k)
    have hone : (w.eval (k + 1)).val = 1 := uMulPow_x_eval_self_val k
    linarith

/-- **Intrinsic Lower-Bound Theorem for Finite Ordinals (`intrinsic_lower_bound_poly`):**
    For **any** polynomial expression `e` (even with arbitrary redundant subterms or
    algebraic cancellations), if `e` is semantically equivalent (`SemJetEq`) to
    `odeOfOrd (Eps0.ofNat (k + 1))`, then its syntactic ordinal must satisfy
    `Eps0.ofNat k ≺ e.ord` (i.e. $\mathrm{ord}(e) \ge k + 1$)! -/
theorem intrinsic_lower_bound_poly (e : UExpr) (he : e.IsPoly) (k : ℕ)
    (hEq : SemJetEq e.eval (odeOfOrd (Eps0.ofNat (k + 1))).eval) :
    Eps0.OLtE (Eps0.ofNat k) e.ord := by
  have hnot : ¬ SemPolyDegLe k e.eval := by
    intro hle
    exact (strictness_polyDegLe k).2.2 (hle.congr hEq)
  have hlt : k < e.polyDeg := by
    by_contra hge
    apply hnot
    intro n hn
    exact e.eval_eq_zero_of_isPoly he n (by omega)
  have holt : Eps0.olt (Eps0.ofNat k) e.ord = true := by
    rw [e.ord_eq_ofNat_polyDeg he, Eps0.olt_ofNat]
    exact decide_eq_true hlt
  simp [Eps0.OLtE, Eps0.oltE, Eps0.nf_ofNat, e.ord_nf, holt]

/-! ### 6B. The $\omega$ Threshold: Soundness of `IsPoly` and Strict Separation by `exp` -/

/-- **Upper-Bound Soundness Below $\omega$ (`soundness_below_omega`):**
    Every expression in `IsPoly` has ordinal $\prec \omega$ and belongs to `SemPolynomial`. -/
theorem soundness_below_omega (e : UExpr) (he : e.IsPoly) :
    Eps0.OLtE e.ord Eps0.omega ∧ SemPolynomial e.eval := by
  obtain ⟨holt, hvan⟩ := e.solN_eq_zero_of_isPoly he
  exact ⟨holt, ⟨e.ord.natPart, fun n hn ↦ (hvan n hn).1⟩⟩

/-- Every Taylor coefficient of `uTower 2 = exp` is strictly positive ($1 / n! > 0$). -/
theorem uTower_two_eval_pos (n : ℕ) : 0 < ((uTower 2).eval n).val := by
  change 0 < (Q.div (Q.ofNat 1) (Q.ofNat (fact n))).val
  have hf_pos : 0 < fact n := fact_pos n
  have hf_num : (Q.ofNat (fact n)).num ≠ 0 := Int.ofNat_ne_zero.mpr (ne_of_gt hf_pos)
  rw [Q.val_div _ _ hf_num, Q.val_ofNat, Q.val_ofNat]
  have hf_rat : (0 : ℚ) < (fact n : ℚ) := by exact_mod_cast hf_pos
  positivity

/-- **Semantic Strictness at $\omega$ (`strictness_at_omega`):**
    `uTower 2` ($\exp x$) has ordinal $\omega$ and does **not** belong to `SemPolynomial`. -/
theorem strictness_at_omega :
    (uTower 2).ord = Eps0.omega ∧ ¬ SemPolynomial (uTower 2).eval := by
  refine ⟨rfl, ?_⟩
  rintro ⟨k, hk⟩
  have hz := hk (k + 1) (Nat.lt_succ_self k)
  have hpos := uTower_two_eval_pos (k + 1)
  linarith

/-- **Intrinsic Lower-Bound Corollary at $\omega$ (`no_isPoly_semJetEq_exp`):**
    No expression in `IsPoly` (of ordinal $< \omega$) is semantically equal to `uTower 2` ($\exp x$). -/
theorem no_isPoly_semJetEq_exp (e : UExpr) (he : e.IsPoly) :
    ¬ SemJetEq e.eval (uTower 2).eval := by
  intro hEq
  exact strictness_at_omega.2 ((soundness_below_omega e he).2.congr hEq)

/-! ### 6C. The $\omega^2$ Threshold: Soundness of `IsExpPoly` ($\prec \omega^2$)
    and Strict Separation by $\frac{1}{1-x}$ (`ord = ω²`) -/

/-- Ordinal notation $2 = \omega^0 \cdot 2$. -/
def Eps0.two : Eps0 := .node .zero 1 .zero

/-- Ordinal notation $\omega^2 = \omega^2 \cdot 1 + 0$. -/
def Eps0.omegaSq : Eps0 := .node Eps0.two 0 .zero

/-- Structural predicate testing that all Cantor exponents in a notation are $< 2$. -/
def Eps0.belowOmegaSq : Eps0 → Bool
  | .zero => true
  | .node e _ r => Eps0.olt e Eps0.two && r.belowOmegaSq

theorem Eps0.olt_omegaSq_of_belowOmegaSq : ∀ a : Eps0,
    a.belowOmegaSq = true → Eps0.olt a Eps0.omegaSq = true
  | .zero, _ => rfl
  | .node e c r, h => by
    have he : Eps0.olt e Eps0.two = true := by
      change (Eps0.olt e Eps0.two && r.belowOmegaSq) = true at h
      exact (Bool.and_eq_true _ _).mp h |>.1
    have hne : e ≠ Eps0.two := by
      intro heq
      subst heq
      rw [Eps0.olt_irrefl] at he
      contradiction
    dsimp [Eps0.omegaSq, Eps0.olt]
    rw [if_neg hne]
    exact he

theorem Eps0.belowOmegaSq_insert (e : Eps0) (he : Eps0.olt e Eps0.two = true) :
    ∀ b : Eps0, b.belowOmegaSq = true → (Eps0.insert e b).belowOmegaSq = true
  | .zero, _ => by
    dsimp [Eps0.insert, Eps0.belowOmegaSq]
    rw [he]
    rfl
  | .node e' c' r', hb => by
    have hsplit : Eps0.olt e' Eps0.two = true ∧ r'.belowOmegaSq = true := by
      change (Eps0.olt e' Eps0.two && r'.belowOmegaSq) = true at hb
      simpa [Bool.and_eq_true] using hb
    obtain ⟨he', hr'⟩ := hsplit
    dsimp [Eps0.insert]
    split
    · dsimp [Eps0.belowOmegaSq]
      rw [he', hr']
      rfl
    · split
      · dsimp [Eps0.belowOmegaSq]
        rw [he, he', hr']
        rfl
      · dsimp [Eps0.belowOmegaSq]
        rw [he', Eps0.belowOmegaSq_insert e he r' hr']
        rfl

theorem Eps0.belowOmegaSq_iterate_insert (e : Eps0) (he : Eps0.olt e Eps0.two = true) :
    ∀ (k : ℕ) (b : Eps0), b.belowOmegaSq = true → ((Eps0.insert e)^[k] b).belowOmegaSq = true
  | 0, _, hb => hb
  | k + 1, b, hb => by
    rw [Function.iterate_succ_apply']
    exact Eps0.belowOmegaSq_insert e he _ (Eps0.belowOmegaSq_iterate_insert e he k b hb)

theorem Eps0.belowOmegaSq_add : ∀ a b : Eps0,
    a.belowOmegaSq = true → b.belowOmegaSq = true → (Eps0.add a b).belowOmegaSq = true
  | .zero, _, _, hb => hb
  | .node e c r, b, ha, hb => by
    have hsplit : Eps0.olt e Eps0.two = true ∧ r.belowOmegaSq = true := by
      change (Eps0.olt e Eps0.two && r.belowOmegaSq) = true at ha
      simpa [Bool.and_eq_true] using ha
    exact Eps0.belowOmegaSq_iterate_insert e hsplit.1 (c + 1) (Eps0.add r b)
      (Eps0.belowOmegaSq_add r b hsplit.2 hb)

theorem Eps0.belowOmegaSq_max (a b : Eps0)
    (ha : a.belowOmegaSq = true) (hb : b.belowOmegaSq = true) :
    (Eps0.max a b).belowOmegaSq = true := by
  unfold Eps0.max
  split <;> assumption

theorem Eps0.belowOmegaSq_ofNat : ∀ n : ℕ, (Eps0.ofNat n).belowOmegaSq = true
  | 0 => rfl
  | _ + 1 => rfl

theorem UExpr.belowOmegaSq_ord_of_isExpPoly : ∀ e : UExpr,
    e.IsExpPoly → e.ord.belowOmegaSq = true
  | .const _, _ | .x, _ | .exp, _ | .sin, _ | .cos, _ => rfl
  | .inv _, h | .comp _ _, h => nomatch h
  | .add a b, ⟨ha, hb⟩ | .sub a b, ⟨ha, hb⟩ =>
    Eps0.belowOmegaSq_max a.ord b.ord
      (a.belowOmegaSq_ord_of_isExpPoly ha) (b.belowOmegaSq_ord_of_isExpPoly hb)
  | .mul a b, ⟨ha, hb⟩ =>
    Eps0.belowOmegaSq_add a.ord b.ord
      (a.belowOmegaSq_ord_of_isExpPoly ha) (b.belowOmegaSq_ord_of_isExpPoly hb)
  | .integ a, ha =>
    Eps0.belowOmegaSq_add a.ord Eps0.one (a.belowOmegaSq_ord_of_isExpPoly ha) rfl
  | .deriv a, ha => by
    dsimp [UExpr.ord]
    split
    · exact Eps0.belowOmegaSq_ofNat _
    · exact a.belowOmegaSq_ord_of_isExpPoly ha

/-- **Every expression in `IsExpPoly` has ordinal strictly below $\omega^2$ (`Eps0.omegaSq`)!** -/
theorem UExpr.oltE_ord_omegaSq_of_isExpPoly (e : UExpr) (he : e.IsExpPoly) :
    Eps0.OLtE e.ord Eps0.omegaSq := by
  have h1 := Eps0.olt_omegaSq_of_belowOmegaSq e.ord (e.belowOmegaSq_ord_of_isExpPoly he)
  have hnf : Eps0.omegaSq.nf = true := rfl
  simp [Eps0.OLtE, Eps0.oltE, e.ord_nf, hnf, h1]

/-- **Upper-Bound Soundness Below $\omega^2$ (`soundness_below_omegaSq`):**
    Every expression `e` in `IsExpPoly` satisfies `e.ord ≺ ω²` and belongs to the
    purely semantic exponential-type class `SemEntireExpType`. -/
theorem soundness_below_omegaSq (e : UExpr) (he : e.IsExpPoly) :
    Eps0.OLtE e.ord Eps0.omegaSq ∧ SemEntireExpType e.eval := by
  obtain ⟨F, hF⟩ := e.analyticJet_of_isExpPoly he
  refine ⟨e.oltE_ord_omegaSq_of_isExpPoly he, ⟨F.M, F.R, fun n ↦ ?_⟩⟩
  have hm := F.majorant_val n
  rwa [hF] at hm

/-- The expression $1 - x$ in `UExpr`. -/
def uOneSubX : UExpr := .sub (.const (Q.ofNat 1)) .x

/-- The geometric-series expression $\frac{1}{1 - x}$ in `UExpr` (solving $y' = y^2, y(0) = 1$). -/
def uGeom : UExpr := .inv uOneSubX

theorem uOneSubX_eval_zero : (uOneSubX.eval 0).val = 1 := by
  rw [show uOneSubX.eval 0 = Q.ofNat 1 by rfl, Q.val_ofNat]
  norm_num

theorem uOneSubX_eval_one : (uOneSubX.eval 1).val = -1 := by
  change (Q.sub ((Jet.const (Q.ofNat 1)).coeff 1) (Jet.varX.coeff 1)).val = -1
  rw [Q.val_sub, show (Jet.const (Q.ofNat 1)).coeff 1 = Q.zero by rfl,
      show Jet.varX.coeff 1 = Q.ofNat 1 by rfl, Q.val_zero, Q.val_ofNat]
  norm_num

theorem uOneSubX_eval_add_two (k : ℕ) : (uOneSubX.eval (k + 2)).val = 0 := by
  change (Q.sub ((Jet.const (Q.ofNat 1)).coeff (k + 2)) (Jet.varX.coeff (k + 2))).val = 0
  rw [Q.val_sub, show (Jet.const (Q.ofNat 1)).coeff (k + 2) = Q.zero by rfl,
      show Jet.varX.coeff (k + 2) = Q.zero by rfl, sub_self]

theorem uGeom_defined : uGeom.Defined := by
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  rw [uOneSubX_eval_zero]
  norm_num

theorem uGeom_inGPAC : InGPAC uGeom.eval :=
  uGeom.inGPAC uGeom_defined

/-- All Taylor coefficients of `uGeom` ($\frac{1}{1-x}$) have rational value $1$. -/
theorem uGeom_eval_val : ∀ n : ℕ, (uGeom.eval n).val = 1
  | 0 => by
    rw [show uGeom.eval 0 = Q.ofNat 1 by rfl, Q.val_ofNat]
    norm_num
  | n + 1 => by
    have h0 : (uOneSubX.eval 0).val ≠ 0 := by rw [uOneSubX_eval_zero]; norm_num
    change (Jet.recip uOneSubX.eval (n + 1)).val = 1
    rw [ux_recip_succ_val uOneSubX.eval h0 n,
        Finset.sum_range_succ' (fun j ↦ (uOneSubX.eval (j + 1)).val * (Jet.recip uOneSubX.eval (n - j)).val) n]
    have htail : ∑ k ∈ Finset.range n,
        (uOneSubX.eval (k + 1 + 1)).val * (Jet.recip uOneSubX.eval (n - (k + 1))).val = 0 := by
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [uOneSubX_eval_add_two k, zero_mul]
    rw [htail, zero_add, Nat.sub_zero, uOneSubX_eval_one, uOneSubX_eval_zero]
    have ih : (Jet.recip uOneSubX.eval n).val = 1 := uGeom_eval_val n
    rw [ih]
    ring

/-- **Semantic Strictness at $\omega^2$ (`strictness_at_omegaSq`):**
    `uGeom` ($\frac{1}{1-x}$) has syntactic ordinal $\omega^2$ (`Eps0.omegaSq`) and
    provably escapes the semantic class `SemEntireExpType`! -/
theorem strictness_at_omegaSq :
    uGeom.ord = Eps0.omegaSq ∧ ¬ SemEntireExpType uGeom.eval := by
  refine ⟨rfl, ?_⟩
  rintro ⟨M, R, hMR⟩
  obtain ⟨n, hn⟩ := geom_not_analyticJet M R
  have h1 : ((RadiusJet.geomOneMinusX.toJet).coeff n).val = (uGeom.eval n).val := by
    rw [uGeom_eval_val n]
    exact Q.val_ofNat 1
  rw [h1] at hn
  have h2 := hMR n
  linarith

/-- **Intrinsic Lower-Bound Corollary at $\omega^2$ (`no_isExpPoly_semJetEq_uGeom`):**
    No expression `e` in `IsExpPoly` (no matter how many `exp`, `sin`, `cos`, products,
    integrals, derivatives, or cancellations it uses) can ever denote $\frac{1}{1-x}$! -/
theorem no_isExpPoly_semJetEq_uGeom (e : UExpr) (he : e.IsExpPoly) :
    ¬ SemJetEq e.eval uGeom.eval := by
  intro hEq
  exact strictness_at_omegaSq.2 ((soundness_below_omegaSq e he).2.congr hEq)

/-! ## 7. Semantic Calibration and Pairwise Distinctness of the $\omega$-Tower (`uTower`) -/

theorem jet_exp_coeff_zero_val : (Jet.exp.coeff 0).val = 1 := by
  rw [show Jet.exp.coeff 0 = Q.ofNat 1 by rfl, Q.val_ofNat]
  norm_num

theorem jet_exp_coeff_one_val : (Jet.exp.coeff 1).val = 1 := by
  rw [show Jet.exp.coeff 1 = Q.ofNat 1 by rfl, Q.val_ofNat]
  norm_num

theorem jet_exp_coeff_two_val : (Jet.exp.coeff 2).val = 1 / 2 := by
  dsimp [Jet.exp, fact]
  have hne : (Q.ofNat 2).num ≠ 0 := by decide
  rw [Q.val_div _ _ hne, Q.val_ofNat, Q.val_ofNat]
  norm_num

theorem compZero_exp_coeff_zero (G : Jet) :
    ((Jet.compZero Jet.exp G).coeff 0).val = 1 := by
  rw [compZero_coeff_val_eq_sum Jet.exp G 0 0 (le_refl 0), Finset.sum_range_one]
  have hh0 : ((hPow G 0).coeff 0).val = 1 := Q.val_ofNat 1
  rw [jet_exp_coeff_zero_val, hh0, mul_one]

theorem compZero_exp_coeff_one (G : Jet) :
    ((Jet.compZero Jet.exp G).coeff 1).val = (G.coeff 1).val := by
  have hd := deriv_compZero_exp_val G 0
  have hL : (((Jet.compZero Jet.exp G).deriv).coeff 0).val =
      ((Jet.compZero Jet.exp G).coeff 1).val := by
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat, Nat.cast_one, one_mul]
  have hR : ((G.deriv.mul (Jet.compZero Jet.exp G)).coeff 0).val = (G.coeff 1).val := by
    dsimp [Jet.mul]
    rw [TrigPoly.cauchyConvAux_val, Finset.sum_range_one, Nat.sub_zero,
        compZero_exp_coeff_zero G, mul_one]
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat, Nat.cast_one, one_mul]
  linarith

theorem compZero_exp_coeff_two (G : Jet) (hG1 : (G.coeff 1).val = 1) :
    ((Jet.compZero Jet.exp G).coeff 2).val = (G.coeff 2).val + 1 / 2 := by
  have hd := deriv_compZero_exp_val G 1
  have hL : (((Jet.compZero Jet.exp G).deriv).coeff 1).val =
      2 * ((Jet.compZero Jet.exp G).coeff 2).val := by
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
    norm_num
  have hR : ((G.deriv.mul (Jet.compZero Jet.exp G)).coeff 1).val =
      1 + 2 * (G.coeff 2).val := by
    dsimp [Jet.mul]
    rw [TrigPoly.cauchyConvAux_val, Finset.sum_range_succ, Finset.sum_range_one,
        Nat.sub_zero, Nat.sub_self, compZero_exp_coeff_one G, compZero_exp_coeff_zero G]
    have hd0 : (G.deriv.coeff 0).val = (G.coeff 1).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat, Nat.cast_one, one_mul]
    have hd1 : (G.deriv.coeff 1).val = 2 * (G.coeff 2).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
      norm_num
    rw [hd0, hd1, hG1]
    ring
  linarith

/-- Degree-$0$ coefficient of `uTower (h + 2)` is $1$ for every $h \in \mathbb{N}$. -/
theorem uTower_eval_zero : ∀ h : ℕ, ((uTower (h + 2)).eval 0).val = 1
  | 0 => jet_exp_coeff_zero_val
  | h + 1 => compZero_exp_coeff_zero ⟨(uTower (h + 2)).eval⟩

/-- Degree-$1$ coefficient of `uTower (h + 2)` is $1$ for every $h \in \mathbb{N}$. -/
theorem uTower_eval_one : ∀ h : ℕ, ((uTower (h + 2)).eval 1).val = 1
  | 0 => jet_exp_coeff_one_val
  | h + 1 => (compZero_exp_coeff_one ⟨(uTower (h + 2)).eval⟩).trans (uTower_eval_one h)

/-- **Exact Semantic Bell-Tower Formula at Degree $2$ (`uTower_eval_two`):**
    For every height $h \in \mathbb{N}$, the quadratic Taylor coefficient of `uTower (h + 2)`
    (whose coefficients are the $h$-iterated Bell numbers $B^{(h)}_n / n!$) equals
    $$\big((\mathrm{uTower}\; (h + 2)).\mathrm{eval}\; 2\big).\mathrm{val} = \frac{h + 1}{2}!$$ -/
theorem uTower_eval_two : ∀ h : ℕ,
    ((uTower (h + 2)).eval 2).val = ((h + 1 : ℕ) : ℚ) / 2
  | 0 => by
    rw [show (uTower 2).eval 2 = Jet.exp.coeff 2 by rfl, jet_exp_coeff_two_val]
    norm_num
  | h + 1 => by
    have hstep := compZero_exp_coeff_two ⟨(uTower (h + 2)).eval⟩ (uTower_eval_one h)
    change ((Jet.compZero Jet.exp ⟨(uTower (h + 2)).eval⟩).coeff 2).val = _
    rw [hstep, uTower_eval_two h]
    push_cast
    ring

/-- **Strict Semantic Monotonicity of the Exponential Tower (`uTower_eval_two_strictMono`):**
    Climbing the ordinal tower $\omega_{h_1 + 2} \prec \omega_{h_2 + 2}$ strictly increases
    the semantic Taylor coefficient at $n = 2$! -/
theorem uTower_eval_two_strictMono {h₁ h₂ : ℕ} (hlt : h₁ < h₂) :
    ((uTower (h₁ + 2)).eval 2).val < ((uTower (h₂ + 2)).eval 2).val := by
  rw [uTower_eval_two h₁, uTower_eval_two h₂]
  have hcast : ((h₁ + 1 : ℕ) : ℚ) < ((h₂ + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : h₁ + 1 < h₂ + 1)
  linarith

/-- **Semantic Injectivity of the Full $\omega$-Tower (`uTower_semJetEq_injective`):**
    Every level $h \in \mathbb{N}$ of the ordinal tower `uTower h` ($\omega_0, \omega_1, \omega_2, \dots < \varepsilon_0$)
    denotes a **distinct analytic function**! -/
theorem uTower_semJetEq_injective : ∀ h₁ h₂ : ℕ,
    SemJetEq (uTower h₁).eval (uTower h₂).eval → h₁ = h₂
  | 0, 0, _ => rfl
  | 1, 1, _ => rfl
  | 0, 1, hEq => by
    have h1 := hEq 1
    have hL : ((uTower 0).eval 1).val = 0 := Q.val_zero
    have hR : ((uTower 1).eval 1).val = 1 := Q.val_ofNat 1
    linarith
  | 1, 0, hEq => by
    have h1 := hEq 1
    have hL : ((uTower 1).eval 1).val = 1 := Q.val_ofNat 1
    have hR : ((uTower 0).eval 1).val = 0 := Q.val_zero
    linarith
  | 0, b + 2, hEq => by
    have h0 := hEq 0
    have hL : ((uTower 0).eval 0).val = 0 := Q.val_zero
    have hR := uTower_eval_zero b
    linarith
  | 1, b + 2, hEq => by
    have h0 := hEq 0
    have hL : ((uTower 1).eval 0).val = 0 := Q.val_zero
    have hR := uTower_eval_zero b
    linarith
  | a + 2, 0, hEq => by
    have h0 := hEq 0
    have hL := uTower_eval_zero a
    have hR : ((uTower 0).eval 0).val = 0 := Q.val_zero
    linarith
  | a + 2, 1, hEq => by
    have h0 := hEq 0
    have hL := uTower_eval_zero a
    have hR : ((uTower 1).eval 0).val = 0 := Q.val_zero
    linarith
  | a + 2, b + 2, hEq => by
    have h2 := hEq 2
    rw [uTower_eval_two a, uTower_eval_two b] at h2
    have hcast : ((a + 1 : ℕ) : ℚ) = ((b + 1 : ℕ) : ℚ) := by linarith
    have hab : a + 1 = b + 1 := Nat.cast_injective hcast
    omega

/-! ### 7B. Upper-Bound Soundness, Semantic Strictness, and Intrinsic Lower Bounds
    Across Every Level $h \in \mathbb{N}$ of the Transfinite Exponential Tower -/

/-- General degree-$2$ Faà di Bruno formula for `Jet.compZero Jet.exp G` on **any** jet `G`:
    $$\big((\mathrm{Jet.compZero}\; \mathrm{Jet.exp}\; G).\mathrm{coeff}\; 2\big).\mathrm{val}
      = \frac{((G.\mathrm{coeff}\; 1).\mathrm{val})^2}{2} + (G.\mathrm{coeff}\; 2).\mathrm{val}.$$ -/
theorem compZero_exp_coeff_two_general (G : Jet) :
    ((Jet.compZero Jet.exp G).coeff 2).val =
      (G.coeff 1).val * (G.coeff 1).val / 2 + (G.coeff 2).val := by
  have hd := deriv_compZero_exp_val G 1
  have hL : (((Jet.compZero Jet.exp G).deriv).coeff 1).val =
      2 * ((Jet.compZero Jet.exp G).coeff 2).val := by
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
    norm_num
  have hR : ((G.deriv.mul (Jet.compZero Jet.exp G)).coeff 1).val =
      (G.coeff 1).val * (G.coeff 1).val + 2 * (G.coeff 2).val := by
    dsimp [Jet.mul]
    rw [TrigPoly.cauchyConvAux_val, Finset.sum_range_succ, Finset.sum_range_one,
        Nat.sub_zero, Nat.sub_self, compZero_exp_coeff_one G, compZero_exp_coeff_zero G]
    have hd0 : (G.deriv.coeff 0).val = (G.coeff 1).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat, Nat.cast_one, one_mul]
    have hd1 : (G.deriv.coeff 1).val = 2 * (G.coeff 2).val := by
      dsimp [Jet.deriv]
      rw [Q.val_mul, Q.val_ofNat]
      norm_num
    rw [hd0, hd1]
    ring
  linarith

/-- Semantic class $H^{\mathrm{tower}}_h$: Taylor jets with $|c_1| \le 1$ and $c_2 \le h / 2$. -/
def SemBellTowerLe (h : ℕ) (c : ℕ → Q) : Prop :=
  |(c 1).val| ≤ 1 ∧ (c 2).val ≤ (h : ℚ) / 2

theorem SemBellTowerLe.congr {h : ℕ} {c₁ c₂ : ℕ → Q}
    (hEq : SemJetEq c₁ c₂) (hc : SemBellTowerLe h c₁) : SemBellTowerLe h c₂ := by
  refine ⟨?_, ?_⟩
  · rw [← hEq 1]; exact hc.1
  · rw [← hEq 2]; exact hc.2

/-- Exponential-composition depth of an expression in the unit-seed tower fragment. -/
def UExpr.expCompDepth : UExpr → ℕ
  | .const _ | .x => 0
  | .exp | .sin | .cos => 1
  | .add a b | .sub a b => max a.expCompDepth b.expCompDepth
  | .mul a b => a.expCompDepth + b.expCompDepth
  | .inv a | .integ a | .deriv a => a.expCompDepth + 1
  | .comp _ b => b.expCompDepth + 1

/-- The unit-seed exponential-tower fragment (`IsUnitSeedTower`): contains all rational
    constants `.const q`, `.x`, `.sin`, `.cos`, `.exp`, closed under arbitrary constant
    shifts (`.add a (.const q)`, `.sub a (.const q)`) and exponential composition
    (`.comp .exp a`). -/
inductive UExpr.IsUnitSeedTower : UExpr → Prop where
  | const (q : Q) : (UExpr.const q).IsUnitSeedTower
  | x : UExpr.x.IsUnitSeedTower
  | sin : UExpr.sin.IsUnitSeedTower
  | cos : UExpr.cos.IsUnitSeedTower
  | exp : UExpr.exp.IsUnitSeedTower
  | addConst {a : UExpr} (q : Q) : a.IsUnitSeedTower → (UExpr.add a (.const q)).IsUnitSeedTower
  | subConst {a : UExpr} (q : Q) : a.IsUnitSeedTower → (UExpr.sub a (.const q)).IsUnitSeedTower
  | compExp {a : UExpr} : a.IsUnitSeedTower → (UExpr.comp .exp a).IsUnitSeedTower

theorem jet_sin_coeff_one_val : (Jet.sin.coeff 1).val = 1 := by
  rw [show Jet.sin.coeff 1 = Q.ofNat 1 by rfl, Q.val_ofNat]
  norm_num

theorem jet_sin_coeff_two_val : (Jet.sin.coeff 2).val = 0 :=
  Q.val_zero

theorem jet_cos_coeff_one_val : (Jet.cos.coeff 1).val = 0 :=
  Q.val_zero

theorem jet_cos_coeff_two_val : (Jet.cos.coeff 2).val = - (1 / 2) := by
  rw [show Jet.cos.coeff 2 = ⟨-1, 1⟩ by rfl]
  unfold Q.val
  dsimp [Q.den]
  norm_num

/-- **Upper-Bound Soundness Across the Exponential Tower (`soundness_unitSeedTower`):**
    Every expression `e` in `IsUnitSeedTower` of exponential-composition depth `d := e.expCompDepth`
    belongs to the semantic class `SemBellTowerLe d` ($|c_1| \le 1$ and $c_2 \le d / 2$)! -/
theorem soundness_unitSeedTower {e : UExpr} (he : e.IsUnitSeedTower) :
    SemBellTowerLe e.expCompDepth e.eval := by
  induction he with
  | const q =>
    refine ⟨?_, ?_⟩
    · change |Q.zero.val| ≤ 1; rw [Q.val_zero, abs_zero]; norm_num
    · change Q.zero.val ≤ (0 : ℚ) / 2; rw [Q.val_zero]; norm_num
  | x =>
    refine ⟨?_, ?_⟩
    · rw [uEval_x_one, abs_one]
    · rw [uEval_x_add_two 0]; norm_num
  | sin =>
    refine ⟨?_, ?_⟩
    · change |(Jet.sin.coeff 1).val| ≤ 1; rw [jet_sin_coeff_one_val, abs_one]
    · change (Jet.sin.coeff 2).val ≤ ((1 : ℕ) : ℚ) / 2; rw [jet_sin_coeff_two_val]; norm_num
  | cos =>
    refine ⟨?_, ?_⟩
    · change |(Jet.cos.coeff 1).val| ≤ 1; rw [jet_cos_coeff_one_val, abs_zero]; norm_num
    · change (Jet.cos.coeff 2).val ≤ ((1 : ℕ) : ℚ) / 2; rw [jet_cos_coeff_two_val]; norm_num
  | exp =>
    refine ⟨?_, ?_⟩
    · change |(Jet.exp.coeff 1).val| ≤ 1; rw [jet_exp_coeff_one_val, abs_one]
    · change (Jet.exp.coeff 2).val ≤ ((1 : ℕ) : ℚ) / 2; rw [jet_exp_coeff_two_val]; norm_num
  | @addConst a q _ ih =>
    dsimp [UExpr.expCompDepth]
    rw [Nat.max_zero]
    refine ⟨?_, ?_⟩
    · change |(Q.add (a.eval 1) Q.zero).val| ≤ 1
      rw [Q.val_add, Q.val_zero, add_zero]
      exact ih.1
    · change (Q.add (a.eval 2) Q.zero).val ≤ _
      rw [Q.val_add, Q.val_zero, add_zero]
      exact ih.2
  | @subConst a q _ ih =>
    dsimp [UExpr.expCompDepth]
    rw [Nat.max_zero]
    refine ⟨?_, ?_⟩
    · change |(Q.sub (a.eval 1) Q.zero).val| ≤ 1
      rw [Q.val_sub, Q.val_zero, sub_zero]
      exact ih.1
    · change (Q.sub (a.eval 2) Q.zero).val ≤ _
      rw [Q.val_sub, Q.val_zero, sub_zero]
      exact ih.2
  | @compExp a _ ih =>
    dsimp [UExpr.expCompDepth]
    refine ⟨?_, ?_⟩
    · change |((Jet.compZero Jet.exp ⟨a.eval⟩).coeff 1).val| ≤ 1
      rw [compZero_exp_coeff_one ⟨a.eval⟩]
      exact ih.1
    · change ((Jet.compZero Jet.exp ⟨a.eval⟩).coeff 2).val ≤ ((a.expCompDepth + 1 : ℕ) : ℚ) / 2
      rw [compZero_exp_coeff_two_general ⟨a.eval⟩]
      have h1 := abs_le.mp ih.1
      have hsq : (a.eval 1).val * (a.eval 1).val ≤ 1 := by nlinarith
      have h2 : (a.eval 2).val ≤ (a.expCompDepth : ℚ) / 2 := ih.2
      push_cast
      linarith

/-- **Semantic Strictness Across the Entire Exponential Tower (`strictness_unitSeedTower`):**
    For every height $h \in \mathbb{N}$, `uTower (h + 2)` (ordinal $\omega_{h+2}$) belongs to
    `SemBellTowerLe (h + 1)` and **provably escapes `SemBellTowerLe h`**! -/
theorem strictness_unitSeedTower (h : ℕ) :
    SemBellTowerLe (h + 1) (uTower (h + 2)).eval ∧
    ¬ SemBellTowerLe h (uTower (h + 2)).eval := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [uTower_eval_one h, abs_one]
  · rw [uTower_eval_two h]
  · rintro ⟨_, h2⟩
    rw [uTower_eval_two h] at h2
    push_cast at h2
    linarith

/-- **Intrinsic Lower-Bound Theorem Across the Exponential Tower (`intrinsic_lower_bound_tower`):**
    For **every** $h \in \mathbb{N}$ and **every** expression `e` in `IsUnitSeedTower`
    (regardless of constant shifts or trigonometric subexpressions), if `SemJetEq e.eval (uTower (h + 2)).eval`,
    then `e` must have exponential-composition depth at least $h + 1$ (`h + 1 ≤ e.expCompDepth`)! -/
theorem intrinsic_lower_bound_tower (e : UExpr) (he : e.IsUnitSeedTower) (h : ℕ)
    (hEq : SemJetEq e.eval (uTower (h + 2)).eval) :
    h + 1 ≤ e.expCompDepth := by
  have hsound := (soundness_unitSeedTower he).congr hEq
  have h2 := hsound.2
  rw [uTower_eval_two h] at h2
  have hcast : ((h + 1 : ℕ) : ℚ) ≤ (e.expCompDepth : ℚ) := by linarith
  exact_mod_cast hcast

/-! ## 8. Presentation Ordinal vs. Intrinsic Ordinal (`HasPresentationLe`)
    and the Falsification Suite ($e^0$, $f \circ 0$, $e^x - e^x$) -/

/-- A Taylor jet `c` has **intrinsic presentation ordinal $\le \alpha$** if there exists
    a defined expression `e : UExpr` with `SemJetEq e.eval c` and `e.ord ≤ α`. -/
def HasPresentationLe (α : Eps0) (c : ℕ → Q) : Prop :=
  ∃ e : UExpr, e.Defined ∧ SemJetEq e.eval c ∧ (Eps0.OLtE e.ord α ∨ e.ord = α)

/-- **Falsification Test 1 ($f \circ 0$ and $e^0$):**
    Composing any expression `a` with any expression `b` of ordinal $0$ (such as `.const q`)
    has syntactic ordinal `.zero` (no ordinal inflation on trivial compositions). -/
theorem ord_comp_of_ord_zero (a b : UExpr) (hb : b.ord = .zero) :
    (UExpr.comp a b).ord = .zero := by
  dsimp [UExpr.ord]
  rw [hb]
  simp

/-- **Falsification Test 2 ($1 / c$):**
    Taking the reciprocal of any expression `a` of ordinal $0$ (such as `.const q`)
    has syntactic ordinal `.zero`. -/
theorem ord_inv_of_ord_zero (a : UExpr) (ha : a.ord = .zero) :
    (UExpr.inv a).ord = .zero := by
  dsimp [UExpr.ord]
  rw [if_pos ha]

/-- **Falsification Test 3 ($e^x - e^x$ Cancellation vs. Intrinsic Ordinal):**
    The unsimplified expression `UExpr.sub .exp .exp` ($e^x - e^x$) has presentation
    ordinal $\omega$, yet is semantically equal (`SemJetEq`) to `.const Q.zero` and
    therefore has **intrinsic presentation ordinal $0$** (`HasPresentationLe Eps0.zero`)! -/
theorem sub_exp_exp_presentation_vs_intrinsic :
    (UExpr.sub .exp .exp).ord = Eps0.omega ∧
    SemJetEq (UExpr.sub .exp .exp).eval (UExpr.const Q.zero).eval ∧
    HasPresentationLe Eps0.zero (UExpr.sub .exp .exp).eval := by
  have hsem : SemJetEq (UExpr.sub .exp .exp).eval (UExpr.const Q.zero).eval := by
    intro n
    change (Q.sub (Jet.exp.coeff n) (Jet.exp.coeff n)).val = ((Jet.const Q.zero).coeff n).val
    rw [Q.val_sub, sub_self]
    cases n <;> exact Q.val_zero.symm
  refine ⟨rfl, hsem, ⟨.const Q.zero, trivial, fun n ↦ (hsem n).symm, Or.inr rfl⟩⟩

/-! ## 9. Direct ODE-System Complexity (`LinearGPACSys`) and the
    Cumulative Descriptive Differential Hierarchy $\mathcal{D}_\alpha$ (`InDescDiff` & `uWaveTower`)

This section bridges our expression-level ordinal hierarchy with:
1. **Direct ODE-system recurrence bounds (`LinearGPACSys` on `GPACSys`):**
   We prove directly from the polynomial ODE recurrence
   $$(n+1)\,Y_v(n+1) = F_v(Y)(n) \quad (\text{`sbd_solN_succ_val`})$$
   that every linear ODE system (`LinearGPACSys sys`, of **any** dimension $N$,
   including arbitrary coupled harmonic oscillators and constant-coefficient linear
   wave systems) satisfies the computed factorial decay bound
   $$|(Y_v)_n| \cdot n! \le 2^M \cdot (2^R)^n \quad (\text{where } (M, R) = \mathrm{sysParams}(\mathrm{sys})),$$
   and hence belongs to `SemEntireExpType`. Consequently, **no linear ODE system of
   any dimension $N$ can ever solve to the 1-variable quadratic ODE $y' = y^2$ (`uGeom`)**!
2. **The Cumulative Descriptive Differential Hierarchy $\mathcal{D}_\alpha$ (`InDescDiff α`):**
   Analogous to the Borel hierarchy $\Sigma^0_\alpha$ in descriptive set theory and
   Fourier synthesis ("waves over waves"), we define $\mathcal{D}_\alpha$ (`InDescDiff α`)
   as the class of Taylor series generated by polynomial ODE systems compiled from
   expressions of Cantor ordinal $\preceq \alpha$, prove its cumulative monotonicity
   $\mathcal{D}_\beta \subseteq \mathcal{D}_\alpha$ ($\beta \prec \alpha$), and construct
   the transfinite wave-modulation cascade `uWaveTower : ℕ → UExpr` ($\sin x \mapsto
   \exp(\sin x) \mapsto \exp(\exp(\sin x)) \mapsto \cdots$), proving that each wave-over-wave
   stage strictly expands the hierarchy across $\omega \prec \omega^\omega \prec
   \omega^{\omega^\omega} \prec \cdots \prec \varepsilon_0$. -/

/-- A `JExprN` expression is a **constant scalar expression** (`NoVars`) if it contains
    no state variables `.var i` and no integration operators `.integ`. -/
def JExprN.NoVars : JExprN → Prop
  | .var _ | .integ _ => False
  | .const _ => True
  | .add a b | .sub a b | .mul a b => a.NoVars ∧ b.NoVars

/-- A `JExprN` expression is **linear in the state variables** (`IsLinear`) if every
    product `.mul a b` multiplies at least one state-free scalar factor (`NoVars`) by
    a linear factor. -/
def JExprN.IsLinear : JExprN → Prop
  | .var _ | .const _ => True
  | .add a b | .sub a b => a.IsLinear ∧ b.IsLinear
  | .mul a b => (a.NoVars ∧ b.IsLinear) ∨ (b.NoVars ∧ a.IsLinear)
  | .integ a => a.IsLinear

/-- A polynomial ODE system `sys` is a **Linear GPAC System** (`LinearGPACSys sys`)
    if it is a well-formed `GPACSys` whose right-hand-side expressions are all linear
    in the state variables. -/
def LinearGPACSys (sys : List (Tm [] JetTy × JExprN)) : Prop :=
  GPACSys sys ∧ ∀ p ∈ sys, p.2.IsLinear

/-- Cauchy product formula for `sbdEvalExpr (.mul a b) W n`. -/
theorem sbdEvalExpr_mul_val (a b : JExprN) (W : ℕ → ℕ → Q) (n : ℕ) :
    (sbdEvalExpr (.mul a b) W n).val =
      ∑ j ∈ Finset.range (n + 1), (sbdEvalExpr a W j).val * (sbdEvalExpr b W (n - j)).val := by
  have hev : sbdEvalExpr (.mul a b) W n =
      ((tmJetMul (Γ := [])).eval Env.nil) (sbdEvalExpr a W) (sbdEvalExpr b W) n := rfl
  rw [hev, tmJetMul_eval]
  simp only [Jet.mul, TrigPoly.cauchyConvAux_val]

/-- Every state-free scalar expression `F` with constant leaves (`ConstsConst`)
    vanishes identically at all Taylor degrees $k + 1 \ge 1$. -/
theorem sbdEvalExpr_noVars_succ_zero (F : JExprN) (hNV : F.NoVars) (hCC : F.ConstsConst)
    (W : ℕ → ℕ → Q) (k : ℕ) :
    (sbdEvalExpr F W (k + 1)).val = 0 := by
  induction F generalizing k with
  | var _ | integ _ => nomatch hNV
  | const c =>
    have hev : sbdEvalExpr (.const c) W (k + 1) = c.eval Env.nil (k + 1) := by
      dsimp [sbdEvalExpr, JExprN.toTm]
      rw [closedWk_eval]
    rw [hev]
    exact hCC k
  | add a b iha ihb =>
    have hev : (sbdEvalExpr (.add a b) W (k + 1)).val =
        (sbdEvalExpr a W (k + 1)).val + (sbdEvalExpr b W (k + 1)).val :=
      Q.val_add _ _
    rw [hev, iha hNV.1 hCC.1 k, ihb hNV.2 hCC.2 k, add_zero]
  | sub a b iha ihb =>
    have hev : (sbdEvalExpr (.sub a b) W (k + 1)).val =
        (sbdEvalExpr a W (k + 1)).val - (sbdEvalExpr b W (k + 1)).val :=
      Q.val_sub _ _
    rw [hev, iha hNV.1 hCC.1 k, ihb hNV.2 hCC.2 k, sub_zero]
  | mul a b iha ihb =>
    rw [sbdEvalExpr_mul_val a b W (k + 1)]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    cases j with
    | zero =>
      rw [Nat.sub_zero, ihb hNV.2 hCC.2 k, mul_zero]
    | succ m =>
      rw [iha hNV.1 hCC.1 m, zero_mul]

/-- At degree $0$, any state-free scalar expression `F` is bounded by `sbdExprBound F K`. -/
theorem sbdEvalExpr_noVars_zero_bound (F : JExprN) (hNV : F.NoVars)
    (W : ℕ → ℕ → Q) {K : ℚ} (hK : 0 ≤ K) :
    |(sbdEvalExpr F W 0).val| ≤ sbdExprBound F K := by
  induction F with
  | var _ | integ _ => nomatch hNV
  | const c =>
    have hev : sbdEvalExpr (.const c) W 0 = c.eval Env.nil 0 := by
      dsimp [sbdEvalExpr, JExprN.toTm]
      rw [closedWk_eval]
    rw [hev]
    exact le_refl _
  | add a b iha ihb =>
    have hev : (sbdEvalExpr (.add a b) W 0).val =
        (sbdEvalExpr a W 0).val + (sbdEvalExpr b W 0).val := Q.val_add _ _
    rw [hev]
    dsimp [sbdExprBound]
    have ha := iha hNV.1
    have hb := ihb hNV.2
    have htri := abs_add_le (sbdEvalExpr a W 0).val (sbdEvalExpr b W 0).val
    linarith
  | sub a b iha ihb =>
    have hev : (sbdEvalExpr (.sub a b) W 0).val =
        (sbdEvalExpr a W 0).val - (sbdEvalExpr b W 0).val := Q.val_sub _ _
    rw [hev]
    dsimp [sbdExprBound]
    have ha := iha hNV.1
    have hb := ihb hNV.2
    have htri := abs_sub (sbdEvalExpr a W 0).val (sbdEvalExpr b W 0).val
    linarith
  | mul a b iha ihb =>
    rw [sbdEvalExpr_mul_val a b W 0, Finset.sum_range_one, Nat.sub_zero, abs_mul]
    dsimp [sbdExprBound]
    have ha := iha hNV.1
    have hb := ihb hNV.2
    have ha0 := sbdExprBound_nonneg a hK
    have hb0 := sbdExprBound_nonneg b hK
    have hprod := mul_le_mul ha hb (abs_nonneg _) ha0
    have hprod0 : 0 ≤ sbdExprBound a K * sbdExprBound b K := by positivity
    linarith

/-- In a Cauchy product `.mul a b` where `a` is state-free (`a.NoVars`), all higher
    convolution terms vanish and the degree-$m$ coefficient is simply $a(0) \cdot b(m)$. -/
theorem sbd_mul_noVars_left_val (a b : JExprN) (haNV : a.NoVars) (haCC : a.ConstsConst)
    (W : ℕ → ℕ → Q) (m : ℕ) :
    (sbdEvalExpr (.mul a b) W m).val =
      (sbdEvalExpr a W 0).val * (sbdEvalExpr b W m).val := by
  rw [sbdEvalExpr_mul_val a b W m, Finset.sum_range_succ' _ m, Nat.sub_zero]
  have htail : ∑ k ∈ Finset.range m,
      (sbdEvalExpr a W (k + 1)).val * (sbdEvalExpr b W (m - (k + 1))).val = 0 := by
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [sbdEvalExpr_noVars_succ_zero a haNV haCC W k, zero_mul]
  linarith

/-- Symmetric right-scalar Cauchy product collapse when `b.NoVars`. -/
theorem sbd_mul_noVars_right_val (a b : JExprN) (hbNV : b.NoVars) (hbCC : b.ConstsConst)
    (W : ℕ → ℕ → Q) (m : ℕ) :
    (sbdEvalExpr (.mul a b) W m).val =
      (sbdEvalExpr a W m).val * (sbdEvalExpr b W 0).val := by
  rw [sbdEvalExpr_mul_val a b W m, Finset.sum_range_succ _ m, Nat.sub_self]
  have hhead : ∑ j ∈ Finset.range m,
      (sbdEvalExpr a W j).val * (sbdEvalExpr b W (m - j)).val = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hsub : m - j = (m - 1 - j) + 1 := by omega
    rw [hsub, sbdEvalExpr_noVars_succ_zero b hbNV hbCC W (m - 1 - j), mul_zero]
  linarith

/-- **Factorial bound preservation for linear `JExprN` expressions:**
    If every state variable $u < \mathrm{sysLen}$ satisfies $|W_u(m)| \cdot m! \le K \cdot B^m$
    for $m \le n$, then any linear expression $F$ satisfies
    $|F(W)(m)| \cdot m! \le \Phi_F(K) \cdot B^m$ for $m \le n$. -/
theorem sbdEvalExpr_linear_fact_bound (F : JExprN) (sysLen : ℕ)
    (hWF : F.WF sysLen) (hCC : F.ConstsConst) (hLin : F.IsLinear)
    (W : ℕ → ℕ → Q) {K B : ℚ} (hK : 0 ≤ K) (hB : 1 ≤ B) (n : ℕ)
    (hW : ∀ u < sysLen, ∀ m ≤ n, |(W u m).val| * (fact m : ℚ) ≤ K * B ^ m) :
    ∀ m ≤ n, |(sbdEvalExpr F W m).val| * (fact m : ℚ) ≤ sbdExprBound F K * B ^ m := by
  have hB0 : (0 : ℚ) ≤ B := by linarith
  induction F with
  | var i =>
    intro m hm
    have hev : sbdEvalExpr (.var i) W m = W i m := by
      change (Tm.var (Γ := [WTy]) .here).eval (Env.cons (σ := WTy) W Env.nil)
        ((natTm i).eval (Env.cons (σ := WTy) W Env.nil)) m = W i m
      rw [natTm_eval]
      rfl
    rw [hev]
    exact hW i hWF m hm
  | const c =>
    intro m _
    have hev : sbdEvalExpr (.const c) W m = c.eval Env.nil m := by
      dsimp [sbdEvalExpr, JExprN.toTm]
      rw [closedWk_eval]
    rw [hev]
    dsimp [sbdExprBound]
    cases m with
    | zero =>
      dsimp [fact]
      rw [mul_one, pow_zero, mul_one]
    | succ k =>
      rw [hCC k, abs_zero, zero_mul]
      positivity
  | add a b iha ihb =>
    intro m hm
    have hev : (sbdEvalExpr (.add a b) W m).val =
        (sbdEvalExpr a W m).val + (sbdEvalExpr b W m).val := Q.val_add _ _
    rw [hev]
    dsimp [sbdExprBound]
    have ha := iha hWF.1 hCC.1 hLin.1 m hm
    have hb := ihb hWF.2 hCC.2 hLin.2 m hm
    have htri := mul_le_mul_of_nonneg_right
      (abs_add_le (sbdEvalExpr a W m).val (sbdEvalExpr b W m).val)
      (show (0 : ℚ) ≤ (fact m : ℚ) by positivity)
    have hring : (sbdExprBound a K + sbdExprBound b K) * B ^ m =
        sbdExprBound a K * B ^ m + sbdExprBound b K * B ^ m := by ring
    linarith
  | sub a b iha ihb =>
    intro m hm
    have hev : (sbdEvalExpr (.sub a b) W m).val =
        (sbdEvalExpr a W m).val - (sbdEvalExpr b W m).val := Q.val_sub _ _
    rw [hev]
    dsimp [sbdExprBound]
    have ha := iha hWF.1 hCC.1 hLin.1 m hm
    have hb := ihb hWF.2 hCC.2 hLin.2 m hm
    have htri := mul_le_mul_of_nonneg_right
      (abs_sub (sbdEvalExpr a W m).val (sbdEvalExpr b W m).val)
      (show (0 : ℚ) ≤ (fact m : ℚ) by positivity)
    have hring : (sbdExprBound a K + sbdExprBound b K) * B ^ m =
        sbdExprBound a K * B ^ m + sbdExprBound b K * B ^ m := by ring
    linarith
  | mul a b iha ihb =>
    intro m hm
    dsimp [sbdExprBound]
    have ha0 := sbdExprBound_nonneg a hK
    have hb0 := sbdExprBound_nonneg b hK
    have hBm0 : (0 : ℚ) ≤ B ^ m := by positivity
    have hprod0 : 0 ≤ sbdExprBound a K * (sbdExprBound b K * B ^ m) := by positivity
    rcases hLin with ⟨haNV, hbLin⟩ | ⟨hbNV, haLin⟩
    · rw [sbd_mul_noVars_left_val a b haNV hCC.1 W m, abs_mul, mul_assoc]
      have ha := sbdEvalExpr_noVars_zero_bound a haNV W hK
      have hb := ihb hWF.2 hCC.2 hbLin m hm
      have hprod := mul_le_mul ha hb (by positivity) ha0
      have hring : 8 * sbdExprBound a K * sbdExprBound b K * B ^ m =
          8 * (sbdExprBound a K * (sbdExprBound b K * B ^ m)) := by ring
      linarith
    · rw [sbd_mul_noVars_right_val a b hbNV hCC.2 W m, abs_mul,
          show |(sbdEvalExpr a W m).val| * |(sbdEvalExpr b W 0).val| * (fact m : ℚ) =
            |(sbdEvalExpr b W 0).val| * (|(sbdEvalExpr a W m).val| * (fact m : ℚ)) by ring]
      have hb := sbdEvalExpr_noVars_zero_bound b hbNV W hK
      have ha := iha hWF.1 hCC.1 haLin m hm
      have hprod := mul_le_mul hb ha (by positivity) hb0
      have hring : 8 * sbdExprBound a K * sbdExprBound b K * B ^ m =
          8 * (sbdExprBound a K * (sbdExprBound b K * B ^ m)) := by ring
      have hcomm : sbdExprBound b K * (sbdExprBound a K * B ^ m) =
          sbdExprBound a K * (sbdExprBound b K * B ^ m) := by ring
      linarith
  | integ a iha =>
    intro m hm
    dsimp [sbdExprBound]
    cases m with
    | zero =>
      have hev : (sbdEvalExpr (.integ a) W 0).val = 0 := Q.val_ofNat 0
      rw [hev, abs_zero, zero_mul]
      have hΦ := sbdExprBound_nonneg a hK
      positivity
    | succ k =>
      have hne : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
      have hev : (sbdEvalExpr (.integ a) W (k + 1)).val =
          (sbdEvalExpr a W k).val / ((k + 1 : ℕ) : ℚ) := by
        change (Q.div (sbdEvalExpr a W k) (Q.ofNat (k + 1))).val = _
        rw [Q.val_div _ _ hne, Q.val_ofNat]
      have hk1_pos : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) := by positivity
      have hfact : (fact (k + 1) : ℚ) = ((k + 1 : ℕ) : ℚ) * (fact k : ℚ) := by
        dsimp [fact]
        push_cast
        ring
      have hcancel : (|(sbdEvalExpr a W k).val| / ((k + 1 : ℕ) : ℚ)) * (fact (k + 1) : ℚ) =
          |(sbdEvalExpr a W k).val| * (fact k : ℚ) := by
        rw [hfact]
        have hk1_ne : ((k + 1 : ℕ) : ℚ) ≠ 0 := ne_of_gt hk1_pos
        field_simp [hk1_ne]
      rw [hev, abs_div, abs_of_pos hk1_pos, hcancel]
      have ha_k := iha hWF hCC hLin k (Nat.le_of_succ_le hm)
      have hΦ := sbdExprBound_nonneg a hK
      have hBk : B ^ k ≤ B ^ (k + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (by positivity) hB
      have hscale := mul_le_mul_of_nonneg_left hBk hΦ
      linarith

/-- **Direct ODE-Recurrence Factorial Majorant for Linear GPAC Systems:**
    From the ODE recurrence $(k+1) Y_v(k+1) = F_v(Y)(k)$ (`sbd_solN_succ_val`), the
    $1/(k+1)$ integration factor accumulates into $1/n!$ across every step $n$. -/
theorem sbd_solN_linear_fact_bound (sys : List (Tm [] JetTy × JExprN)) (h : LinearGPACSys sys)
    {K B : ℚ} (hK : 0 ≤ K) (hB : 4 ≤ B)
    (hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ K)
    (hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 K ≤ K * B) :
    ∀ n : ℕ, ∀ v < sys.length, |(solN sys v n).val| * (fact n : ℚ) ≤ K * B ^ n := by
  have hB1 : (1 : ℚ) ≤ B := by linarith
  have hB0 : (0 : ℚ) ≤ B := by linarith
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hp_mem := List.getElem_mem hv
    have hpv := h.1 sys[v] hp_mem
    have hlin := h.2 sys[v] hp_mem
    cases m with
    | zero =>
      rw [uMul_solN_zero_val sys (gpac_wf h.1) v hv]
      dsimp [fact]
      rw [mul_one, pow_zero, mul_one]
      exact hInit sys[v] hp_mem
    | succ k =>
      rw [sbd_solN_succ_val sys h.1 v hv k]
      have hk1_pos : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) := by positivity
      have hfact : (fact (k + 1) : ℚ) = ((k + 1 : ℕ) : ℚ) * (fact k : ℚ) := by
        dsimp [fact]
        push_cast
        ring
      have hcancel :
          (|(sbdEvalExpr sys[v].2 (solN sys) k).val| / ((k + 1 : ℕ) : ℚ)) * (fact (k + 1) : ℚ) =
            |(sbdEvalExpr sys[v].2 (solN sys) k).val| * (fact k : ℚ) := by
        rw [hfact]
        have hk1_ne : ((k + 1 : ℕ) : ℚ) ≠ 0 := ne_of_gt hk1_pos
        field_simp [hk1_ne]
      rw [abs_div, abs_of_pos hk1_pos, hcancel]
      have hexpr := sbdEvalExpr_linear_fact_bound sys[v].2 sys.length hpv.1 hpv.2.2 hlin
        (solN sys) hK hB1 k (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu) k (le_refl k)
      have hΦ : 0 ≤ sbdExprBound sys[v].2 K := sbdExprBound_nonneg sys[v].2 hK
      have hstep_v := hStep sys[v] hp_mem
      have hΦ_le : sbdExprBound sys[v].2 K ≤ K * B := by linarith
      have hscale : sbdExprBound sys[v].2 K * B ^ k ≤ (K * B) * B ^ k :=
        mul_le_mul_of_nonneg_right hΦ_le (by positivity)
      have hpow : (K * B) * B ^ k = K * B ^ (k + 1) := by
        rw [pow_succ]
        ring
      linarith

/-- **Computed Factorial Majorant Theorem for Linear ODE Systems (`solN_linear_factorial_bound_computed`):**
    For **every** linear ODE system `sys` (`LinearGPACSys sys`) of arbitrary dimension $N$,
    its syntax-computed parameters `(M, R) = sysParams sys` certify the global factorial
    decay bound
    $$|(Y_v)_n| \cdot n! \le 2^M \cdot (2^R)^n$$
    for every state component $v < N$ and every Taylor degree $n \in \mathbb{N}$! -/
theorem solN_linear_factorial_bound_computed (sys : List (Tm [] JetTy × JExprN))
    (h : LinearGPACSys sys) :
    ∀ v < sys.length, ∀ n : ℕ,
      |(solN sys v n).val| * (fact n : ℚ) ≤
        (2 : ℚ) ^ (sysParams sys).1 * ((2 : ℚ) ^ (sysParams sys).2) ^ n := by
  intro v hv n
  let M := (sysMaxInitN sys).log2 + 1
  let P := sysMaxPhiN (2 ^ M) sys
  let R := (4 * P + 4).log2 + 1
  have hMdef : (sysParams sys).1 = M := rfl
  have hRdef : (sysParams sys).2 = R := rfl
  rw [hMdef, hRdef]
  have hKcast : (((2 ^ M : ℕ) : ℕ) : ℚ) = (2 : ℚ) ^ M := by push_cast; rfl
  have hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ (2 : ℚ) ^ M := by
    intro p hp
    have h1 := Q.abs_val_le_natAbsBound (p.1.eval Env.nil 0)
    have h2 : ((p.1.eval Env.nil 0).natAbsBound : ℚ) ≤ (sysMaxInitN sys : ℚ) := by
      exact_mod_cast sysMaxInitN_mem hp
    have h3 : ((sysMaxInitN sys : ℕ) : ℚ) ≤ (2 : ℚ) ^ M := by
      exact_mod_cast (Nat.lt_log2_self (n := sysMaxInitN sys)).le
    linarith
  have hB : (4 : ℚ) ≤ (2 : ℚ) ^ R := by
    have h' : ((4 * P + 4 : ℕ) : ℚ) ≤ (2 : ℚ) ^ R := by
      exact_mod_cast (Nat.lt_log2_self (n := 4 * P + 4)).le
    push_cast at h'
    have : (0 : ℚ) ≤ (P : ℚ) := Nat.cast_nonneg P
    linarith
  have hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 ((2 : ℚ) ^ M) ≤ (2 : ℚ) ^ M * (2 : ℚ) ^ R := by
    intro p hp
    have h1 := sbdExprBound_le_natBound p.2 (2 ^ M)
    rw [hKcast] at h1
    have h2 : (p.2.natBound (2 ^ M) : ℚ) ≤ (P : ℚ) := by
      exact_mod_cast sysMaxPhiN_mem _ hp
    have h3 : ((4 * P + 4 : ℕ) : ℚ) ≤ (2 : ℚ) ^ R := by
      exact_mod_cast (Nat.lt_log2_self (n := 4 * P + 4)).le
    push_cast at h3
    have hK1 : (1 : ℚ) ≤ (2 : ℚ) ^ M := one_le_pow₀ (by norm_num)
    have hR0 : (0 : ℚ) ≤ (2 : ℚ) ^ R := by positivity
    nlinarith
  exact sbd_solN_linear_fact_bound sys h (by positivity) hB hInit hStep n v hv

/-- **Soundness of Linear ODE Systems (`linearGPACSys_semEntireExpType`):**
    Every component `solN sys v` of a linear ODE system `LinearGPACSys sys`
    (of arbitrary dimension $N$) belongs to the entire exponential-type class
    `SemEntireExpType`. -/
theorem linearGPACSys_semEntireExpType (sys : List (Tm [] JetTy × JExprN))
    (h : LinearGPACSys sys) (v : ℕ) (hv : v < sys.length) :
    SemEntireExpType (solN sys v) :=
  ⟨(sysParams sys).1, (sysParams sys).2, solN_linear_factorial_bound_computed sys h v hv⟩

/-- **Direct ODE-System Separation Theorem (`no_linearGPACSys_semJetEq_uGeom`):**
    **No** linear ODE system `LinearGPACSys sys` of **any** dimension $N \in \mathbb{N}$
    (no matter how many coupled harmonic oscillators, Fourier modes, or linear states
    it superposes) can ever have a solution component `solN sys v` equal to `uGeom`
    ($\frac{1}{1-x}$, the solution to the 1-variable quadratic ODE $y' = y^2$)! -/
theorem no_linearGPACSys_semJetEq_uGeom (sys : List (Tm [] JetTy × JExprN))
    (h : LinearGPACSys sys) (v : ℕ) (hv : v < sys.length) :
    ¬ SemJetEq (solN sys v) uGeom.eval := by
  intro hEq
  exact strictness_at_omegaSq.2
    ((linearGPACSys_semEntireExpType sys h v hv).congr hEq)

/-! ### 9B. The Cumulative Descriptive Differential Hierarchy $\mathcal{D}_\alpha$ (`InDescDiff α`)
    and the Transfinite Wave-Modulation Cascade ("Waves Over Waves", `uWaveTower`) -/

/-- Transitivity of the structural Cantor normal form order `Eps0.OLtE`. -/
theorem Eps0.OLtE.trans {a b c : Eps0} (hab : Eps0.OLtE a b) (hbc : Eps0.OLtE b c) :
    Eps0.OLtE a c := by
  unfold Eps0.OLtE Eps0.oltE at hab hbc ⊢
  simp only [Bool.and_eq_true] at hab hbc ⊢
  exact ⟨⟨hab.1.1, hbc.1.2⟩, Eps0.olt_trans hab.2 hbc.2⟩

/-- **The Cumulative Descriptive Differential Hierarchy ($\mathcal{D}_\alpha$, `InDescDiff α`):**
    A Taylor series `c : ℕ → Q` belongs to level $\alpha \prec \varepsilon_0$ of the
    descriptive differential hierarchy if there exists a well-defined expression `e : UExpr`
    with syntactic ordinal $e.\mathrm{ord} \preceq \alpha$ whose compiled polynomial ODE
    system `e.compile` solves to `c` (`SemJetEq (solN e.compile.sys e.compile.v) c`). -/
def InDescDiff (α : Eps0) (c : ℕ → Q) : Prop :=
  ∃ e : UExpr, e.Defined ∧ (Eps0.OLtE e.ord α ∨ e.ord = α) ∧
    SemJetEq (solN e.compile.sys e.compile.v) c

/-- **Equivalence of the ODE-System Hierarchy and Intrinsic Presentation Hierarchy:**
    Because `UExpr.compile_correct` guarantees that the compiled polynomial ODE system
    `e.compile` solves to `e.eval`, `InDescDiff α c` is equivalent to `HasPresentationLe α c`. -/
theorem InDescDiff_iff_hasPresentationLe (α : Eps0) (c : ℕ → Q) :
    InDescDiff α c ↔ HasPresentationLe α c := by
  constructor
  · rintro ⟨e, he, hord, hsol⟩
    refine ⟨e, he, fun n ↦ ?_, hord⟩
    rw [(e.compile_correct he).2 n]
    exact hsol n
  · rintro ⟨e, he, hev, hord⟩
    refine ⟨e, he, hord, fun n ↦ ?_⟩
    rw [← (e.compile_correct he).2 n]
    exact hev n

/-- **Every level $\mathcal{D}_\alpha$ ($\alpha \prec \varepsilon_0$) of the Descriptive
    Differential Hierarchy is contained in the GPAC polynomial-ODE universe `InGPAC`.** -/
theorem InDescDiff_inGPAC {α : Eps0} {c : ℕ → Q} (hc : InDescDiff α c) : InGPAC c := by
  rcases hc with ⟨e, he, _, hsol⟩
  exact ⟨e.compile.sys, (e.compile_correct he).1, e.compile.v, e.compile.hv,
    fun n ↦ (hsol n).symm⟩

/-- **Cumulative Monotonicity of the Descriptive Differential Hierarchy (`InDescDiff_mono`):**
    Whenever $\beta \prec \alpha$ in Cantor Normal Form (`Eps0.OLtE β α`),
    $$\mathcal{D}_\beta \subseteq \mathcal{D}_\alpha \quad (\text{`InDescDiff β c → InDescDiff α c`}).$$ -/
theorem InDescDiff_mono {β α : Eps0} (hβα : Eps0.OLtE β α) {c : ℕ → Q}
    (hc : InDescDiff β c) : InDescDiff α c := by
  rcases hc with ⟨e, he, hord, hsol⟩
  refine ⟨e, he, ?_, hsol⟩
  rcases hord with hlt | heq
  · exact Or.inl (hlt.trans hβα)
  · rw [heq]
    exact Or.inl hβα

/-- **Transfinite Wave-Modulation Cascade ("Waves Over Waves", `uWaveTower : ℕ → UExpr`):**
    Starting from the fundamental harmonic oscillator `.sin` ($\sin x$, solving $y'' = -y$
    at ordinal $\omega$), each stage $h + 1$ uses the stage-$h$ waveform as the rate/phase
    driver of a new differential equation $Y_{h+1}' = Y_h' \cdot Y_{h+1}$
    (`UExpr.comp .exp (uWaveTower h)`). -/
def uWaveTower : ℕ → UExpr
  | 0 => .sin
  | h + 1 => .comp .exp (uWaveTower h)

/-- Degree-$0$ coefficient of `uWaveTower (h + 1)` is $1$. -/
theorem uWaveTower_succ_eval_zero (h : ℕ) : ((uWaveTower (h + 1)).eval 0).val = 1 :=
  compZero_exp_coeff_zero ⟨(uWaveTower h).eval⟩

/-- Every stage `uWaveTower h` of the wave-modulation cascade is well-defined (`Defined`). -/
theorem uWaveTower_defined : ∀ h : ℕ, (uWaveTower h).Defined
  | 0 => trivial
  | h + 1 => ⟨trivial, uWaveTower_defined h⟩

/-- Every stage `uWaveTower h` belongs to the unit-seed tower fragment `IsUnitSeedTower`. -/
theorem uWaveTower_isUnitSeedTower : ∀ h : ℕ, (uWaveTower h).IsUnitSeedTower
  | 0 => .sin
  | h + 1 => .compExp (uWaveTower_isUnitSeedTower h)

/-- The exponential-composition depth of `uWaveTower h` is $h + 1$. -/
theorem uWaveTower_expCompDepth : ∀ h : ℕ, (uWaveTower h).expCompDepth = h + 1
  | 0 => rfl
  | h + 1 => congrArg (· + 1) (uWaveTower_expCompDepth h)

/-- **Syntactic Ordinal of the Wave Cascade (`uWaveTower_ord`):**
    Stage $h$ of `uWaveTower` has exact Cantor ordinal $\omega_{h+2}$
    ($\omega, \omega^\omega, \omega^{\omega^\omega}, \dots \prec \varepsilon_0$). -/
theorem uWaveTower_ord : ∀ h : ℕ, (uWaveTower h).ord = Eps0.omegaTower (h + 2)
  | 0 => rfl
  | h + 1 => by
    have ih := uWaveTower_ord h
    have hne : (uWaveTower h).ord ≠ .zero := by
      rw [ih]
      intro hc
      cases hc
    dsimp [uWaveTower, UExpr.ord]
    rw [if_pos ⟨rfl, hne⟩, ih]
    rfl

/-- **Compiled ODE System Dimension of the Wave Cascade (`uWaveTower_compile_length`):**
    Because `.sin` compiles to a $2$-dimensional harmonic oscillator system
    ($y_0' = y_1, y_1' = -y_0$) and each wave modulation adds a coupled state equation,
    `uWaveTower h` compiles to a polynomial ODE system of exact dimension $h + 2$! -/
theorem uWaveTower_compile_length : ∀ h : ℕ, (uWaveTower h).compile.sys.length = h + 2
  | 0 => rfl
  | h + 1 => by
    have hstep : (uWaveTower (h + 1)).compile.sys.length =
        (uWaveTower h).compile.sys.length + (flatAll UExpr.exp.compile.sys).length :=
      comp_compSys_length (flatAll UExpr.exp.compile.sys) (uWaveTower h).compile.sys _ _
    have hexp : (flatAll UExpr.exp.compile.sys).length = 1 := rfl
    rw [hstep, hexp, uWaveTower_compile_length h]

/-- Degree-$1$ Taylor coefficient of `uWaveTower h` is $1$ for every $h \in \mathbb{N}$. -/
theorem uWaveTower_eval_one : ∀ h : ℕ, ((uWaveTower h).eval 1).val = 1
  | 0 => jet_sin_coeff_one_val
  | h + 1 => (compZero_exp_coeff_one ⟨(uWaveTower h).eval⟩).trans (uWaveTower_eval_one h)

/-- **Exact Quadratic Modulation Formula for "Waves Over Waves" (`uWaveTower_eval_two`):**
    Starting from $\sin x$ ($[x^2]\sin x = 0$), each wave-over-wave modulation stage $h$
    adds exactly $1/2$ to the quadratic Taylor coefficient:
    $$\big((\mathrm{uWaveTower}\; h).\mathrm{eval}\; 2\big).\mathrm{val} = \frac{h}{2}!$$ -/
theorem uWaveTower_eval_two : ∀ h : ℕ, ((uWaveTower h).eval 2).val = (h : ℚ) / 2
  | 0 => by
    change (Jet.sin.coeff 2).val = (0 : ℚ) / 2
    rw [jet_sin_coeff_two_val]
    norm_num
  | h + 1 => by
    have hstep := compZero_exp_coeff_two ⟨(uWaveTower h).eval⟩ (uWaveTower_eval_one h)
    change ((Jet.compZero Jet.exp ⟨(uWaveTower h).eval⟩).coeff 2).val = _
    rw [hstep, uWaveTower_eval_two h]
    push_cast
    ring

/-- **Every wave-modulation stage `uWaveTower (h + 1)` belongs to $\mathcal{D}_{\omega_{h+3}}$,
    lies in `SemBellTowerLe (h + 1)`, and strictly escapes `SemBellTowerLe h`!** -/
theorem uWaveTower_hierarchy_strictness (h : ℕ) :
    InDescDiff (Eps0.omegaTower (h + 3)) (uWaveTower (h + 1)).eval ∧
    SemBellTowerLe (h + 1) (uWaveTower (h + 1)).eval ∧
    ¬ SemBellTowerLe h (uWaveTower (h + 1)).eval := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨uWaveTower (h + 1), uWaveTower_defined (h + 1),
      Or.inr (uWaveTower_ord (h + 1)), fun n ↦ ?_⟩
    exact ((uWaveTower (h + 1)).compile_correct (uWaveTower_defined (h + 1))).2 n |>.symm
  · rw [uWaveTower_eval_one (h + 1), abs_one]
  · rw [uWaveTower_eval_two (h + 1)]
  · rintro ⟨_, h2⟩
    rw [uWaveTower_eval_two (h + 1)] at h2
    push_cast at h2
    linarith

/-- **Pairwise Semantic Distinctness of All Wave-Modulation Stages (`uWaveTower_semJetEq_injective`):**
    Every stage $h \in \mathbb{N}$ of the "waves over waves" cascade `uWaveTower h`
    generates a distinct analytic waveform! -/
theorem uWaveTower_semJetEq_injective (h₁ h₂ : ℕ)
    (hEq : SemJetEq (uWaveTower h₁).eval (uWaveTower h₂).eval) : h₁ = h₂ := by
  have h2 := hEq 2
  rw [uWaveTower_eval_two h₁, uWaveTower_eval_two h₂] at h2
  have hcast : (h₁ : ℚ) = (h₂ : ℚ) := by linarith
  exact Nat.cast_injective hcast

/-! ## 10. Concrete Guarded Checks Across the Ordinal Spectrum -/

-- 1. Finite ordinals (< ω): polynomials, degree read off by `ord.natPart`
#guard (UExpr.const (Q.ofNat 5)).ord == Eps0.zero
#guard UExpr.x.ord == Eps0.one
#guard (UExpr.mul .x (.mul .x .x)).ord == Eps0.ofNat 3
#guard (UExpr.integ (.mul .x .x)).ord == Eps0.ofNat 3
#guard (UExpr.deriv (.mul .x (.mul .x .x))).ord == Eps0.ofNat 2
#guard Eps0.olt (UExpr.mul .x (.mul .x .x)).ord Eps0.omega == true

-- 2. ω-level: linear ODE generators and exponential polynomials
#guard UExpr.exp.ord == Eps0.omega
#guard UExpr.sin.ord == Eps0.omega
#guard (UExpr.mul .exp .sin).ord == Eps0.node Eps0.one 1 .zero   -- ω · 2
#guard (UExpr.add (.mul .exp .sin) (.mul .x .x)).ord == Eps0.node Eps0.one 1 .zero

-- 3. ω-tower (ω^ω, ω^(ω^ω), ... < ε₀): coupled ODE compositions
#guard (uTower 0).ord == Eps0.omegaTower 0
#guard (uTower 1).ord == Eps0.omegaTower 1
#guard (uTower 2).ord == Eps0.omegaTower 2
#guard (uTower 3).ord == Eps0.omegaTower 3
#guard (uTower 4).ord == Eps0.omegaTower 4
#guard ((uTower 2).compile.sys.length, (uTower 3).compile.sys.length, (uTower 4).compile.sys.length)
  == (1, 2, 3)
#guard ((uTower 2).radiusParams, (uTower 3).radiusParams, (uTower 4).radiusParams, (uTower 5).radiusParams)
  == ((0, 0), (0, 1), (0, 2), (0, 3))

-- 4. Full ε₀ surjectivity: realizing Goodstein and Kirby–Paris Hydra ordinals as ODEs!
#guard (odeOfOrd (ordE 2 100)).ord == ordE 2 100
#guard (odeOfOrd (ordEOfHydra (hydraOf 7))).ord == ordEOfHydra (hydraOf 7)

-- 5. Semantic separation at ω² and Bell-tower Taylor coefficients:
#guard uGeom.ord == Eps0.omegaSq
#guard [(((uTower 2).eval 2).val : ℚ), (((uTower 3).eval 2).val : ℚ), (((uTower 4).eval 2).val : ℚ)]
  == [1 / 2, 1, 3 / 2]
#guard (UExpr.comp .exp (.const Q.zero)).ord == Eps0.zero
#guard ((uWaveTower 0).ord, (uWaveTower 1).ord, (uWaveTower 2).ord)
  == (Eps0.omegaTower 2, Eps0.omegaTower 3, Eps0.omegaTower 4)
#guard ((uWaveTower 0).compile.sys.length, (uWaveTower 1).compile.sys.length, (uWaveTower 2).compile.sys.length)
  == (2, 3, 4)
#guard [(((uWaveTower 0).eval 2).val : ℚ), (((uWaveTower 1).eval 2).val : ℚ), (((uWaveTower 2).eval 2).val : ℚ)]
  == [0, 1 / 2, 1]

#print axioms UExpr.ord_nf
#print axioms UExpr.solN_eq_zero_of_isPoly
#print axioms UExpr.analyticJet_of_isExpPoly
#print axioms uTower_ord
#print axioms uTower_ord_strictMono
#print axioms uTower_radiusParams_R_strictMono
#print axioms uTower_compile_length_strictMono
#print axioms odeOfOrd_inGPAC
#print axioms odeOfOrd_ord
#print axioms soundness_polyDegLe
#print axioms strictness_polyDegLe
#print axioms intrinsic_lower_bound_poly
#print axioms soundness_below_omega
#print axioms strictness_at_omega
#print axioms no_isPoly_semJetEq_exp
#print axioms soundness_below_omegaSq
#print axioms strictness_at_omegaSq
#print axioms no_isExpPoly_semJetEq_uGeom
#print axioms uTower_eval_two
#print axioms uTower_eval_two_strictMono
#print axioms uTower_semJetEq_injective
#print axioms soundness_unitSeedTower
#print axioms strictness_unitSeedTower
#print axioms intrinsic_lower_bound_tower
#print axioms sub_exp_exp_presentation_vs_intrinsic
#print axioms solN_linear_factorial_bound_computed
#print axioms no_linearGPACSys_semJetEq_uGeom
#print axioms InDescDiff_mono
#print axioms uWaveTower_hierarchy_strictness
#print axioms uWaveTower_semJetEq_injective

end HAomega
