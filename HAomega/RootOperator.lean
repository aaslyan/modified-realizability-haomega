/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseEval
import HAomega.Bisection

/-!
# The root operator: bisection on the closed universe

Two extracted programs composed: the certified evaluator `UExpr.approx`
(`UniverseEval.lean`) colours the grid `x_k = a + k(b−a)/2ʲ` by the sign of `f`
at precision `2⁻ᵐ`, and the bisection operator `bisect` (`Bisection.lean`)
finds where the colour changes.

    UExpr.root e a b j m  =  x_i,   i = bisect j (k ↦ [approx f (x_k) m < 0]) 0

**What is proved** (`UExpr.root_spec`): if the colours at the two ends differ,
the returned point lies in `[a, b]` and every partial sum of `f`'s Taylor series
past `N = m + M + 3` is small there,

    |S_N(root)| < 2⁻ᵐ + 2^{M+R+2} · (b − a) / 2ʲ,

the second term being the slope bound of the partial sums on the disk
(`evalPoly_lip_disk`) times the grid step.  This is the **approximate
intermediate value theorem**, realized by binary search.  It is the constructive
form: an exact zero is not computable from the function in general (the
location of a zero is not continuous in `f`), and the extracted operator, like
every extract, is continuous.

Scope: `e` an expression of the universe, `[a, b]` inside its certified disk
`|x| ≤ 2^{-(R+2)}` (`(M, R) = e.radiusParams`).  The operator is choice-free
(`[propext, Quot.sound]`); its certificate is metatheory.
-/

namespace HAomega

/-- The grid point `a + k(b−a)/2ʲ`. -/
def rootGrid (a b : Q) (j k : Nat) : Q :=
  Q.add a (Q.div (Q.mul (Q.ofNat k) (Q.sub b a)) (Q.ofNat (2 ^ j)))

/-- The sign colouring of `f` on the grid, at precision `2⁻ᵐ`: `1` where the
certified approximation is negative, `0` where it is not. -/
def UExpr.rootColor (e : UExpr) (a b : Q) (j m : Nat) (k : Nat) : Nat :=
  Q.ltN (e.approx (rootGrid a b j k) m) (Q.ofNat 0)

/-- The grid index bisection returns. -/
def UExpr.rootIndex (e : UExpr) (a b : Q) (j m : Nat) : Nat :=
  bisect j (e.rootColor a b j m) 0

/-- **The root operator.** -/
def UExpr.root (e : UExpr) (a b : Q) (j m : Nat) : Q :=
  rootGrid a b j (e.rootIndex a b j m)

/-! ## The grid -/

theorem rootGrid_val (a b : Q) (j k : Nat) :
    (rootGrid a b j k).val = a.val + (k : Rat) * (b.val - a.val) / (2 : Rat) ^ j := by
  unfold rootGrid
  rw [Q.val_add, Q.val_div_all, Q.val_mul, Q.val_ofNat, Q.val_sub, Q.val_ofNat]
  push_cast; ring

theorem rootGrid_mem (a b : Q) (j k : Nat) (hab : a.val ≤ b.val) (hk : k ≤ 2 ^ j) :
    a.val ≤ (rootGrid a b j k).val ∧ (rootGrid a b j k).val ≤ b.val := by
  rw [rootGrid_val]
  have h2 : (0 : Rat) < (2 : Rat) ^ j := by positivity
  have hk' : (k : Rat) ≤ (2 : Rat) ^ j := by exact_mod_cast hk
  have hba : 0 ≤ b.val - a.val := by linarith
  constructor
  · have : 0 ≤ (k : Rat) * (b.val - a.val) / (2 : Rat) ^ j := by positivity
    linarith
  · have : (k : Rat) * (b.val - a.val) / (2 : Rat) ^ j ≤ b.val - a.val := by
      rw [div_le_iff₀ h2]; nlinarith
    linarith

theorem rootGrid_step (a b : Q) (j k : Nat) :
    (rootGrid a b j (k + 1)).val - (rootGrid a b j k).val = (b.val - a.val) / (2 : Rat) ^ j := by
  rw [rootGrid_val, rootGrid_val]; push_cast; ring

/-! ## The certificate -/

/-- **The root operator is correct**: the approximate intermediate value
theorem, by bisection. -/
theorem UExpr.root_spec (e : UExpr) (h : e.Defined) (a b : Q) (j m : Nat)
    (ha : |a.val| ≤ 1 / (2 : Rat) ^ (e.radiusParams.2 + 2))
    (hb : |b.val| ≤ 1 / (2 : Rat) ^ (e.radiusParams.2 + 2))
    (hab : a.val ≤ b.val)
    (hends : e.rootColor a b j m 0 ≠ e.rootColor a b j m (2 ^ j)) (d : Nat) :
    a.val ≤ (e.root a b j m).val ∧ (e.root a b j m).val ≤ b.val ∧
    |(Jet.evalPoly ⟨e.eval⟩ (m + (e.radiusParams.1 + 3) + d) (e.root a b j m)).val|
      < 1 / (2 : Rat) ^ m
        + (2 : Rat) ^ (e.radiusParams.1 + e.radiusParams.2 + 2) * ((b.val - a.val) / (2 : Rat) ^ j) := by
  -- the bisection step
  set c := e.rootColor a b j m with hcdef
  have hb0 : c 0 ≠ c (0 + 2 ^ j) := by rwa [Nat.zero_add]
  obtain ⟨hi, hci⟩ := bisect_spec j c 0 hb0
  set i := bisect j c 0 with hidef
  rw [Nat.zero_add] at hci
  have hroot : e.root a b j m = rootGrid a b j i := rfl
  rw [hroot]
  set x := rootGrid a b j i with hxdef
  set y := rootGrid a b j (i + 1) with hydef
  have hxm := rootGrid_mem a b j i hab (le_of_lt hi)
  have hym := rootGrid_mem a b j (i + 1) hab hi
  refine ⟨hxm.1, hxm.2, ?_⟩
  -- the radius data
  set M := e.radiusParams.1 with hMdef
  set R := e.radiusParams.2 with hRdef
  obtain ⟨F, hF⟩ := e.radiusJet h
  have hp := e.radiusParams_eq h
  have hFM : (e.radiusJet h).1.M = M := congrArg Prod.fst hp
  have hFR : (e.radiusJet h).1.R = R := congrArg Prod.snd hp
  -- points in the disk
  have hdisk : ∀ z : Q, a.val ≤ z.val → z.val ≤ b.val → |z.val| ≤ 1 / (2 : Rat) ^ (R + 2) := by
    intro z h1 h2
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith [ha.1, hb.2]
  have hdisk1 : ∀ z : Q, |z.val| ≤ 1 / (2 : Rat) ^ (R + 2) → |z.val| ≤ 1 / (2 : Rat) ^ (R + 1) := by
    intro z hz
    exact le_trans hz (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hxd := hdisk x hxm.1 hxm.2
  have hyd := hdisk y hym.1 hym.2
  -- the evaluator's guarantee at both points
  set N := m + (M + 3) + d with hNdef
  have happ : ∀ z : Q, |z.val| ≤ 1 / (2 : Rat) ^ (R + 1) →
      |(Jet.evalPoly ⟨e.eval⟩ N z).val - (e.approx z m).val| < 1 / (2 : Rat) ^ m := by
    intro z hz
    have := e.approx_spec h z hz m d
    rwa [extractedJetCauchyModulusComputed_eq] at this
  have hax := happ x (hdisk1 x hxd)
  have hay := happ y (hdisk1 y hyd)
  -- the slope bound between the two neighbours
  have hlip : |(Jet.evalPoly ⟨e.eval⟩ N x).val - (Jet.evalPoly ⟨e.eval⟩ N y).val|
      ≤ (2 : Rat) ^ (M + R + 2) * ((b.val - a.val) / (2 : Rat) ^ j) := by
    let G := (e.radiusJet h).1
    have hG : G.toJet = ⟨e.eval⟩ := (e.radiusJet h).2
    let r : Q := D.toQ (D.pow2neg (R + 2))
    have hr : |r.val| = 1 / (2 : Rat) ^ (R + 2) := by
      dsimp [r]; rw [toQ_pow2neg_val, abs_of_pos (by positivity)]
    have hrle : |r.val| ≤ 1 / (2 : Rat) ^ (G.R + 2) := by rw [hr, hFR]
    have := G.evalPoly_lip_disk r x y hrle (by rw [hr]; exact hxd) (by rw [hr]; exact hyd) N
    rw [hG] at this
    have hstep : |x.val - y.val| = (b.val - a.val) / (2 : Rat) ^ j := by
      have := rootGrid_step a b j i
      rw [abs_sub_comm, abs_of_nonneg (by
        rw [← hydef, ← hxdef] at this; rw [this]; have : 0 ≤ b.val - a.val := by linarith
        positivity)]
      exact this
    have hDM : G.deriv.M + 1 = M + R + 2 := by
      show G.M + G.R + 1 + 1 = M + R + 2
      rw [hFM, hFR]
    rw [hDM, hstep] at this
    exact this
  -- the two colours differ: one neighbour is negative, the other not
  have hL : 0 ≤ (2 : Rat) ^ (M + R + 2) * ((b.val - a.val) / (2 : Rat) ^ j) := by
    have : 0 ≤ b.val - a.val := by linarith
    positivity
  rw [abs_lt] at hax hay ⊢
  rw [abs_le] at hlip
  rcases Q.ltN_eq_zero_or_one (e.approx x m) (Q.ofNat 0) with hx0 | hx1 <;>
  rcases Q.ltN_eq_zero_or_one (e.approx y m) (Q.ofNat 0) with hy0 | hy1
  · exact absurd (hx0.trans hy0.symm) hci
  · rw [Q.ltN_eq_zero_iff, Q.val_ofNat_zero] at hx0
    rw [Q.ltN_eq_one_iff, Q.val_ofNat_zero] at hy1
    constructor <;> linarith
  · rw [Q.ltN_eq_one_iff, Q.val_ofNat_zero] at hx1
    rw [Q.ltN_eq_zero_iff, Q.val_ofNat_zero] at hy0
    constructor <;> linarith
  · exact absurd (hx1.trans hy1.symm) hci

/-! ## Examples: a logarithm and an inverse sine, as roots

On `[0, 1/4]`, inside the disk `|x| ≤ 1/4` of both expressions (`R = 0`).
Constants are written with small numerators: the coefficient bound of a
constant `q` is `2^|num q|`, so `1 + 1/40` costs far less slope than `41/40`. -/

/-- `eˣ − 1 − 1/40`: its root is `ln (41/40)`. -/
def rootExLog : UExpr := .sub (.sub .exp (.const (Q.ofNat 1))) (.const ⟨1, 39⟩)

/-- `sin x − 1/5`: its root is `arcsin (1/5)` — an inverse function, by bisection. -/
def rootExAsin : UExpr := .sub .sin (.const ⟨1, 4⟩)

#guard rootExLog.radiusParams = (3, 0)
#guard rootExAsin.radiusParams = (2, 0)
-- the end colours differ (the hypothesis of `root_spec`)
#guard rootExLog.rootColor ⟨0, 0⟩ ⟨1, 3⟩ 40 40 0 = 1 ∧ rootExLog.rootColor ⟨0, 0⟩ ⟨1, 3⟩ 40 40 (2 ^ 40) = 0
#guard rootExAsin.rootColor ⟨0, 0⟩ ⟨1, 3⟩ 40 40 0 = 1 ∧ rootExAsin.rootColor ⟨0, 0⟩ ⟨1, 3⟩ 40 40 (2 ^ 40) = 0
-- `j = m = 40`: certified `|S_N(root)| < 2⁻⁴⁰ + 2^{M+2}·2⁻⁴²`, and against floating point:
#guard (let r := rootExLog.root ⟨0, 0⟩ ⟨1, 3⟩ 40 40
        (Float.ofInt r.num / Float.ofNat r.den - Float.log 1.025).abs < 1e-10)
#guard (let r := rootExAsin.root ⟨0, 0⟩ ⟨1, 3⟩ 40 40
        (Float.ofInt r.num / Float.ofNat r.den - Float.asin 0.2).abs < 1e-10)

#print axioms UExpr.root
#print axioms UExpr.root_spec

end HAomega
