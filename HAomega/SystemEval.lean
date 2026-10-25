/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemBound
import HAomega.UniverseEval
import HAomega.UniverseMembers

/-!
# Certified evaluation of every polynomial system

`solN_geom_bound` (`SystemBound.lean`) states that coefficient bounds `(M, R)`
exist for every `GPACSys`. Here they are **computed** from the system's syntax,
by a choice-free recursion (`sysParams`), and the computed pair is proved to be
a bound (`solN_geom_bound_computed`). With it every component of every system is
a `RadiusJet`, so the proof-computed Cauchy modulus of `UniverseEval.lean`
applies, and every member of the universe gets a certified evaluator:

    GPACSys.approx sys v x k      within 2⁻ᵏ of every later partial sum,
                                  for |x| ≤ 2^{-(R+1)}             (approx_spec)

`UExpr.approx` did this expression by expression; this does it for every
system, including those not produced by `UExpr.compile`.
-/

namespace HAomega

/-- A natural upper bound for `|q|`: `|num|`, since the denominator is `≥ 1`. -/
def Q.natAbsBound (q : Q) : Nat := q.num.natAbs

theorem Q.abs_val_le_natAbsBound (q : Q) : |q.val| ≤ (q.natAbsBound : Rat) := by
  unfold Q.val Q.natAbsBound
  have hd : (1 : Rat) ≤ (q.den : Rat) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr q.den_ne_zero
  have hden : |(q.den : Rat)| = (q.den : Rat) := abs_of_pos (by linarith)
  rw [abs_div, hden, natAbs_cast_rat]
  exact div_le_self (abs_nonneg _) hd

/-- `sbdExprBound`, in natural numbers and with each constant bounded by
`Q.natAbsBound`: computable without `Q.val`. -/
def JExprN.natBound : JExprN → Nat → Nat
  | .var _, K => K
  | .const c, _ => (c.eval Env.nil 0).natAbsBound
  | .add a b, K => a.natBound K + b.natBound K
  | .sub a b, K => a.natBound K + b.natBound K
  | .mul a b, K => 8 * a.natBound K * b.natBound K
  | .integ a, K => a.natBound K

theorem sbdExprBound_le_natBound (F : JExprN) (K : Nat) :
    sbdExprBound F (K : Rat) ≤ (F.natBound K : Rat) := by
  induction F with
  | var _ => exact le_refl _
  | const c => exact Q.abs_val_le_natAbsBound _
  | add a b iha ihb =>
    show sbdExprBound a K + sbdExprBound b K ≤ ((a.natBound K + b.natBound K : Nat) : Rat)
    push_cast; linarith
  | sub a b iha ihb =>
    show sbdExprBound a K + sbdExprBound b K ≤ ((a.natBound K + b.natBound K : Nat) : Rat)
    push_cast; linarith
  | mul a b iha ihb =>
    show 8 * sbdExprBound a K * sbdExprBound b K ≤ ((8 * a.natBound K * b.natBound K : Nat) : Rat)
    push_cast
    have ha0 := sbdExprBound_nonneg a (Nat.cast_nonneg K)
    have hb0 := sbdExprBound_nonneg b (Nat.cast_nonneg K)
    have := mul_le_mul iha ihb hb0 (by positivity)
    nlinarith
  | integ a iha => exact iha

/-- The largest initial-value bound of a system (at least `1`). -/
def sysMaxInitN : List (Tm [] JetTy × JExprN) → Nat
  | [] => 1
  | p :: rest => max (p.1.eval Env.nil 0).natAbsBound (sysMaxInitN rest)

/-- The largest equation multiplier of a system at `K`. -/
def sysMaxPhiN (K : Nat) : List (Tm [] JetTy × JExprN) → Nat
  | [] => 0
  | p :: rest => max (p.2.natBound K) (sysMaxPhiN K rest)

/-- **The computed coefficient bound** `(M, R)` of a system: `2^M` above every
initial value, `2^R` above `4·max_v Φ_{F_v}(2^M) + 4`. -/
def sysParams (sys : List (Tm [] JetTy × JExprN)) : Nat × Nat :=
  let M := (sysMaxInitN sys).log2 + 1
  (M, (4 * sysMaxPhiN (2 ^ M) sys + 4).log2 + 1)

theorem sysMaxInitN_mem {sys : List (Tm [] JetTy × JExprN)} {p : Tm [] JetTy × JExprN}
    (hp : p ∈ sys) : (p.1.eval Env.nil 0).natAbsBound ≤ sysMaxInitN sys := by
  induction sys with
  | nil => nomatch hp
  | cons hd rest ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact le_max_left _ _
    · exact le_trans (ih hp) (le_max_right _ _)

theorem sysMaxPhiN_mem (K : Nat) {sys : List (Tm [] JetTy × JExprN)} {p : Tm [] JetTy × JExprN}
    (hp : p ∈ sys) : p.2.natBound K ≤ sysMaxPhiN K sys := by
  induction sys with
  | nil => nomatch hp
  | cons hd rest ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact le_max_left _ _
    · exact le_trans (ih hp) (le_max_right _ _)

/-- **The computed pair is a coefficient bound.** -/
theorem solN_geom_bound_computed (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys) :
    ∀ v, v < sys.length → ∀ n : Nat,
      |(solN sys v n).val| ≤ (2 : Rat) ^ (sysParams sys).1 * ((2 : Rat) ^ (sysParams sys).2) ^ n := by
  intro v hv n
  let M := (sysMaxInitN sys).log2 + 1
  let P := sysMaxPhiN (2 ^ M) sys
  let R := (4 * P + 4).log2 + 1
  have hMdef : (sysParams sys).1 = M := rfl
  have hRdef : (sysParams sys).2 = R := rfl
  rw [hMdef, hRdef]
  have hK1 : (1 : Rat) ≤ (2 : Rat) ^ M := one_le_pow₀ (by norm_num)
  have hKcast : (((2 ^ M : Nat) : Nat) : Rat) = (2 : Rat) ^ M := by push_cast; rfl
  have hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ (2 : Rat) ^ M := by
    intro p hp
    have h1 := Q.abs_val_le_natAbsBound (p.1.eval Env.nil 0)
    have h2 : ((p.1.eval Env.nil 0).natAbsBound : Rat) ≤ (sysMaxInitN sys : Rat) := by
      exact_mod_cast sysMaxInitN_mem hp
    have h3 : ((sysMaxInitN sys : Nat) : Rat) ≤ (2 : Rat) ^ M := by
      have := (Nat.lt_log2_self (n := sysMaxInitN sys)).le
      exact_mod_cast this
    linarith
  have hB : (4 : Rat) ≤ (2 : Rat) ^ R := by
    have := (Nat.lt_log2_self (n := 4 * P + 4)).le
    have h' : ((4 * P + 4 : Nat) : Rat) ≤ (2 : Rat) ^ R := by exact_mod_cast this
    push_cast at h'
    have : (0 : Rat) ≤ (P : Rat) := Nat.cast_nonneg P
    linarith
  have hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 ((2 : Rat) ^ M) ≤ (2 : Rat) ^ M * (2 : Rat) ^ R := by
    intro p hp
    have h1 := sbdExprBound_le_natBound p.2 (2 ^ M)
    rw [hKcast] at h1
    have h2 : (p.2.natBound (2 ^ M) : Rat) ≤ (P : Rat) := by exact_mod_cast sysMaxPhiN_mem _ hp
    have h3 : ((4 * P + 4 : Nat) : Rat) ≤ (2 : Rat) ^ R := by
      exact_mod_cast (Nat.lt_log2_self (n := 4 * P + 4)).le
    push_cast at h3
    have hR0 : (0 : Rat) ≤ (2 : Rat) ^ R := by positivity
    nlinarith
  have hw := sbd_solN_weighted_bound sys h (by positivity) hB hInit hStep n v hv
  exact le_trans hw (div_le_self (by positivity) (sbdSq_ge_one n))

/-- Component `v` of a system as a `RadiusJet`, with the computed parameters. -/
def GPACSys.radiusJet (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys) (v : Nat)
    (hv : v < sys.length) : RadiusJet where
  toJet := ⟨solN sys v⟩
  M := (sysParams sys).1
  R := (sysParams sys).2
  bound n := (RadiusJet.bound_iff_val _ _ _ _).mpr (solN_geom_bound_computed sys h v hv n)

/-- **The certified approximation** of component `v` of a system at `x`, to `2⁻ᵏ`. -/
def GPACSys.approx (sys : List (Tm [] JetTy × JExprN)) (v : Nat) (x : Q) (k : Nat) : Q :=
  Jet.evalPoly ⟨solN sys v⟩ (extractedJetCauchyModulusComputed (solN sys v) (sysParams sys).1 x k) x

/-- **Every member of the universe has a certified evaluator**: on the disk
`|x| ≤ 2^{-(R+1)}`, every later partial sum is within `2⁻ᵏ` of `approx`. -/
theorem GPACSys.approx_spec (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys) (v : Nat)
    (hv : v < sys.length) (x : Q) (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams sys).2 + 1))
    (k d : Nat) :
    |(Jet.evalPoly ⟨solN sys v⟩
        (extractedJetCauchyModulusComputed (solN sys v) (sysParams sys).1 x k + d) x).val
      - (GPACSys.approx sys v x k).val| < 1 / (2 : Rat) ^ k := by
  have := (GPACSys.radiusJet sys h v hv).cauchyComputed_correct x hx k 0 d
  dsimp only [GPACSys.radiusJet] at this
  rw [Nat.add_zero] at this
  rw [abs_sub_comm]
  exact this

/-! ## Examples

`memSinCosSys` (`sin' = cos`, `cos' = −sin`) gets `(M, R) = (1, 4)` from the
syntax alone, so its disk is `|x| ≤ 1/32`; at `k = 10` the modulus is `N = 14`.

`tan` as the solution of the Riccati system `y = 0 + ∫(1 + y·y)` — a system
written directly, not produced by `UExpr.compile` — gets `(M, R) = (1, 8)`.

**Cost.** `solN` evaluates the Picard iterates lazily, so for a nonlinear
system the cost of coefficient `n` grows exponentially (for `tan`: degree 7 in
≈ 4 s, 11 in ≈ 13 s, measured by `lake env lean`); the guard stays at `k = 3`
(`N = 7`). The memoized table of `SystemFast.lean` (`solFast`, proved equal to
`solN`) removes the cost. -/

#guard sysParams memSinCosSys = (1, 4)
#guard extractedJetCauchyModulusComputed (solN memSinCosSys 0) (sysParams memSinCosSys).1 ⟨1, 31⟩ 10 = 14
#guard (let r := GPACSys.approx memSinCosSys 0 ⟨1, 31⟩ 10
        (Float.ofInt r.num / Float.ofNat r.den - Float.sin (1 / 32)).abs < 1e-6)

/-- `tan`: `y = 0 + ∫(1 + y·y)`. -/
def sysTan : List (Tm [] JetTy × JExprN) :=
  [(tmZeroJet, .add (.const tmConstOneJet) (.mul (.var 0) (.var 0)))]

theorem sysTan_gpac : GPACSys sysTan := by
  intro p hp
  simp only [sysTan, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨⟨trivial, ⟨show 0 < 1 by omega, show 0 < 1 by omega⟩⟩, gpac_isConstJet_zero,
    mem_isConstJet_one, trivial, trivial⟩

#guard sysParams sysTan = (1, 8)
#guard (let r := GPACSys.approx sysTan 0 ⟨1, 1023⟩ 3
        (Float.ofInt r.num / Float.ofNat r.den - Float.tan (1 / 1024)).abs < 1 / 8)

#print axioms sysParams
#print axioms GPACSys.approx
#print axioms solN_geom_bound_computed
#print axioms GPACSys.approx_spec

end HAomega
