/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseExpr
import HAomega.JetCauchyComputed

/-!
# Certified evaluation of the universe (closed-universe pillar 5)

`UExpr.compile` turns every expression of the universe into a system whose
coefficients the proof-computed solver produces. This module turns coefficients
into numbers: every expression has an explicit disk on which the partial sums of
its Taylor series converge with the modulus computed by `jetCauchyModulusComputedD`.

* `UExpr.radiusJet` — every expression has a geometric coefficient bound
  `|c_n| ≤ 2^M (2^R)^n`, with `M`, `R` computed from the expression;
* `RadiusJet.cauchyComputed_correct` — the extracted modulus of
  `jetCauchyModulusComputedD` is correct on the disk `|x| ≤ 2^{-(R+1)}`, read off
  the derivation through `soundness`;
* `UExpr.certifiedEval` — the two together: for every expression `e`, point `x` in
  its disk and precision `k`, the partial sums past the extracted `N(k)` stay
  within `2^{-k}` of each other.
-/

namespace HAomega

/-- A radius bound transfers along value agreement of the coefficients. -/
def RadiusJet.ofVal (F : RadiusJet) (c : Nat → Q)
    (h : ∀ n, (c n).val = (F.toJet.coeff n).val) : RadiusJet where
  toJet := ⟨c⟩
  M := F.M
  R := F.R
  bound n := by
    rw [RadiusJet.bound_iff_val]
    show |(c n).val| ≤ _
    rw [h n]
    exact F.bound_val n

/-- Elementary dominance `(m : Rat) ≤ 2^m`. -/
theorem uEval_nat_le_two_pow : ∀ m : Nat, (m : Rat) ≤ (2 : Rat) ^ m
  | 0 => by norm_num
  | k + 1 => by
    have ih := uEval_nat_le_two_pow k
    have h1 : (1 : Rat) ≤ (2 : Rat) ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    push_cast
    linarith

/-- Every rational `q : Q` satisfies `|q.val| ≤ 2^{|q.num|}`. -/
theorem uEval_const_val_bound (q : Q) : |q.val| ≤ (2 : Rat) ^ q.num.natAbs := by
  have hd_pos : (0 : Rat) < (q.den : Rat) := q.den_cast_pos
  have hd_ge : (1 : Rat) ≤ (q.den : Rat) := by exact_mod_cast Nat.succ_pos q.denPred
  have hval : |q.val| = ((q.num.natAbs : Nat) : Rat) / (q.den : Rat) := by
    unfold Q.val
    rw [abs_div, abs_of_pos hd_pos, ← natAbs_cast_rat]
  rw [hval]
  have h1 : ((q.num.natAbs : Nat) : Rat) / (q.den : Rat) ≤ ((q.num.natAbs : Nat) : Rat) :=
    div_le_self (by positivity) hd_ge
  exact le_trans h1 (uEval_nat_le_two_pow q.num.natAbs)

/-- Constant jet `Jet.const q` equipped with its `RadiusJet` bound. -/
def uEval_constRadiusJet (q : Q) : RadiusJet where
  toJet := Jet.const q
  M := q.num.natAbs
  R := 0
  bound n := by
    rw [RadiusJet.bound_iff_val]
    cases n with
    | zero =>
      dsimp [Jet.const]
      simpa using uEval_const_val_bound q
    | succ k =>
      dsimp [Jet.const]
      rw [Q.val_zero, abs_zero]
      positivity

/-- Scalar multiplication of a `RadiusJet` by a rational `q : Q`. -/
def uEval_scaleRadiusJet (q : Q) (F : RadiusJet) : RadiusJet where
  toJet := F.toJet.scale q
  M := q.num.natAbs + F.M
  R := F.R
  bound n := by
    rw [RadiusJet.bound_iff_val]
    dsimp [Jet.scale]
    rw [Q.val_mul, abs_mul]
    have hq := uEval_const_val_bound q
    have hF := F.bound_val n
    have hmul := mul_le_mul hq hF (abs_nonneg _) (by positivity)
    have hrhs : (2 : Rat) ^ q.num.natAbs * ((2 : Rat) ^ F.M * ((2 : Rat) ^ F.R) ^ n) =
        (2 : Rat) ^ (q.num.natAbs + F.M) * ((2 : Rat) ^ F.R) ^ n := by
      rw [pow_add (2 : Rat) q.num.natAbs F.M, mul_assoc]
    linarith

/-- Value of the partial Cauchy convolution in the scaled reciprocal recurrence. -/
theorem uEval_recip_convAux_val (FA : RadiusJet) (f : Nat → Q) (hFA : FA.toJet = ⟨f⟩)
    (h0 : (f 0).val ≠ 0) (k : Nat) : ∀ r : Nat,
    (Jet.cauchyConvAux (uEval_scaleRadiusJet (Q.div (Q.ofNat 1) (f 0)) FA).toJet.shift
      ⟨fun n ↦ Q.mul (f 0) (Jet.recip f n)⟩ k r).val =
      ∑ j ∈ Finset.range r, (f (j + 1)).val * (Jet.recip f (k - j)).val
  | 0 => by
    dsimp [Jet.cauchyConvAux]
    simp [Q.val_zero]
  | j + 1 => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_add, uEval_recip_convAux_val FA f hFA h0 k j, Finset.sum_range_succ]
    congr 1
    dsimp [uEval_scaleRadiusJet, Jet.shift, Jet.scale]
    rw [hFA]
    simp only [Q.val_mul, Q.val_div _ _ (inv_num_ne_zero h0), Q.val_ofNat, Nat.cast_one]
    field_simp

/-- Geometric bound on the normalized reciprocal coefficients `f(0) · (recip f)_n`. -/
theorem uEval_recip_scaled_bound (FA : RadiusJet) (f : Nat → Q) (hFA : FA.toJet = ⟨f⟩)
    (h0 : (f 0).val ≠ 0) (n : Nat) :
    let G := uEval_scaleRadiusJet (Q.div (Q.ofNat 1) (f 0)) FA
    |(Q.mul (f 0) (Jet.recip f n)).val| ≤ ((2 : Rat) ^ (G.M + G.R + 1)) ^ n := by
  intro G
  induction n using Nat.strongRecOn with
  | ind m ih =>
    cases m with
    | zero =>
      change |(Q.mul (f 0) (Q.div (Q.ofNat 1) (f 0))).val| ≤ 1
      rw [Q.val_mul, Q.val_div _ _ (inv_num_ne_zero h0), Q.val_ofNat, Nat.cast_one]
      have h1 : (f 0).val * ((1 : Rat) / (f 0).val) = 1 := by field_simp
      rw [h1]
      norm_num
    | succ k =>
      have hI : ∀ i ≤ k, |(Q.mul (f 0) (Jet.recip f i)).val| ≤ ((2 : Rat) ^ (G.M + G.R + 1)) ^ i :=
        fun i hi ↦ ih i (Nat.lt_succ_of_le hi)
      have hconv := G.invOneSub_convAux_bound (fun i ↦ Q.mul (f 0) (Jet.recip f i)) k hI (k + 1) (le_refl _)
      have hval : (Q.mul (f 0) (Jet.recip f (k + 1))).val =
          - (Jet.cauchyConvAux G.toJet.shift ⟨fun i ↦ Q.mul (f 0) (Jet.recip f i)⟩ k (k + 1)).val := by
        rw [Q.val_mul, ux_recip_succ_val f h0 k, uEval_recip_convAux_val FA f hFA h0 k (k + 1)]
        field_simp
      rw [hval, abs_neg]
      have hpos : (0 : Rat) ≤ ((2 : Rat) ^ (G.M + G.R + 1)) ^ (k + 1) * (1 / (2 : Rat) ^ (k + 1)) := by
        positivity
      linarith

/-- `RadiusJet` bound for `Jet.recip f` when `f` has a `RadiusJet` bound and `(f 0).val ≠ 0`. -/
def uEval_recipRadiusJet (FA : RadiusJet) (f : Nat → Q) (hFA : FA.toJet = ⟨f⟩)
    (h0 : (f 0).val ≠ 0) : RadiusJet :=
  let q0 := Q.div (Q.ofNat 1) (f 0)
  let G := uEval_scaleRadiusJet q0 FA
  { toJet := ⟨Jet.recip f⟩
    M := q0.num.natAbs
    R := G.M + G.R + 1
    bound := fun n ↦ by
      rw [RadiusJet.bound_iff_val]
      have h_id : (Jet.recip f n).val = q0.val * (Q.mul (f 0) (Jet.recip f n)).val := by
        dsimp [q0]
        rw [Q.val_div _ _ (inv_num_ne_zero h0), Q.val_mul, Q.val_ofNat, Nat.cast_one]
        field_simp
      have h_abs : |(Jet.recip f n).val| = |q0.val| * |(Q.mul (f 0) (Jet.recip f n)).val| := by
        rw [h_id, abs_mul]
      rw [h_abs]
      exact mul_le_mul (uEval_const_val_bound q0) (uEval_recip_scaled_bound FA f hFA h0 n)
        (abs_nonneg _) (by positivity) }

/-- **Every expression of the universe has a geometric coefficient bound.** -/
def UExpr.radiusJet : (e : UExpr) → e.Defined → {F : RadiusJet // F.toJet = ⟨e.eval⟩}
  | .const q, _ => ⟨uEval_constRadiusJet q, rfl⟩
  | .x, _ => ⟨RadiusJet.varX, rfl⟩
  | .exp, _ => ⟨RadiusJet.exp, rfl⟩
  | .sin, _ => ⟨RadiusJet.sin, rfl⟩
  | .cos, _ => ⟨RadiusJet.cos, rfl⟩
  | .add a b, h =>
    let ⟨FA, hFA⟩ := a.radiusJet h.1
    let ⟨FB, hFB⟩ := b.radiusJet h.2
    ⟨(FA.add FB).ofVal (UExpr.add a b).eval (fun n ↦ by
      dsimp [UExpr.eval, RadiusJet.add, Jet.add]
      rw [hFA, hFB]), rfl⟩
  | .sub a b, h =>
    let ⟨FA, hFA⟩ := a.radiusJet h.1
    let ⟨FB, hFB⟩ := b.radiusJet h.2
    ⟨(FA.sub FB).ofVal (UExpr.sub a b).eval (fun n ↦ by
      dsimp [UExpr.eval, RadiusJet.sub, Jet.sub]
      rw [hFA, hFB]), rfl⟩
  | .mul a b, h =>
    let ⟨FA, hFA⟩ := a.radiusJet h.1
    let ⟨FB, hFB⟩ := b.radiusJet h.2
    ⟨(FA.mul FB).ofVal (UExpr.mul a b).eval (fun n ↦ by
      dsimp [UExpr.eval, RadiusJet.mul]
      rw [tmJetMul_eval, hFA, hFB]), rfl⟩
  | .inv a, h =>
    let ⟨FA, hFA⟩ := a.radiusJet h.1
    ⟨uEval_recipRadiusJet FA a.eval hFA h.2, rfl⟩
  | .integ a, h =>
    let ⟨FA, hFA⟩ := a.radiusJet h
    ⟨FA.integ.ofVal (UExpr.integ a).eval (fun n ↦ by
      dsimp [UExpr.eval, RadiusJet.integ]
      rw [hFA]
      cases n <;> rfl), rfl⟩
  | .deriv a, h =>
    let ⟨FA, hFA⟩ := a.radiusJet h
    ⟨FA.deriv.ofVal (UExpr.deriv a).eval (fun n ↦ by
      dsimp [UExpr.eval, RadiusJet.deriv]
      rw [hFA]
      rfl), rfl⟩
  | .comp a b, h =>
    let ⟨FA, hFA⟩ := a.radiusJet h.1
    let ⟨FB, hFB⟩ := b.radiusJet h.2
    ⟨(FA.compZero FB).ofVal (UExpr.comp a b).eval (fun n ↦ by
      dsimp [UExpr.eval, RadiusJet.compZero]
      rw [hFA, hFB]), rfl⟩

/-- Evaluation of the Order-0 pair recurrence inside `tmJetEvalPoly`. -/
theorem uEval_tmJetEvalPairAt_rec (c : Nat → Q) (x : Q) : ∀ N : Nat,
    (Nat.rec (motive := fun _ ↦ Q × Q) (Q.ofNat 0, Q.ofNat 1)
      (fun j (st : Q × Q) ↦ (Q.add st.1 (Q.mul (c j) st.2), Q.mul x st.2)) N : Q × Q) =
      ((Jet.mk c).evalPoly N x, qpow x N)
  | 0 => rfl
  | n + 1 => by
    change (Q.add (Nat.rec (motive := fun _ ↦ Q × Q) (Q.ofNat 0, Q.ofNat 1)
        (fun j (st : Q × Q) ↦ (Q.add st.1 (Q.mul (c j) st.2), Q.mul x st.2)) n).1
      (Q.mul (c n) (Nat.rec (motive := fun _ ↦ Q × Q) (Q.ofNat 0, Q.ofNat 1)
        (fun j (st : Q × Q) ↦ (Q.add st.1 (Q.mul (c j) st.2), Q.mul x st.2)) n).2),
      Q.mul x (Nat.rec (motive := fun _ ↦ Q × Q) (Q.ofNat 0, Q.ofNat 1)
        (fun j (st : Q × Q) ↦ (Q.add st.1 (Q.mul (c j) st.2), Q.mul x st.2)) n).2) =
      (Q.add ((Jet.mk c).evalPoly n x) (Q.mul (c n) (qpow x n)), Q.mul x (qpow x n))
    rw [uEval_tmJetEvalPairAt_rec c x n]

/-- Evaluating `tmJetEvalPoly` produces `Jet.evalPoly`. -/
theorem uEval_tmJetEvalPoly_eval {Γ : List Ty} (e : Env Γ) (c : Nat → Q) (N : Nat) (x : Q) :
    ((tmJetEvalPoly (Γ := Γ)).eval e) c N x = (Jet.mk c).evalPoly N x :=
  congrArg Prod.fst (uEval_tmJetEvalPairAt_rec c x N)

/-- Rational value of `qabsT.eval`. -/
theorem uEval_qabsT_val {Γ : List Ty} (e : Env Γ) (d : Q) :
    ((qabsT (Γ := Γ)).eval e d).val = |d.val| := by
  change (Nat.rec (motive := fun _ ↦ Q) d (fun _ _ ↦ Q.sub (Q.ofNat 0) d)
    (Q.ltN d (Q.ofNat 0))).val = |d.val|
  rcases Q.ltN_eq_zero_or_one d (Q.ofNat 0) with h | h
  · rw [h]
    have hge : 0 ≤ d.val := by
      have h0 := (Q.ltN_eq_zero_iff d (Q.ofNat 0)).mp h
      rwa [Q.val_ofNat, Nat.cast_zero] at h0
    exact (abs_of_nonneg hge).symm
  · rw [h]
    have hlt : d.val < 0 := by
      have h1 := (Q.ltN_eq_one_iff d (Q.ofNat 0)).mp h
      rwa [Q.val_ofNat, Nat.cast_zero] at h1
    show (Q.sub (Q.ofNat 0) d).val = |d.val|
    rw [Q.val_sub, Q.val_ofNat, Nat.cast_zero, zero_sub, abs_of_neg hlt]

/-- Value-level characterization of `qclose.eval`. -/
theorem uEval_qclose_eq_one_iff {Γ : List Ty} (e : Env Γ) (k : Nat) (u v : Q) :
    ((qclose (Γ := Γ)).eval e) k u v = 1 ↔ |u.val - v.val| < 1 / (2 : Rat) ^ k := by
  change Q.ltN
    ((qabsT (Γ := .rat :: .rat :: .nat :: Γ)).eval (Env.cons v (Env.cons u (Env.cons k e))) (Q.sub u v))
    ((qpow2 (Γ := .rat :: .rat :: .nat :: Γ)).eval (Env.cons v (Env.cons u (Env.cons k e))) k) = 1 ↔ _
  rw [Q.ltN_eq_one_iff, uEval_qabsT_val, qpow2_eval, Q.val_sub, toQ_pow2neg_val]

/-- Realizability of `jetTermPremise` for `F : RadiusJet` on its half-radius disk. -/
theorem uEval_mr_jetTermPremise (F : RadiusJet) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 1)) :
    MR (jetTermPremise []) (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil)))
      (fun _ ↦ ()) := by
  intro n
  have hxa : Qle (Q.neg (D.toQ (D.pow2neg (F.R + 1)))) x = true := by
    rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val]
    exact (abs_le.mp hx).1
  have hxb : Qle x (D.toQ (D.pow2neg (F.R + 1))) = true := by
    rw [Qle_eq_true_iff, toQ_pow2neg_val]
    exact (abs_le.mp hx).2
  have hsat := F.satisfies_jetTermPremise x hxa hxb n
  let e4 : Env [.nat, .rat, .nat, JetTy] :=
    Env.cons n (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil)))
  change Q.ltN
    ((qabsT (Γ := [.nat, .rat, .nat, JetTy])).eval e4
      (Q.sub (((tmJetEvalPoly (Γ := [.nat, .rat, .nat, JetTy])).eval e4) F.toJet.coeff n x)
             (((tmJetEvalPoly (Γ := [.nat, .rat, .nat, JetTy])).eval e4) F.toJet.coeff (n + 1) x)))
    (Q.mul (((qpow2pos (Γ := [.nat, .rat, .nat, JetTy])).eval e4) (F.M + 3))
      (Q.sub (((qpow2 (Γ := [.nat, .rat, .nat, JetTy])).eval e4) (n + 1))
             (((qpow2 (Γ := [.nat, .rat, .nat, JetTy])).eval e4) (n + 2)))) = 1
  rw [uEval_tmJetEvalPoly_eval, uEval_tmJetEvalPoly_eval, qpow2pos_eval_eq, qpow2_eval, qpow2_eval]
  rw [Q.ltN_eq_one_iff, uEval_qabsT_val]
  rw [Q.ltN_eq_one_iff, Q.val_abs] at hsat
  exact hsat

/-- Realizability of `qGeomArithPremise` for `F : RadiusJet`. -/
theorem uEval_mr_qGeomArithPremise (F : RadiusJet) (x : Q) :
    MR (qGeomArithPremise []) (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil)))
      ⟨fun _ ↦ (), ⟨fun _ _ _ ↦ (), ⟨fun _ _ ↦ (), fun _ _ ↦ ()⟩⟩⟩ := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · intro m
    have hsat := satisfies_qGeomZero F.M m
    let e4 : Env [.nat, .rat, .nat, JetTy] :=
      Env.cons m (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil)))
    change Q.ltN
      ((qabsT (Γ := [.nat, .rat, .nat, JetTy])).eval e4 (Q.ofNat 0))
      (Q.mul (((qpow2pos (Γ := [.nat, .rat, .nat, JetTy])).eval e4) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .rat, .nat, JetTy])).eval e4) m)
               (((qpow2 (Γ := [.nat, .rat, .nat, JetTy])).eval e4) (m + 0 + 1)))) = 1
    rw [qpow2pos_eval_eq, qpow2_eval, qpow2_eval, Q.ltN_eq_one_iff, uEval_qabsT_val]
    rw [Q.ltN_eq_one_iff, Q.val_abs] at hsat
    exact hsat
  · intro u v w
    have hsat := satisfies_qTriangle u v w
    let e6 : Env [.rat, .rat, .rat, .rat, .nat, JetTy] :=
      Env.cons w (Env.cons v (Env.cons u (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil)))))
    change Q.ltN
      (Q.add ((qabsT (Γ := [.rat, .rat, .rat, .rat, .nat, JetTy])).eval e6 (Q.sub u v))
             ((qabsT (Γ := [.rat, .rat, .rat, .rat, .nat, JetTy])).eval e6 (Q.sub v w)))
      ((qabsT (Γ := [.rat, .rat, .rat, .rat, .nat, JetTy])).eval e6 (Q.sub u w)) = 0
    rw [Q.ltN_eq_zero_iff, Q.val_add, uEval_qabsT_val, uEval_qabsT_val, uEval_qabsT_val]
    rw [Q.ltN_eq_zero_iff, Q.val_add, Q.val_abs, Q.val_abs, Q.val_abs] at hsat
    exact hsat
  · intro m d2
    let e5 : Env [.nat, .nat, .rat, .nat, JetTy] :=
      Env.cons d2 (Env.cons m (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil))))
    change Q.add
      (Q.mul (((qpow2pos (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) m)
               (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (m + d2 + 1))))
      (Q.mul (((qpow2pos (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (m + d2 + 1))
               (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (m + d2 + 2)))) =
      Q.mul (((qpow2pos (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) m)
               (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (m + (d2 + 1) + 1)))
    rw [qpow2pos_eval_eq, qpow2_eval, qpow2_eval, qpow2_eval, qpow2_eval]
    exact satisfies_qTelescope F.M m d2
  · intro s d2
    let e5 : Env [.nat, .nat, .rat, .nat, JetTy] :=
      Env.cons d2 (Env.cons s (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil))))
    change Q.ltN
      (Q.mul (((qpow2pos (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (s + (F.M + 3)))
               (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (s + (F.M + 3) + d2 + 1))))
      (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) s) = 1
    rw [qpow2pos_eval_eq, qpow2_eval, qpow2_eval, qpow2_eval]
    exact satisfies_qScaleCancel F.M s d2

/-- Realizability of `qHalvePremise` for `F : RadiusJet`. -/
theorem uEval_mr_qHalvePremise (F : RadiusJet) (x : Q) :
    MR (qHalvePremise []) (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil)))
      ⟨fun _ _ ↦ (), fun _ _ _ _ ↦ ()⟩ := by
  refine ⟨?_, ?_⟩
  · intro d1 d2
    let e5 : Env [.nat, .nat, .rat, .nat, JetTy] :=
      Env.cons d2 (Env.cons d1 (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil))))
    change Q.ltN
      (Q.mul (((qpow2pos (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (F.M + 3 + d1))
               (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) (F.M + 3 + d1 + d2 + 1))))
      (((qpow2 (Γ := [.nat, .nat, .rat, .nat, JetTy])).eval e5) 0) = 1
    rw [qpow2pos_eval_eq, qpow2_eval, qpow2_eval, qpow2_eval]
    exact satisfies_qHalveBase F.M d1 d2
  · intro m e2 k _ hpre
    let e6 : Env [.nat, .nat, .nat, .rat, .nat, JetTy] :=
      Env.cons k (Env.cons e2 (Env.cons m (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil)))))
    change Q.ltN
      (Q.mul (((qpow2pos (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) m)
               (((qpow2 (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) (m + e2 + 1))))
      (((qpow2 (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) k) = 1 at hpre
    change Q.ltN
      (Q.mul (((qpow2pos (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) (F.M + 3))
        (Q.sub (((qpow2 (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) (m + 1))
               (((qpow2 (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) (m + 1 + e2 + 1))))
      (((qpow2 (Γ := [.nat, .nat, .nat, .rat, .nat, JetTy])).eval e6) (k + 1)) = 1
    rw [qpow2pos_eval_eq, qpow2_eval, qpow2_eval, qpow2_eval] at hpre ⊢
    exact satisfies_qHalveStep F.M m e2 k hpre

/-- **The proof-computed Cauchy modulus is correct**, through `soundness` applied to
    `jetCauchyModulusComputedD`, on the half-radius disk of any `RadiusJet`. -/
theorem RadiusJet.cauchyComputed_correct (F : RadiusJet) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 1)) (k d₁ d₂ : Nat) :
    let N := extractedJetCauchyModulusComputed F.toJet.coeff F.M x k
    |(F.toJet.evalPoly (N + d₁) x).val - (F.toJet.evalPoly (N + d₁ + d₂) x).val|
      < 1 / (2 : Rat) ^ k := by
  intro N
  have hs := soundness (jetCauchyModulusComputedD (Γ := []) (Δ := Ctx.nil))
    Env.nil Env.nil realizes_nil
    F.toJet.coeff F.M x
    (fun _ ↦ ()) (uEval_mr_jetTermPremise F x hx)
    ⟨fun _ ↦ (), ⟨fun _ _ _ ↦ (), ⟨fun _ _ ↦ (), fun _ _ ↦ ()⟩⟩⟩ (uEval_mr_qGeomArithPremise F x)
    ⟨fun _ _ ↦ (), fun _ _ _ _ ↦ ()⟩ (uEval_mr_qHalvePremise F x)
    k d₁ d₂
  let e7 : Env [.nat, .nat, .nat, .nat, .rat, .nat, JetTy] :=
    Env.cons d₂ (Env.cons d₁ (Env.cons N (Env.cons k (Env.cons x (Env.cons F.M (Env.cons F.toJet.coeff Env.nil))))))
  change ((qclose (Γ := [.nat, .nat, .nat, .nat, .rat, .nat, JetTy])).eval e7) k
    (((tmJetEvalPoly (Γ := [.nat, .nat, .nat, .nat, .rat, .nat, JetTy])).eval e7) F.toJet.coeff (N + d₁) x)
    (((tmJetEvalPoly (Γ := [.nat, .nat, .nat, .nat, .rat, .nat, JetTy])).eval e7) F.toJet.coeff (N + d₁ + d₂) x) = 1 at hs
  rw [uEval_tmJetEvalPoly_eval, uEval_tmJetEvalPoly_eval, uEval_qclose_eq_one_iff] at hs
  exact hs

/-- **Certified evaluation of the universe.** For every expression `e`, every rational
    point `x` in its disk and every precision `k`, the partial sums of `e`'s Taylor
    series past the proof-computed `N(k)` stay within `2^{-k}` of each other. -/
theorem UExpr.certifiedEval (e : UExpr) (h : e.Defined) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ ((e.radiusJet h).1.R + 1)) (k d : Nat) :
    let N := extractedJetCauchyModulusComputed e.eval (e.radiusJet h).1.M x k
    |(Jet.evalPoly ⟨e.eval⟩ (N + d) x).val - (Jet.evalPoly ⟨e.eval⟩ N x).val|
      < 1 / (2 : Rat) ^ k := by
  intro N
  let F := (e.radiusJet h).1
  have hF : F.toJet = ⟨e.eval⟩ := (e.radiusJet h).2
  have hcoeff : F.toJet.coeff = e.eval := congrArg Jet.coeff hF
  have hstep := F.cauchyComputed_correct x hx k 0 d
  dsimp only at hstep
  rw [hcoeff, hF, Nat.add_zero] at hstep
  rwa [abs_sub_comm]

/-- The bound parameters `(M, R)` of `UExpr.radiusJet`, by a plain recursion: the
    runnable evaluator reads them from here, so it carries none of the bound proofs. -/
def UExpr.radiusParams : UExpr → Nat × Nat
  | .const q => (q.num.natAbs, 0)
  | .x | .exp | .sin | .cos => (0, 0)
  | .add a b | .sub a b => (max a.radiusParams.1 b.radiusParams.1 + 1, max a.radiusParams.2 b.radiusParams.2)
  | .mul a b => (a.radiusParams.1 + b.radiusParams.1 + 1, max a.radiusParams.2 b.radiusParams.2 + 1)
  | .inv a =>
    let q0 := Q.div (Q.ofNat 1) (a.eval 0)
    (q0.num.natAbs, q0.num.natAbs + a.radiusParams.1 + a.radiusParams.2 + 1)
  | .integ a => a.radiusParams
  | .deriv a => (a.radiusParams.1 + a.radiusParams.2 + 1, a.radiusParams.2 + 1)
  | .comp a b => (a.radiusParams.1, a.radiusParams.2 + b.radiusParams.1 + b.radiusParams.2 + 1)

theorem UExpr.radiusParams_eq : (e : UExpr) → (h : e.Defined) →
    ((e.radiusJet h).1.M, (e.radiusJet h).1.R) = e.radiusParams
  | .const _, _ | .x, _ | .exp, _ | .sin, _ | .cos, _ => rfl
  | .add a b, h | .sub a b, h | .mul a b, h | .comp a b, h => by
    have ha := a.radiusParams_eq h.1
    have hb := b.radiusParams_eq h.2
    rcases hA : a.radiusJet h.1 with ⟨FA, hFA⟩
    rcases hB : b.radiusJet h.2 with ⟨FB, hFB⟩
    rw [hA] at ha
    rw [hB] at hb
    simp only [UExpr.radiusJet, hA, hB, UExpr.radiusParams, ← ha, ← hb]
    rfl
  | .inv a, h => by
    have ha := a.radiusParams_eq h.1
    rcases hA : a.radiusJet h.1 with ⟨FA, hFA⟩
    rw [hA] at ha
    simp only [UExpr.radiusJet, hA, UExpr.radiusParams, ← ha]
    rfl
  | .integ a, h | .deriv a, h => by
    have ha := a.radiusParams_eq h
    rcases hA : a.radiusJet h with ⟨FA, hFA⟩
    rw [hA] at ha
    simp only [UExpr.radiusJet, hA, UExpr.radiusParams, ← ha]
    rfl

/-- The certified approximation of `e` at `x` to precision `2^{-k}`. -/
def UExpr.approx (e : UExpr) (x : Q) (k : Nat) : Q :=
  Jet.evalPoly ⟨e.eval⟩ (extractedJetCauchyModulusComputed e.eval e.radiusParams.1 x k) x

/-- **The evaluator is certified**: for a defined `e` and `x` in its disk
    `|x| ≤ 2^{-(R+1)}`, every later partial sum is within `2^{-k}` of `e.approx x k`. -/
theorem UExpr.approx_spec (e : UExpr) (h : e.Defined) (x : Q)
    (hx : |x.val| ≤ 1 / (2 : Rat) ^ (e.radiusParams.2 + 1)) (k d : Nat) :
    |(Jet.evalPoly ⟨e.eval⟩
        (extractedJetCauchyModulusComputed e.eval e.radiusParams.1 x k + d) x).val
      - (e.approx x k).val| < 1 / (2 : Rat) ^ k := by
  have hp := e.radiusParams_eq h
  have hM : (e.radiusJet h).1.M = e.radiusParams.1 := congrArg Prod.fst hp
  have hR : (e.radiusJet h).1.R = e.radiusParams.2 := congrArg Prod.snd hp
  rw [← hR] at hx
  have := e.certifiedEval h x hx k d
  simp only [hM] at this
  exact this

/-! ## Example: `tan` at `x = 1/16`

`tan = sin · (1/cos)` gets `(M, R) = (2, 3)`, so its disk is `|x| ≤ 1/16` and the
modulus is `N(k) = k + 5`. At `k = 20` the certified value agrees with the
floating-point `tan (1/16) = 0.0625815075…` to `10⁻⁹` (the guarantee is `2^{-20}`). -/

/-- `tan`, as an expression of the universe. -/
def uEvalTan : UExpr := .mul .sin (.inv .cos)

theorem uEvalTan_defined : uEvalTan.Defined := ⟨trivial, trivial, by
  show (Jet.cos.coeff 0).val ≠ 0
  rw [show Jet.cos.coeff 0 = Q.ofNat 1 by decide, Q.val_ofNat]
  norm_num⟩

#guard uEvalTan.radiusParams = (2, 3)
#guard extractedJetCauchyModulusComputed uEvalTan.eval uEvalTan.radiusParams.1 ⟨1, 15⟩ 20 = 25
#guard let q := uEvalTan.approx ⟨1, 15⟩ 20
  Float.abs (Float.ofInt q.num / Float.ofNat (q.denPred + 1) - 0.0625815075) < 1e-9

#print axioms UExpr.radiusJet
#print axioms RadiusJet.cauchyComputed_correct
#print axioms UExpr.certifiedEval
#print axioms UExpr.radiusParams_eq
#print axioms UExpr.approx
#print axioms UExpr.approx_spec

end HAomega
