/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.SystemFast
import HAomega.SystemPerturb
import HAomega.UniverseExpr

/-!
# Helper lemmas for re-centering a flat polynomial system

Polynomial shift operator `rctShift`, finite-support tracking `rctSuppAt`,
binomial evaluation identity, Cauchy product multiplicativity, derivative
commutation, residual geometric bounds, and perturbed table majorants for
`SystemRecenter.lean`.
-/

namespace HAomega

/-- Lift a Mathlib rational `r : Rat` to `Q`. Proof-side only. -/
def rctOfRat (r : Rat) : Q := Q.of r.num r.den

@[simp]
theorem rctOfRat_val (r : Rat) : (rctOfRat r).val = r := by
  unfold rctOfRat
  rw [Q.val_of r.num r.den r.den_nz]
  exact Rat.num_div_den r

/-- `Jet.evalPoly ⟨f⟩ N x` in `Rat` equals `∑ m ∈ Finset.range N, (f m).val * x.val ^ m`. -/
theorem rct_evalPoly_val_eq_sum (f : Nat → Q) : ∀ (N : Nat) (x : Q),
    (Jet.evalPoly ⟨f⟩ N x).val = ∑ m ∈ Finset.range N, (f m).val * x.val ^ m
  | 0, _ => by simp [Jet.evalPoly, Q.val_zero]
  | n + 1, x => by
    rw [Jet.evalPoly_succ ⟨f⟩ n x, rct_evalPoly_val_eq_sum f n x, Finset.sum_range_succ]

/-- `f : Nat → Q` vanishes in value from degree `D` onwards. -/
def rctSuppAt (D : Nat) (f : Nat → Q) : Prop :=
  ∀ m : Nat, D ≤ m → (f m).val = 0

theorem rctSuppAt_mono {D D' : Nat} (h : D ≤ D') {f : Nat → Q} (hf : rctSuppAt D f) :
    rctSuppAt D' f :=
  fun m hm ↦ hf m (le_trans h hm)

/-- If `rctSuppAt D f` and `D ≤ L`, `evalPoly` at `L` equals `evalPoly` at `D`. -/
theorem rct_evalPoly_eq_of_supp {D L : Nat} (hDL : D ≤ L) (f : Nat → Q)
    (hf : rctSuppAt D f) (x : Q) :
    (Jet.evalPoly ⟨f⟩ L x).val = (Jet.evalPoly ⟨f⟩ D x).val := by
  rw [rct_evalPoly_val_eq_sum, rct_evalPoly_val_eq_sum]
  symm
  refine Finset.sum_subset (Finset.range_mono hDL) fun m _ hnot ↦ ?_
  rw [Finset.mem_range, not_lt] at hnot
  rw [hf m hnot, zero_mul]

/-- Polynomial shift by `x₀ : Rat` of a jet truncated at `D`:
    `(rctShift x₀ D f n).val = ∑_{m < D} C(m, n) (f m).val x₀^{m - n}`. -/
def rctShift (x₀ : Rat) (D : Nat) (f : Nat → Q) (n : Nat) : Q :=
  rctOfRat (∑ m ∈ Finset.range D, (m.choose n : Rat) * (f m).val * x₀ ^ (m - n))

@[simp]
theorem rctShift_val (x₀ : Rat) (D : Nat) (f : Nat → Q) (n : Nat) :
    (rctShift x₀ D f n).val =
      ∑ m ∈ Finset.range D, (m.choose n : Rat) * (f m).val * x₀ ^ (m - n) :=
  rctOfRat_val _

theorem rctShift_congr (x₀ : Rat) (D : Nat) (f g : Nat → Q)
    (h : ∀ m < D, (f m).val = (g m).val) (n : Nat) :
    (rctShift x₀ D f n).val = (rctShift x₀ D g n).val := by
  rw [rctShift_val, rctShift_val]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [h m hm]

theorem rctShift_supp (x₀ : Rat) (D : Nat) (f : Nat → Q) :
    rctSuppAt D (rctShift x₀ D f) := by
  intro n hn
  rw [rctShift_val]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  have hlt : m < n := Nat.lt_of_lt_of_le hm hn
  rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul, zero_mul]

theorem rctShift_eq_of_supp (x₀ : Rat) {D D' : Nat} (hDD' : D ≤ D') (f : Nat → Q)
    (hf : rctSuppAt D f) (n : Nat) :
    (rctShift x₀ D' f n).val = (rctShift x₀ D f n).val := by
  rw [rctShift_val, rctShift_val]
  symm
  refine Finset.sum_subset (Finset.range_mono hDD') fun m _ hnot ↦ ?_
  rw [Finset.mem_range, not_lt] at hnot
  rw [hf m hnot, mul_zero, zero_mul]

/-- At degree `0`, `rctShift x₀.val D f 0` has value `(Jet.evalPoly ⟨f⟩ D x₀).val`. -/
theorem rctShift_zero_deg (x₀ : Q) (D : Nat) (f : Nat → Q) :
    (rctShift x₀.val D f 0).val = (Jet.evalPoly ⟨f⟩ D x₀).val := by
  rw [rctShift_val, rct_evalPoly_val_eq_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]

/-- **Step 1(i): Binomial evaluation identity for `rctShift`.**
    For `D ≤ L`, `S_L(τ_{x₀} f)(t) = S_D(f)(x₀ + t)`. -/
theorem rct_evalPoly_shift (x₀ t : Q) (D L : Nat) (hDL : D ≤ L) (f : Nat → Q) :
    (Jet.evalPoly ⟨rctShift x₀.val D f⟩ L t).val =
      (Jet.evalPoly ⟨f⟩ D (Q.add x₀ t)).val := by
  rw [rct_evalPoly_eq_of_supp hDL _ (rctShift_supp x₀.val D f) t,
      rct_evalPoly_val_eq_sum, rct_evalPoly_val_eq_sum]
  have h1 :
      (∑ n ∈ Finset.range D, (rctShift x₀.val D f n).val * t.val ^ n) =
      ∑ n ∈ Finset.range D, ∑ m ∈ Finset.range D,
        (f m).val * (t.val ^ n * x₀.val ^ (m - n) * (m.choose n : Rat)) := by
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [rctShift_val, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    ring
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [← Finset.mul_sum]
  congr 1
  have hsub :
      (∑ n ∈ Finset.range D, (t.val ^ n * x₀.val ^ (m - n) * (m.choose n : Rat))) =
      ∑ n ∈ Finset.range (m + 1), (t.val ^ n * x₀.val ^ (m - n) * (m.choose n : Rat)) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hnot ↦ ?_
    rw [Finset.mem_range, not_lt] at hnot
    have hlt : m < n := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
  rw [hsub, ← add_pow t.val x₀.val m, Q.val_add, add_comm]

theorem rctShift_add (x₀ : Rat) (D : Nat) (f g : Nat → Q) (n : Nat) :
    (rctShift x₀ D (fun m ↦ Q.add (f m) (g m)) n).val =
      (rctShift x₀ D f n).val + (rctShift x₀ D g n).val := by
  rw [rctShift_val, rctShift_val, rctShift_val, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Q.val_add]
  ring

theorem rctShift_sub (x₀ : Rat) (D : Nat) (f g : Nat → Q) (n : Nat) :
    (rctShift x₀ D (fun m ↦ Q.sub (f m) (g m)) n).val =
      (rctShift x₀ D f n).val - (rctShift x₀ D g n).val := by
  rw [rctShift_val, rctShift_val, rctShift_val, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Q.val_sub]
  ring

/-- Support of a Cauchy product of finitely-supported jets. -/
theorem rctSuppAt_mul {Da Db : Nat} {f g : Nat → Q}
    (hf : rctSuppAt Da f) (hg : rctSuppAt Db g) :
    rctSuppAt (Da + Db) (((tmJetMul (Γ := [])).eval Env.nil) f g) := by
  intro m hm
  rw [inv_jetMul_val]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  by_cases hjDa : Da ≤ j
  · rw [hf j hjDa, zero_mul]
  · have hDb : Db ≤ m - j := by omega
    rw [hg (m - j) hDb, mul_zero]

/-- Reindexing a triangular sum `m < D, a ≤ m` into `a < D, b < D - a` with `m = a + b`. -/
theorem rct_sum_triangle_reindex : ∀ (D : Nat) (Φ : Nat → Nat → Rat),
    (∑ m ∈ Finset.range D, ∑ a ∈ Finset.range (m + 1), Φ m a) =
      ∑ a ∈ Finset.range D, ∑ b ∈ Finset.range (D - a), Φ (a + b) a
  | 0, _ => by simp
  | D + 1, Φ => by
    rw [Finset.sum_range_succ, rct_sum_triangle_reindex D Φ,
        Finset.sum_range_succ (fun a ↦ Φ D a) D,
        Finset.sum_range_succ (fun a ↦ ∑ b ∈ Finset.range (D + 1 - a), Φ (a + b) a) D]
    rw [Nat.add_sub_self_left D 1, Finset.sum_range_one, Nat.add_zero, ← add_assoc,
        ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Finset.mem_range] at ha
    have hsub : D + 1 - a = (D - a) + 1 := by omega
    have hadd : a + (D - a) = D := by omega
    rw [hsub, Finset.sum_range_succ, hadd]

/-- Rectangular reduction of a triangular sum when `Ψ a b = 0` outside `a < Da ∧ b < Db`. -/
theorem rct_sum_triangle_supp (Da Db : Nat) (Ψ : Nat → Nat → Rat)
    (hΨ : ∀ a b, Da ≤ a ∨ Db ≤ b → Ψ a b = 0) :
    (∑ m ∈ Finset.range (Da + Db), ∑ a ∈ Finset.range (m + 1), Ψ a (m - a)) =
      ∑ a ∈ Finset.range Da, ∑ b ∈ Finset.range Db, Ψ a b := by
  rw [rct_sum_triangle_reindex (Da + Db) (fun m a ↦ Ψ a (m - a))]
  have h1 :
      (∑ a ∈ Finset.range (Da + Db), ∑ b ∈ Finset.range (Da + Db - a), Ψ a (a + b - a)) =
      ∑ a ∈ Finset.range Da, ∑ b ∈ Finset.range (Da + Db - a), Ψ a (a + b - a) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun a _ hnot ↦ ?_
    rw [Finset.mem_range, not_lt] at hnot
    exact Finset.sum_eq_zero fun b _ ↦ hΨ a (a + b - a) (Or.inl hnot)
  rw [h1]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.mem_range] at ha
  symm
  trans (∑ b ∈ Finset.range Db, Ψ a (a + b - a))
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Nat.add_sub_cancel_left]
  · refine Finset.sum_subset (Finset.range_mono (by omega)) fun b _ hnot ↦ ?_
    rw [Finset.mem_range, not_lt] at hnot
    rw [Nat.add_sub_cancel_left]
    exact hΨ a b (Or.inr hnot)

/-- Vandermonde convolution identity with powers of `x₀`. -/
theorem rct_vandermonde_term (x₀ : Rat) (a b n : Nat) :
    (∑ j ∈ Finset.range (n + 1),
      ((a.choose j : Rat) * x₀ ^ (a - j)) *
        ((b.choose (n - j) : Rat) * x₀ ^ (b - (n - j)))) =
    ((a + b).choose n : Rat) * x₀ ^ (a + b - n) := by
  have h1 :
      (∑ j ∈ Finset.range (n + 1),
        ((a.choose j : Rat) * x₀ ^ (a - j)) *
          ((b.choose (n - j) : Rat) * x₀ ^ (b - (n - j)))) =
      ∑ j ∈ Finset.range (n + 1),
        ((a.choose j * b.choose (n - j) : Nat) : Rat) * x₀ ^ (a + b - n) := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    by_cases hja : j ≤ a
    · by_cases hjb : n - j ≤ b
      · have hexp : (a - j) + (b - (n - j)) = a + b - n := by omega
        push_cast
        calc ((a.choose j : Rat) * x₀ ^ (a - j)) * ((b.choose (n - j) : Rat) * x₀ ^ (b - (n - j)))
            = (a.choose j : Rat) * (b.choose (n - j) : Rat) * (x₀ ^ (a - j) * x₀ ^ (b - (n - j))) := by ring
          _ = (a.choose j : Rat) * (b.choose (n - j) : Rat) * x₀ ^ (a + b - n) := by
            rw [← pow_add, hexp]
      · have hlt : b < n - j := by omega
        rw [Nat.choose_eq_zero_of_lt hlt]
        simp
    · have hlt : a < j := by omega
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
  rw [h1, ← Finset.sum_mul]
  congr 1
  have hv := Nat.add_choose_eq a b n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ a.choose i * b.choose j) n] at hv
  exact_mod_cast hv.symm

/-- **Step 1(ii): `rctShift` commutes with Cauchy multiplication of supported polynomials.** -/
theorem rctShift_mul (x₀ : Rat) {Da Db : Nat} (f g : Nat → Q)
    (hf : rctSuppAt Da f) (hg : rctSuppAt Db g) (n : Nat) :
    (rctShift x₀ (Da + Db) (((tmJetMul (Γ := [])).eval Env.nil) f g) n).val =
      ((((tmJetMul (Γ := [])).eval Env.nil) (rctShift x₀ Da f) (rctShift x₀ Db g)) n).val := by
  rw [rctShift_val, inv_jetMul_val]
  have hL :
      (∑ m ∈ Finset.range (Da + Db),
        (m.choose n : Rat) * ((((tmJetMul (Γ := [])).eval Env.nil) f g) m).val * x₀ ^ (m - n)) =
      ∑ m ∈ Finset.range (Da + Db), ∑ a ∈ Finset.range (m + 1),
        ((a + (m - a)).choose n : Rat) * (f a).val * (g (m - a)).val * x₀ ^ (a + (m - a) - n) := by
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [inv_jetMul_val, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [Finset.mem_range] at ha
    have hadd : a + (m - a) = m := by omega
    rw [hadd]
    ring
  rw [hL, rct_sum_triangle_supp Da Db
    (fun a b ↦ ((a + b).choose n : Rat) * (f a).val * (g b).val * x₀ ^ (a + b - n))]
  · have hR :
        (∑ i ∈ Finset.range (n + 1),
          (rctShift x₀ Da f i).val * (rctShift x₀ Db g (n - i)).val) =
        ∑ a ∈ Finset.range Da, ∑ b ∈ Finset.range Db,
          (f a).val * (g b).val *
            (∑ i ∈ Finset.range (n + 1),
              ((a.choose i : Rat) * x₀ ^ (a - i)) *
                ((b.choose (n - i) : Rat) * x₀ ^ (b - (n - i)))) := by
      trans (∑ i ∈ Finset.range (n + 1),
        ∑ a ∈ Finset.range Da, ∑ b ∈ Finset.range Db,
          (f a).val * (g b).val *
            (((a.choose i : Rat) * x₀ ^ (a - i)) *
              ((b.choose (n - i) : Rat) * x₀ ^ (b - (n - i)))))
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [rctShift_val, rctShift_val, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        ring
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [← Finset.mul_sum]
    rw [hR]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [rct_vandermonde_term]
    ring
  · intro a b hab
    rcases hab with ha | hb
    · rw [hf a ha]; ring
    · rw [hg b hb]; ring

/-- **Step 1(iv): `rctShift` fixes constant jets.** -/
theorem rctSuppAt_constJet {c : Tm [] JetTy} (hc : IsConstJet c) :
    rctSuppAt 1 (c.eval Env.nil) := by
  intro m hm
  cases m with
  | zero => omega
  | succ k => exact hc k

theorem rctShift_constJet (x₀ : Rat) {D : Nat} (hD : 1 ≤ D) {c : Tm [] JetTy}
    (hc : IsConstJet c) (n : Nat) :
    (rctShift x₀ D (c.eval Env.nil) n).val = (c.eval Env.nil n).val := by
  rw [rctShift_eq_of_supp x₀ hD _ (rctSuppAt_constJet hc), rctShift_val, Finset.sum_range_one]
  cases n with
  | zero =>
    rw [Nat.choose_self, Nat.cast_one, Nat.sub_zero, pow_zero, one_mul, mul_one]
  | succ k =>
    rw [Nat.choose_eq_zero_of_lt (Nat.succ_pos k), Nat.cast_zero, zero_mul, zero_mul, hc k]

/-- Syntactic degree bound for `sbdEvalExpr F W` when variables are supported below `N`. -/
def rctExprDeg : JExprN → Nat → Nat
  | .var _, N => N
  | .const _, N => N
  | .add a b, N => max (rctExprDeg a N) (rctExprDeg b N)
  | .sub a b, N => max (rctExprDeg a N) (rctExprDeg b N)
  | .mul a b, N => rctExprDeg a N + rctExprDeg b N
  | .integ a, N => rctExprDeg a N + 1

theorem rctExprDeg_ge (F : JExprN) (N : Nat) : N ≤ rctExprDeg F N := by
  induction F with
  | var _ => exact le_refl N
  | const _ => exact le_refl N
  | add a _ iha _ => exact le_trans iha (le_max_left _ _)
  | sub a _ iha _ => exact le_trans iha (le_max_left _ _)
  | mul a _ iha _ => exact le_trans iha (Nat.le_add_right _ _)
  | integ a iha => exact le_trans iha (Nat.le_succ _)

theorem rct_sbdEvalExpr_var (i : Nat) (W : Nat → Nat → Q) :
    sbdEvalExpr (.var i) W = W i := by
  funext m
  change (Tm.var (Γ := [WTy]) .here).eval (Env.cons (σ := WTy) W Env.nil)
    ((natTm i).eval (Env.cons (σ := WTy) W Env.nil)) m = W i m
  rw [natTm_eval]; rfl

theorem rct_sbdEvalExpr_const (c : Tm [] JetTy) (W : Nat → Nat → Q) :
    sbdEvalExpr (.const c) W = c.eval Env.nil := by
  funext m
  dsimp [sbdEvalExpr, JExprN.toTm]; rw [closedWk_eval]

theorem rct_sbdEvalExpr_add (a b : JExprN) (W : Nat → Nat → Q) :
    sbdEvalExpr (.add a b) W = fun m ↦ Q.add (sbdEvalExpr a W m) (sbdEvalExpr b W m) := rfl

theorem rct_sbdEvalExpr_sub (a b : JExprN) (W : Nat → Nat → Q) :
    sbdEvalExpr (.sub a b) W = fun m ↦ Q.sub (sbdEvalExpr a W m) (sbdEvalExpr b W m) := rfl

theorem rct_sbdEvalExpr_mul (a b : JExprN) (W : Nat → Nat → Q) :
    sbdEvalExpr (.mul a b) W =
      ((tmJetMul (Γ := [])).eval Env.nil) (sbdEvalExpr a W) (sbdEvalExpr b W) := rfl

/-- If `W u` is supported below `N` (`1 ≤ N`), `sbdEvalExpr F W` is supported below `rctExprDeg F N`. -/
theorem rct_sbdEvalExpr_supp (F : JExprN) (sysLen : Nat) (hWF : F.WF sysLen)
    (hCC : F.ConstsConst) (hNo : F.NoInteg) (W : Nat → Nat → Q) {N : Nat} (hN : 1 ≤ N)
    (hW : ∀ u < sysLen, rctSuppAt N (W u)) :
    rctSuppAt (rctExprDeg F N) (sbdEvalExpr F W) := by
  induction F with
  | var i =>
    rw [rct_sbdEvalExpr_var]
    exact hW i hWF
  | const c =>
    rw [rct_sbdEvalExpr_const]
    exact rctSuppAt_mono hN (rctSuppAt_constJet hCC)
  | add a b iha ihb =>
    intro m hm
    rw [rct_sbdEvalExpr_add]
    dsimp only
    rw [Q.val_add, iha hWF.1 hCC.1 hNo.1 m (le_trans (le_max_left _ _) hm),
        ihb hWF.2 hCC.2 hNo.2 m (le_trans (le_max_right _ _) hm), add_zero]
  | sub a b iha ihb =>
    intro m hm
    rw [rct_sbdEvalExpr_sub]
    dsimp only
    rw [Q.val_sub, iha hWF.1 hCC.1 hNo.1 m (le_trans (le_max_left _ _) hm),
        ihb hWF.2 hCC.2 hNo.2 m (le_trans (le_max_right _ _) hm), sub_zero]
  | mul a b iha ihb =>
    rw [rct_sbdEvalExpr_mul]
    exact rctSuppAt_mul (iha hWF.1 hCC.1 hNo.1) (ihb hWF.2 hCC.2 hNo.2)
  | integ _ _ => exact False.elim hNo

/-- `rctShift` commutes with `sbdEvalExpr F` for every flat expression `F`. -/
theorem rct_sbdEvalExpr_shift (F : JExprN) (sysLen : Nat) (hWF : F.WF sysLen)
    (hCC : F.ConstsConst) (hNo : F.NoInteg) (W : Nat → Nat → Q) (x₀ : Rat) {N D : Nat}
    (hN : 1 ≤ N) (hD : rctExprDeg F N ≤ D) (hW : ∀ u < sysLen, rctSuppAt N (W u)) (n : Nat) :
    (rctShift x₀ D (sbdEvalExpr F W) n).val =
      (sbdEvalExpr F (fun u ↦ rctShift x₀ N (W u)) n).val := by
  induction F generalizing D n with
  | var i =>
    dsimp [rctExprDeg] at hD
    rw [rct_sbdEvalExpr_var, rct_sbdEvalExpr_var]
    exact rctShift_eq_of_supp x₀ hD (W i) (hW i hWF) n
  | const c =>
    dsimp [rctExprDeg] at hD
    rw [rct_sbdEvalExpr_const, rct_sbdEvalExpr_const]
    exact rctShift_constJet x₀ (le_trans hN hD) hCC n
  | add a b iha ihb =>
    dsimp [rctExprDeg] at hD
    rw [rct_sbdEvalExpr_add, rct_sbdEvalExpr_add]
    dsimp only
    rw [rctShift_add x₀ D (sbdEvalExpr a W) (sbdEvalExpr b W) n,
        iha hWF.1 hCC.1 hNo.1 (le_trans (le_max_left _ _) hD) n,
        ihb hWF.2 hCC.2 hNo.2 (le_trans (le_max_right _ _) hD) n,
        Q.val_add]
  | sub a b iha ihb =>
    dsimp [rctExprDeg] at hD
    rw [rct_sbdEvalExpr_sub, rct_sbdEvalExpr_sub]
    dsimp only
    rw [rctShift_sub x₀ D (sbdEvalExpr a W) (sbdEvalExpr b W) n,
        iha hWF.1 hCC.1 hNo.1 (le_trans (le_max_left _ _) hD) n,
        ihb hWF.2 hCC.2 hNo.2 (le_trans (le_max_right _ _) hD) n,
        Q.val_sub]
  | mul a b iha ihb =>
    dsimp [rctExprDeg] at hD
    have hSa := rct_sbdEvalExpr_supp a sysLen hWF.1 hCC.1 hNo.1 W hN hW
    have hSb := rct_sbdEvalExpr_supp b sysLen hWF.2 hCC.2 hNo.2 W hN hW
    rw [rct_sbdEvalExpr_mul, rct_sbdEvalExpr_mul,
        rctShift_eq_of_supp x₀ hD _ (rctSuppAt_mul hSa hSb) n,
        rctShift_mul x₀ _ _ hSa hSb n]
    exact tmJetMul_agreeV Env.nil Env.nil (n + 1)
      (rctShift x₀ (rctExprDeg a N) (sbdEvalExpr a W))
      (sbdEvalExpr a (fun u ↦ rctShift x₀ N (W u)))
      (rctShift x₀ (rctExprDeg b N) (sbdEvalExpr b W))
      (sbdEvalExpr b (fun u ↦ rctShift x₀ N (W u)))
      (fun i _ ↦ iha hWF.1 hCC.1 hNo.1 (le_refl _) i)
      (fun i _ ↦ ihb hWF.2 hCC.2 hNo.2 (le_refl _) i)
      n (Nat.lt_succ_self n)
  | integ _ _ => exact False.elim hNo

/-- **Step 1(iii): `rctShift` commutes with formal differentiation.** -/
theorem rctShift_deriv (x₀ : Rat) {N D : Nat} (hND : N ≤ D) (f : Nat → Q)
    (hf : rctSuppAt N f) (n : Nat) :
    ((n + 1 : Nat) : Rat) * (rctShift x₀ N f (n + 1)).val =
      (rctShift x₀ D (fun m ↦ Q.mul (Q.ofNat (m + 1)) (f (m + 1))) n).val := by
  let f' : Nat → Q := fun m ↦ Q.mul (Q.ofNat (m + 1)) (f (m + 1))
  have hf' : rctSuppAt N f' := by
    intro m hm
    dsimp [f']
    rw [Q.val_mul, hf (m + 1) (Nat.le_succ_of_le hm), mul_zero]
  rw [rctShift_eq_of_supp x₀ hND f' hf' n, rctShift_val, rctShift_val, Finset.mul_sum]
  cases N with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ' _ M, Nat.choose_zero_succ, Nat.cast_zero,
        zero_mul, zero_mul, mul_zero, add_zero, Finset.sum_range_succ _ M]
    have hM : (M.choose n : Rat) * (f' M).val * x₀ ^ (M - n) = 0 := by
      dsimp [f']
      rw [Q.val_mul, hf (M + 1) (le_refl _), mul_zero, mul_zero, zero_mul]
    rw [hM, add_zero]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hchoose : ((n + 1 : Nat) : Rat) * ((k + 1).choose (n + 1) : Rat) =
        (k.choose n : Rat) * ((k + 1 : Nat) : Rat) := by
      have hnat := (Nat.add_one_mul_choose_eq k n).symm
      have hrat : (((k + 1).choose (n + 1) * (n + 1) : Nat) : Rat) =
          (((k + 1) * k.choose n : Nat) : Rat) := by exact_mod_cast hnat
      push_cast at hrat ⊢
      linarith
    dsimp [f']
    rw [Q.val_mul, Q.val_ofNat, Nat.succ_sub_succ]
    calc ((n + 1 : Nat) : Rat) * (((k + 1).choose (n + 1) : Rat) * (f (k + 1)).val * x₀ ^ (k - n))
        = (((n + 1 : Nat) : Rat) * ((k + 1).choose (n + 1) : Rat)) * (f (k + 1)).val * x₀ ^ (k - n) := by ring
      _ = (k.choose n : Rat) * (((k + 1 : Nat) : Rat) * (f (k + 1)).val) * x₀ ^ (k - n) := by
        rw [hchoose]; ring

/-! ## Step 2: Truncation, residual, and shifted geometric bounds -/

/-- Truncate a jet `f : Nat → Q` at degree `N`. -/
def rctTrunc (N : Nat) (f : Nat → Q) (m : Nat) : Q :=
  if m < N then f m else Q.zero

theorem rctTrunc_lt {N m : Nat} (hm : m < N) (f : Nat → Q) :
    rctTrunc N f m = f m := if_pos hm

theorem rctTrunc_ge {N m : Nat} (hm : N ≤ m) (f : Nat → Q) :
    rctTrunc N f m = Q.zero := if_neg (not_lt.mpr hm)

theorem rctSuppAt_trunc (N : Nat) (f : Nat → Q) :
    rctSuppAt N (rctTrunc N f) := by
  intro m hm
  rw [rctTrunc_ge hm, Q.val_zero]

theorem rctShift_trunc_eq (x₀ : Rat) (N : Nat) (f : Nat → Q) (n : Nat) :
    (rctShift x₀ N (rctTrunc N f) n).val = (rctShift x₀ N f n).val :=
  rctShift_congr x₀ N (rctTrunc N f) f (fun _ hm ↦ by rw [rctTrunc_lt hm]) n

theorem rct_evalPoly_trunc_eq (N : Nat) (f : Nat → Q) (x : Q) :
    (Jet.evalPoly ⟨rctTrunc N f⟩ N x).val = (Jet.evalPoly ⟨f⟩ N x).val := by
  rw [rct_evalPoly_val_eq_sum, rct_evalPoly_val_eq_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Finset.mem_range] at hm
  rw [rctTrunc_lt hm]

/-- Residual of a truncated jet table `p : Nat → Nat → Q` for equation `F` of variable `v`:
    `r_v(m) = (m + 1) p_v(m + 1) - F(p)(m)`. -/
def rctResidual (F : JExprN) (p : Nat → Nat → Q) (v m : Nat) : Q :=
  Q.sub (Q.mul (Q.ofNat (m + 1)) (p v (m + 1))) (sbdEvalExpr F p m)

/-- **Step 2 recurrence for shifted truncated jets:**
    If `p u` is supported below `N` (`1 ≤ N`) and `rctExprDeg F N ≤ D`, then
    `d u := rctShift x₀ N (p u)` satisfies
    `(n + 1) * d_v(n + 1) = F(d)(n) + (τ_{x₀} r_v)(n)`. -/
theorem rct_shift_recurrence (F : JExprN) (sysLen : Nat) (hWF : F.WF sysLen)
    (hCC : F.ConstsConst) (hNo : F.NoInteg) (p : Nat → Nat → Q) (x₀ : Rat)
    {N D : Nat} (hN : 1 ≤ N) (hD : rctExprDeg F N ≤ D)
    (hp : ∀ u < sysLen, rctSuppAt N (p u)) (v : Nat) (hv : v < sysLen) (n : Nat) :
    ((n + 1 : Nat) : Rat) * (rctShift x₀ N (p v) (n + 1)).val =
      (sbdEvalExpr F (fun u ↦ rctShift x₀ N (p u)) n).val +
        (rctShift x₀ D (rctResidual F p v) n).val := by
  have hND : N ≤ D := le_trans (rctExprDeg_ge F N) hD
  rw [rctShift_deriv x₀ hND (p v) (hp v hv) n]
  unfold rctResidual
  rw [rctShift_sub x₀ D (fun m ↦ Q.mul (Q.ofNat (m + 1)) (p v (m + 1))) (sbdEvalExpr F p) n,
      rct_sbdEvalExpr_shift F sysLen hWF hCC hNo p x₀ hN hD hp n]
  ring

theorem rct_choose_le_two_pow_nat : ∀ m n : Nat, m.choose n ≤ 2 ^ m
  | 0, n => by cases n <;> simp
  | m + 1, 0 => by simp [Nat.one_le_two_pow]
  | m + 1, n + 1 => by
    rw [Nat.choose_succ_succ, Nat.pow_succ]
    have h1 := rct_choose_le_two_pow_nat m n
    have h2 := rct_choose_le_two_pow_nat m n.succ
    omega

theorem rct_choose_le_two_pow (m n : Nat) : (m.choose n : Rat) ≤ (2 : Rat) ^ m := by
  exact_mod_cast rct_choose_le_two_pow_nat m n

theorem rct_sum_half_pow_eq : ∀ D : Nat,
    (∑ m ∈ Finset.range D, (1 / 2 : Rat) ^ m) = 2 - 2 * (1 / 2 : Rat) ^ D
  | 0 => by simp
  | D + 1 => by
    rw [Finset.sum_range_succ, rct_sum_half_pow_eq D, pow_succ]
    ring

theorem rct_sum_half_pow_le_two (D : Nat) :
    (∑ m ∈ Finset.range D, (1 / 2 : Rat) ^ m) ≤ 2 := by
  rw [rct_sum_half_pow_eq D]
  have hpos : (0 : Rat) ≤ (1 / 2 : Rat) ^ D := by positivity
  linarith

theorem rct_half_pow_anti {a b : Nat} (hab : a ≤ b) :
    (1 / 2 : Rat) ^ b ≤ (1 / 2 : Rat) ^ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have h1 : (1 / 2 : Rat) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : Rat) ≤ (1 / 2 : Rat) ^ a := by positivity
  nlinarith

theorem rct_sbdSq_le_four_pow : ∀ n : Nat, sbdSq n ≤ (4 : Rat) ^ n
  | 0 => by unfold sbdSq; norm_num
  | k + 1 => by
    have h1 := sbdSq_succ_le_four k
    have ih := rct_sbdSq_le_four_pow k
    rw [pow_succ]
    linarith

/-- General geometric bound on `rctShift x₀ D f n`:
    if `f m = 0` for `m < M₀` and `|f m| ≤ C * B₀^m` for `m ≥ M₀`, and `|x₀| ≤ 1 / (8 * B₀)`,
    then `|(rctShift x₀ D f n).val| ≤ 2 * C * (1 / 2)^M₀ * (8 * B₀)^n`. -/
theorem rctShift_geom_bound (x₀ : Rat) (D M₀ : Nat) (f : Nat → Q) {C B₀ : Rat}
    (hC : 0 ≤ C) (hB₀ : 0 < B₀) (hx₀ : |x₀| ≤ 1 / (8 * B₀))
    (h_zero : ∀ m < M₀, (f m).val = 0)
    (h_bound : ∀ m, M₀ ≤ m → |(f m).val| ≤ C * B₀ ^ m) (n : Nat) :
    |(rctShift x₀ D f n).val| ≤ 2 * C * (1 / 2 : Rat) ^ M₀ * (8 * B₀) ^ n := by
  rw [rctShift_val]
  have h_abs :
      |∑ m ∈ Finset.range D, (m.choose n : Rat) * (f m).val * x₀ ^ (m - n)| ≤
      ∑ m ∈ Finset.range D, |(m.choose n : Rat) * (f m).val * x₀ ^ (m - n)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_terms :
      (∑ m ∈ Finset.range D, |(m.choose n : Rat) * (f m).val * x₀ ^ (m - n)|) ≤
      ∑ m ∈ Finset.range D, (C * (1 / 2 : Rat) ^ M₀ * (8 * B₀) ^ n) * (1 / 2 : Rat) ^ m := by
    refine Finset.sum_le_sum fun m _ ↦ ?_
    by_cases hmM : m < M₀
    · rw [h_zero m hmM, mul_zero, zero_mul, abs_zero]
      positivity
    · have hMm : M₀ ≤ m := not_lt.mp hmM
      by_cases hmn : m < n
      · rw [Nat.choose_eq_zero_of_lt hmn, Nat.cast_zero, zero_mul, zero_mul, abs_zero]
        positivity
      · have hnm : n ≤ m := not_lt.mp hmn
        have hch_nonneg : (0 : Rat) ≤ (m.choose n : Rat) := Nat.cast_nonneg _
        rw [abs_mul, abs_mul, abs_of_nonneg hch_nonneg, abs_pow]
        have h1 : (m.choose n : Rat) * |(f m).val| ≤ (2 : Rat) ^ m * (C * B₀ ^ m) :=
          mul_le_mul (rct_choose_le_two_pow m n) (h_bound m hMm) (abs_nonneg _) (by positivity)
        have h2 : (m.choose n : Rat) * |(f m).val| * |x₀| ^ (m - n) ≤
            (2 : Rat) ^ m * (C * B₀ ^ m) * |x₀| ^ (m - n) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h_2B : (2 : Rat) ^ m * B₀ ^ m =
            (1 / 2 : Rat) ^ m * (1 / 2 : Rat) ^ m * (8 * B₀) ^ m := by
          rw [← mul_pow, ← mul_pow, ← mul_pow]
          congr 1
          ring
        have hx8_le_1 : |x₀| * (8 * B₀) ≤ 1 := by
          have h8pos : (0 : Rat) < 8 * B₀ := by positivity
          have hmul := mul_le_mul_of_nonneg_right hx₀ (le_of_lt h8pos)
          rw [one_div_mul_cancel (ne_of_gt h8pos)] at hmul
          exact hmul
        have hx8_pow : |x₀| ^ (m - n) * (8 * B₀) ^ (m - n) ≤ 1 := by
          rw [← mul_pow]
          exact pow_le_one₀ (by positivity) hx8_le_1
        have h8_split : (8 * B₀) ^ m = (8 * B₀) ^ (m - n) * (8 * B₀) ^ n := by
          rw [← pow_add, Nat.sub_add_cancel hnm]
        have hx8_m : |x₀| ^ (m - n) * (8 * B₀) ^ m ≤ (8 * B₀) ^ n := by
          rw [h8_split, ← mul_assoc]
          have h8n_nonneg : (0 : Rat) ≤ (8 * B₀) ^ n := by positivity
          nlinarith
        have h_mid : (2 : Rat) ^ m * (C * B₀ ^ m) * |x₀| ^ (m - n) =
            (C * (1 / 2 : Rat) ^ m * (1 / 2 : Rat) ^ m) * (|x₀| ^ (m - n) * (8 * B₀) ^ m) := by
          calc (2 : Rat) ^ m * (C * B₀ ^ m) * |x₀| ^ (m - n)
              = C * ((2 : Rat) ^ m * B₀ ^ m) * |x₀| ^ (m - n) := by ring
            _ = (C * (1 / 2 : Rat) ^ m * (1 / 2 : Rat) ^ m) * (|x₀| ^ (m - n) * (8 * B₀) ^ m) := by
              rw [h_2B]; ring
        have h3 : (2 : Rat) ^ m * (C * B₀ ^ m) * |x₀| ^ (m - n) ≤
            (C * (1 / 2 : Rat) ^ m * (1 / 2 : Rat) ^ m) * (8 * B₀) ^ n := by
          rw [h_mid]
          exact mul_le_mul_of_nonneg_left hx8_m (by positivity)
        have h_anti : (1 / 2 : Rat) ^ m ≤ (1 / 2 : Rat) ^ M₀ := rct_half_pow_anti hMm
        have h4 : (C * (1 / 2 : Rat) ^ m * (1 / 2 : Rat) ^ m) * (8 * B₀) ^ n ≤
            (C * (1 / 2 : Rat) ^ M₀ * (8 * B₀) ^ n) * (1 / 2 : Rat) ^ m := by
          have h_pos : (0 : Rat) ≤ C * (1 / 2 : Rat) ^ m * (8 * B₀) ^ n := by positivity
          nlinarith
        linarith
  rw [← Finset.mul_sum] at h_terms
  have h_sum := mul_le_mul_of_nonneg_left (rct_sum_half_pow_le_two D)
    (show (0 : Rat) ≤ C * (1 / 2 : Rat) ^ M₀ * (8 * B₀) ^ n by positivity)
  linarith

/-- Weighted version of `rctShift_geom_bound` with `/ sbdSq n` and growth base `32 * B₀`. -/
theorem rctShift_weighted_bound (x₀ : Rat) (D M₀ : Nat) (f : Nat → Q) {C B₀ : Rat}
    (hC : 0 ≤ C) (hB₀ : 0 < B₀) (hx₀ : |x₀| ≤ 1 / (8 * B₀))
    (h_zero : ∀ m < M₀, (f m).val = 0)
    (h_bound : ∀ m, M₀ ≤ m → |(f m).val| ≤ C * B₀ ^ m) (n : Nat) :
    |(rctShift x₀ D f n).val| ≤ 2 * C * (1 / 2 : Rat) ^ M₀ * (32 * B₀) ^ n / sbdSq n := by
  have h1 := rctShift_geom_bound x₀ D M₀ f hC hB₀ hx₀ h_zero h_bound n
  have hsq_pos : (0 : Rat) < sbdSq n := sbdSq_pos n
  rw [le_div_iff₀ hsq_pos]
  have h2 : (8 * B₀) ^ n * sbdSq n ≤ (32 * B₀) ^ n := by
    have hsq4 := rct_sbdSq_le_four_pow n
    have hmul : (8 * B₀) ^ n * sbdSq n ≤ (8 * B₀) ^ n * (4 : Rat) ^ n :=
      mul_le_mul_of_nonneg_left hsq4 (by positivity)
    have hpow : (8 * B₀) ^ n * (4 : Rat) ^ n = (32 * B₀) ^ n := by
      rw [← mul_pow]
      congr 1
      ring
    linarith
  have h3 : (2 * C * (1 / 2 : Rat) ^ M₀) * ((8 * B₀) ^ n * sbdSq n) ≤
      (2 * C * (1 / 2 : Rat) ^ M₀) * (32 * B₀) ^ n :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 := mul_le_mul_of_nonneg_right h1 (le_of_lt hsq_pos)
  linarith

theorem rct_sysParams_B_ge_four (sys : List (Tm [] JetTy × JExprN)) :
    (4 : Rat) ≤ (2 : Rat) ^ (sysParams sys).2 := by
  let M := (sysMaxInitN sys).log2 + 1
  let P := sysMaxPhiN (2 ^ M) sys
  let R := (4 * P + 4).log2 + 1
  change (4 : Rat) ≤ (2 : Rat) ^ R
  have h := (Nat.lt_log2_self (n := 4 * P + 4)).le
  have h' : ((4 * P + 4 : Nat) : Rat) ≤ (2 : Rat) ^ R := by exact_mod_cast h
  push_cast at h'
  have : (0 : Rat) ≤ (P : Rat) := Nat.cast_nonneg P
  linarith

theorem rct_sysParams_step (sys : List (Tm [] JetTy × JExprN)) :
    ∀ p ∈ sys,
      4 * sbdExprBound p.2 ((2 : Rat) ^ (sysParams sys).1) ≤
        (2 : Rat) ^ (sysParams sys).1 * (2 : Rat) ^ (sysParams sys).2 := by
  intro p hp
  let M := (sysMaxInitN sys).log2 + 1
  let P := sysMaxPhiN (2 ^ M) sys
  let R := (4 * P + 4).log2 + 1
  change 4 * sbdExprBound p.2 ((2 : Rat) ^ M) ≤ (2 : Rat) ^ M * (2 : Rat) ^ R
  have hK1 : (1 : Rat) ≤ (2 : Rat) ^ M := one_le_pow₀ (by norm_num)
  have hKcast : (((2 ^ M : Nat) : Nat) : Rat) = (2 : Rat) ^ M := by push_cast; rfl
  have h1 := sbdExprBound_le_natBound p.2 (2 ^ M)
  rw [hKcast] at h1
  have h2 : (p.2.natBound (2 ^ M) : Rat) ≤ (P : Rat) := by exact_mod_cast sysMaxPhiN_mem _ hp
  have h3 : ((4 * P + 4 : Nat) : Rat) ≤ (2 : Rat) ^ R := by
    exact_mod_cast (Nat.lt_log2_self (n := 4 * P + 4)).le
  push_cast at h3
  have hR0 : (0 : Rat) ≤ (2 : Rat) ^ R := by positivity
  nlinarith

theorem rct_solFast_weighted_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (v : Nat) (hv : v < sys.length) (n : Nat) :
    |(solFast sys v n).val| ≤
      (2 : Rat) ^ (sysParams sys).1 * ((2 : Rat) ^ (sysParams sys).2) ^ n / sbdSq n := by
  rw [solFast_val sys h v hv n]
  let M := (sysParams sys).1
  have hInit : ∀ p ∈ sys, |(p.1.eval Env.nil 0).val| ≤ (2 : Rat) ^ M := by
    intro p hp
    have h1 := Q.abs_val_le_natAbsBound (p.1.eval Env.nil 0)
    have h2 : ((p.1.eval Env.nil 0).natAbsBound : Rat) ≤ (sysMaxInitN sys : Rat) := by
      exact_mod_cast sysMaxInitN_mem hp
    have h3 : ((sysMaxInitN sys : Nat) : Rat) ≤ (2 : Rat) ^ M := by
      have := (Nat.lt_log2_self (n := sysMaxInitN sys)).le
      exact_mod_cast this
    linarith
  exact sbd_solN_weighted_bound sys h (by positivity)
    (rct_sysParams_B_ge_four sys) hInit (rct_sysParams_step sys) n v hv

theorem rct_trunc_solFast_weighted_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (N u : Nat) (hu : u < sys.length) (m : Nat) :
    |(rctTrunc N (solFast sys u) m).val| ≤
      (2 : Rat) ^ (sysParams sys).1 * ((2 : Rat) ^ (sysParams sys).2) ^ m / sbdSq m := by
  by_cases hm : m < N
  · rw [rctTrunc_lt hm]
    exact rct_solFast_weighted_bound sys h u hu m
  · rw [rctTrunc_ge (not_lt.mp hm), Q.val_zero, abs_zero]
    have hsq : (0 : Rat) < sbdSq m := sbdSq_pos m
    positivity

/-- Below degree `N - 1`, the residual of `rctTrunc N (solFast sys)` vanishes. -/
theorem rct_residual_zero_lt (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (N v : Nat) (hv : v < sys.length) (m : Nat) (hm : m < N - 1) :
    (rctResidual sys[v].2 (fun u ↦ rctTrunc N (solFast sys u)) v m).val = 0 := by
  have hm1 : m + 1 < N := by omega
  have hpv := h sys[v] (List.getElem_mem hv)
  unfold rctResidual
  dsimp only
  rw [Q.val_sub, Q.val_mul, Q.val_ofNat, rctTrunc_lt hm1,
      solFast_val sys h v hv (m + 1), sbd_solN_succ_val sys h v hv m]
  have hk1_ne : ((m + 1 : Nat) : Rat) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hk1_ne]
  have hcongr := sfst_sbdEvalExpr_congr sys[v].2 sys.length hpv.1
    (fun u ↦ rctTrunc N (solFast sys u)) (solN sys) m fun u hu j hj ↦ by
      have hjN : j < N := by omega
      dsimp only
      rw [rctTrunc_lt hjN, solFast_val sys h u hu j]
  rw [hcongr, sub_self]

/-- From degree `N - 1` onwards, the residual is bounded by `(K₀ * B₀) * B₀^m`. -/
theorem rct_residual_bound_ge (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (N v : Nat) (hv : v < sys.length) (m : Nat) (hm : N - 1 ≤ m) :
    |(rctResidual sys[v].2 (fun u ↦ rctTrunc N (solFast sys u)) v m).val| ≤
      ((2 : Rat) ^ (sysParams sys).1 * (2 : Rat) ^ (sysParams sys).2) *
        ((2 : Rat) ^ (sysParams sys).2) ^ m := by
  have hm1 : N ≤ m + 1 := by omega
  have hpv := h sys[v] (List.getElem_mem hv)
  unfold rctResidual
  dsimp only
  rw [Q.val_sub, Q.val_mul, rctTrunc_ge hm1, Q.val_zero, mul_zero, zero_sub, abs_neg]
  let K₀ : Rat := (2 : Rat) ^ (sysParams sys).1
  let B₀ : Rat := (2 : Rat) ^ (sysParams sys).2
  have h_phi_nonneg : (0 : Rat) ≤ sbdExprBound sys[v].2 K₀ :=
    sbdExprBound_nonneg sys[v].2 (by positivity)
  have h_eb := sbd_evalExpr_bound sys[v].2 sys.length hpv.1 hpv.2.2
    (fun u ↦ rctTrunc N (solFast sys u)) (by positivity) (rct_sysParams_B_ge_four sys) m
    (fun u hu j _ ↦ rct_trunc_solFast_weighted_bound sys h N u hu j) m (le_refl m)
  have h_drop : sbdExprBound sys[v].2 K₀ * B₀ ^ m / sbdSq m ≤ sbdExprBound sys[v].2 K₀ * B₀ ^ m :=
    div_le_self (by positivity) (sbdSq_ge_one m)
  have h_step := rct_sysParams_step sys sys[v] (List.getElem_mem hv)
  have h_phi_le : sbdExprBound sys[v].2 K₀ ≤ K₀ * B₀ := by linarith
  have h_mul : sbdExprBound sys[v].2 K₀ * B₀ ^ m ≤ (K₀ * B₀) * B₀ ^ m :=
    mul_le_mul_of_nonneg_right h_phi_le (by positivity)
  linarith

/-! ## Step 3: Residual perturbation bound and Step 4 polynomial tail bounds -/

theorem rct_d_geom_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (x₀ : Q) (N : Nat)
    (hx₀ : |x₀.val| ≤ 1 / (8 * (2 : Rat) ^ (sysParams sys).2))
    (u : Nat) (hu : u < sys.length) (n : Nat) :
    |(rctShift x₀.val N (rctTrunc N (solFast sys u)) n).val| ≤
      (2 * (2 : Rat) ^ (sysParams sys).1) * (8 * (2 : Rat) ^ (sysParams sys).2) ^ n := by
  let K₀ : Rat := (2 : Rat) ^ (sysParams sys).1
  let B₀ : Rat := (2 : Rat) ^ (sysParams sys).2
  have hB₀_ge_4 := rct_sysParams_B_ge_four sys
  have hB₀_pos : (0 : Rat) < B₀ := by linarith
  have h_bd : ∀ m, 0 ≤ m → |(rctTrunc N (solFast sys u) m).val| ≤ K₀ * B₀ ^ m := by
    intro m _
    have hw := rct_trunc_solFast_weighted_bound sys h N u hu m
    exact le_trans hw (div_le_self (by positivity) (sbdSq_ge_one m))
  have h1 := rctShift_geom_bound x₀.val N 0 (rctTrunc N (solFast sys u))
    (by positivity) hB₀_pos hx₀ (fun _ hm ↦ absurd hm (Nat.not_lt_zero _)) h_bd n
  rw [pow_zero, mul_one] at h1
  exact h1

theorem rct_d_weighted_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (x₀ : Q) (N : Nat)
    (hx₀ : |x₀.val| ≤ 1 / (8 * (2 : Rat) ^ (sysParams sys).2))
    {B : Rat} (hB_32 : 32 * (2 : Rat) ^ (sysParams sys).2 ≤ B)
    (u : Nat) (hu : u < sys.length) (n : Nat) :
    |(rctShift x₀.val N (rctTrunc N (solFast sys u)) n).val| ≤
      (2 * (2 : Rat) ^ (sysParams sys).1) * B ^ n / sbdSq n := by
  let K₀ : Rat := (2 : Rat) ^ (sysParams sys).1
  let B₀ : Rat := (2 : Rat) ^ (sysParams sys).2
  have hB₀_ge_4 := rct_sysParams_B_ge_four sys
  have hB₀_pos : (0 : Rat) < B₀ := by linarith
  have h_bd : ∀ m, 0 ≤ m → |(rctTrunc N (solFast sys u) m).val| ≤ K₀ * B₀ ^ m := by
    intro m _
    have hw := rct_trunc_solFast_weighted_bound sys h N u hu m
    exact le_trans hw (div_le_self (by positivity) (sbdSq_ge_one m))
  have h1 := rctShift_weighted_bound x₀.val N 0 (rctTrunc N (solFast sys u))
    (by positivity) hB₀_pos hx₀ (fun _ hm ↦ absurd hm (Nat.not_lt_zero _)) h_bd n
  rw [pow_zero, mul_one] at h1
  have hpow : (32 * B₀) ^ n ≤ B ^ n := pow_le_pow_left₀ (by positivity) hB_32 n
  have h2 : (2 * K₀) * (32 * B₀) ^ n / sbdSq n ≤ (2 * K₀) * B ^ n / sbdSq n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
      (le_of_lt (sbdSq_pos n))
  exact le_trans h1 h2

/-- Weighted majorant bound for any coefficient table `z` satisfying the ODE recurrence. -/
theorem rct_z_weighted_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (z : Nat → Nat → Q) {K B : Rat} (hK : 0 ≤ K) (hB : 4 ≤ B)
    (hz_init : ∀ v < sys.length, |(z v 0).val| ≤ K)
    (hz_succ : ∀ v (hv : v < sys.length) (k : Nat),
      (z v (k + 1)).val = (sbdEvalExpr sys[v].2 z k).val / ((k + 1 : Nat) : Rat))
    (hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 K ≤ K * B) :
    ∀ n : Nat, ∀ v < sys.length, |(z v n).val| ≤ K * B ^ n / sbdSq n := by
  have hB0 : (0 : Rat) ≤ B := by linarith
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hpv := h sys[v] (List.getElem_mem hv)
    cases m with
    | zero =>
      have hsq0 : sbdSq 0 = 1 := by unfold sbdSq; norm_num
      rw [hsq0, pow_zero, mul_one, div_one]
      exact hz_init v hv
    | succ k =>
      rw [hz_succ v hv k]
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      rw [abs_div, abs_of_pos hk1_pos]
      have h_div_le : |(sbdEvalExpr sys[v].2 z k).val| / ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr sys[v].2 z k).val| :=
        div_le_self (abs_nonneg _) hk1_ge
      have h_expr := sbd_evalExpr_bound sys[v].2 sys.length hpv.1 hpv.2.2 z hK hB k
        (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu) k (le_refl k)
      have hΦ : 0 ≤ sbdExprBound sys[v].2 K := sbdExprBound_nonneg sys[v].2 hK
      have h_scale := sbd_step_scale hΦ hB0 (hStep sys[v] (List.getElem_mem hv)) k
      linarith

/-- **Step 3: Residual perturbation bound** between `z` and `d := fun u ↦ rctShift x₀.val N (rctTrunc N (solFast sys u))`. -/
theorem rct_z_diff_weighted_bound (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (hflat : ∀ p ∈ sys, p.2.NoInteg) (z : Nat → Nat → Q) (x₀ : Q) {N : Nat} (hN : 1 ≤ N)
    (hx₀ : |x₀.val| ≤ 1 / (8 * (2 : Rat) ^ (sysParams sys).2))
    {B : Rat} (hB_32 : 32 * (2 : Rat) ^ (sysParams sys).2 ≤ B)
    (hStep : ∀ p ∈ sys,
      4 * sbdExprBound p.2 (2 * (2 : Rat) ^ (sysParams sys).1) ≤
        (2 * (2 : Rat) ^ (sysParams sys).1) * B)
    (hDiffStep : ∀ p ∈ sys,
      4 * (sptDiffBound p.2 (2 * (2 : Rat) ^ (sysParams sys).1) 1 + 1) ≤ B)
    (hz_zero : ∀ v < sys.length, (z v 0).val = (Jet.evalPoly ⟨solFast sys v⟩ N x₀).val)
    (hz_succ : ∀ v (hv : v < sys.length) (k : Nat),
      (z v (k + 1)).val = (sbdEvalExpr sys[v].2 z k).val / ((k + 1 : Nat) : Rat)) :
    ∀ n : Nat, ∀ v < sys.length,
      |(z v n).val - (rctShift x₀.val N (rctTrunc N (solFast sys v)) n).val| ≤
        (2 * ((2 : Rat) ^ (sysParams sys).1 * (2 : Rat) ^ (sysParams sys).2) *
          (1 / 2 : Rat) ^ (N - 1)) * 1 * B ^ n / sbdSq n := by
  let K₀ : Rat := (2 : Rat) ^ (sysParams sys).1
  let B₀ : Rat := (2 : Rat) ^ (sysParams sys).2
  let K : Rat := 2 * K₀
  let δ : Rat := 2 * (K₀ * B₀) * (1 / 2 : Rat) ^ (N - 1)
  let p : Nat → Nat → Q := fun u ↦ rctTrunc N (solFast sys u)
  let d : Nat → Nat → Q := fun u ↦ rctShift x₀.val N (p u)
  have hB₀_ge_4 := rct_sysParams_B_ge_four sys
  have hB_ge_4 : (4 : Rat) ≤ B := by linarith
  have hB0 : (0 : Rat) ≤ B := by linarith
  have hK_nonneg : (0 : Rat) ≤ K := by positivity
  have hδ_nonneg : (0 : Rat) ≤ δ := by positivity
  have hd_zero_eq : ∀ v < sys.length, (z v 0).val = (d v 0).val := by
    intro v hv
    dsimp [d, p]
    rw [rctShift_zero_deg x₀ N (rctTrunc N (solFast sys v)),
        rct_evalPoly_trunc_eq N (solFast sys v) x₀, hz_zero v hv]
  have hz_init : ∀ v < sys.length, |(z v 0).val| ≤ K := by
    intro v hv
    rw [hd_zero_eq v hv]
    have hd0 := rct_d_geom_bound sys h x₀ N hx₀ v hv 0
    rw [pow_zero, mul_one] at hd0
    exact hd0
  have hW_z := rct_z_weighted_bound sys h z hK_nonneg hB_ge_4 hz_init hz_succ hStep
  have hW_d : ∀ n : Nat, ∀ u < sys.length, |(d u n).val| ≤ K * B ^ n / sbdSq n :=
    fun n u hu ↦ rct_d_weighted_bound sys h x₀ N hx₀ hB_32 u hu n
  intro n
  induction n using Nat.strongRecOn with
  | ind m ih =>
    intro v hv
    have hpv := h sys[v] (List.getElem_mem hv)
    cases m with
    | zero =>
      change |(z v 0).val - (d v 0).val| ≤ δ * 1 * B ^ 0 / sbdSq 0
      rw [hd_zero_eq v hv, sub_self, abs_zero]
      have hsq0 : (0 : Rat) < sbdSq 0 := sbdSq_pos 0
      positivity
    | succ k =>
      change |(z v (k + 1)).val - (d v (k + 1)).val| ≤ δ * 1 * B ^ (k + 1) / sbdSq (k + 1)
      let D := rctExprDeg sys[v].2 N
      have h_rec := rct_shift_recurrence sys[v].2 sys.length hpv.1 hpv.2.2
        (hflat sys[v] (List.getElem_mem hv)) p x₀.val hN (le_refl D)
        (fun u _ ↦ rctSuppAt_trunc N (solFast sys u)) v hv k
      have hk1_ge : (1 : Rat) ≤ ((k + 1 : Nat) : Rat) := by
        exact_mod_cast Nat.succ_pos k
      have hk1_pos : (0 : Rat) < ((k + 1 : Nat) : Rat) := by positivity
      have hk1_ne : ((k + 1 : Nat) : Rat) ≠ 0 := ne_of_gt hk1_pos
      have hd_succ : (d v (k + 1)).val =
          ((sbdEvalExpr sys[v].2 d k).val +
            (rctShift x₀.val D (rctResidual sys[v].2 p v) k).val) / ((k + 1 : Nat) : Rat) := by
        rw [eq_div_iff hk1_ne]
        linarith
      rw [hz_succ v hv k, hd_succ, ← sub_div, abs_div, abs_of_pos hk1_pos]
      have h_div_le :
          |(sbdEvalExpr sys[v].2 z k).val -
            ((sbdEvalExpr sys[v].2 d k).val +
              (rctShift x₀.val D (rctResidual sys[v].2 p v) k).val)| /
            ((k + 1 : Nat) : Rat) ≤
          |(sbdEvalExpr sys[v].2 z k).val -
            ((sbdEvalExpr sys[v].2 d k).val +
              (rctShift x₀.val D (rctResidual sys[v].2 p v) k).val)| :=
        div_le_self (abs_nonneg _) hk1_ge
      have h_split :
          (sbdEvalExpr sys[v].2 z k).val -
            ((sbdEvalExpr sys[v].2 d k).val +
              (rctShift x₀.val D (rctResidual sys[v].2 p v) k).val) =
          ((sbdEvalExpr sys[v].2 z k).val - (sbdEvalExpr sys[v].2 d k).val) -
            (rctShift x₀.val D (rctResidual sys[v].2 p v) k).val := by ring
      have h_tri :
          |(sbdEvalExpr sys[v].2 z k).val -
            ((sbdEvalExpr sys[v].2 d k).val +
              (rctShift x₀.val D (rctResidual sys[v].2 p v) k).val)| ≤
          |(sbdEvalExpr sys[v].2 z k).val - (sbdEvalExpr sys[v].2 d k).val| +
            |(rctShift x₀.val D (rctResidual sys[v].2 p v) k).val| := by
        rw [h_split]
        exact abs_sub _ _
      have h_expr := spt_evalExpr_diff_bound sys[v].2 sys.length hpv.1 hpv.2.2
        z d hK_nonneg (by norm_num) hδ_nonneg hB_ge_4 k
        (fun u hu j _ ↦ hW_z j u hu)
        (fun u hu j _ ↦ hW_d j u hu)
        (fun u hu j hj ↦ ih j (Nat.lt_succ_of_le hj) u hu)
        k (le_refl k)
      have h_res_32 := rctShift_weighted_bound x₀.val D (N - 1) (rctResidual sys[v].2 p v)
        (show 0 ≤ K₀ * B₀ by positivity) (show 0 < B₀ by linarith) hx₀
        (rct_residual_zero_lt sys h N v hv)
        (rct_residual_bound_ge sys h N v hv) k
      have hpow_k : (32 * B₀) ^ k ≤ B ^ k := pow_le_pow_left₀ (by positivity) hB_32 k
      have h_res_B : δ * (32 * B₀) ^ k / sbdSq k ≤ δ * B ^ k / sbdSq k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow_k hδ_nonneg)
          (le_of_lt (sbdSq_pos k))
      have h_res : |(rctShift x₀.val D (rctResidual sys[v].2 p v) k).val| ≤ δ * B ^ k / sbdSq k :=
        le_trans h_res_32 h_res_B
      have h_comb :
          δ * sptDiffBound sys[v].2 K 1 * B ^ k / sbdSq k + δ * B ^ k / sbdSq k =
          (δ * (sptDiffBound sys[v].2 K 1 + 1)) * B ^ k / sbdSq k := by ring
      have hΨ_nonneg : (0 : Rat) ≤ δ * (sptDiffBound sys[v].2 K 1 + 1) := by
        have := sptDiffBound_nonneg sys[v].2 hK_nonneg (show (0 : Rat) ≤ 1 by norm_num)
        positivity
      have h4Ψ : 4 * (δ * (sptDiffBound sys[v].2 K 1 + 1)) ≤ (δ * 1) * B := by
        have hstep_v := mul_le_mul_of_nonneg_left (hDiffStep sys[v] (List.getElem_mem hv)) hδ_nonneg
        linarith
      have h_scale := sbd_step_scale hΨ_nonneg hB0 h4Ψ k
      linarith

/-- Unified bound on the difference of `evalPoly` for two jets `f, g` agreeing below `M₀`
    and differing by at most `C * B^n` from `M₀` onwards, for `|x| ≤ 1 / (4 * B)`. -/
theorem rct_evalPoly_diff_bound (f g : Nat → Q) (L M₀ : Nat) (x : Q) {C B : Rat}
    (hC : 0 ≤ C) (hB : 0 < B) (hx : |x.val| ≤ 1 / (4 * B))
    (h_eq : ∀ n < M₀, (f n).val = (g n).val)
    (h_bd : ∀ n, M₀ ≤ n → |(f n).val - (g n).val| ≤ C * B ^ n) :
    |(Jet.evalPoly ⟨f⟩ L x).val - (Jet.evalPoly ⟨g⟩ L x).val| ≤
      2 * C * (1 / 2 : Rat) ^ M₀ := by
  rw [rct_evalPoly_val_eq_sum, rct_evalPoly_val_eq_sum, ← Finset.sum_sub_distrib]
  have h_abs :
      |∑ n ∈ Finset.range L, ((f n).val * x.val ^ n - (g n).val * x.val ^ n)| ≤
      ∑ n ∈ Finset.range L, |(f n).val * x.val ^ n - (g n).val * x.val ^ n| :=
    Finset.abs_sum_le_sum_abs _ _
  have h_terms :
      (∑ n ∈ Finset.range L, |(f n).val * x.val ^ n - (g n).val * x.val ^ n|) ≤
      ∑ n ∈ Finset.range L, (C * (1 / 2 : Rat) ^ M₀) * (1 / 2 : Rat) ^ n := by
    refine Finset.sum_le_sum fun n _ ↦ ?_
    rw [← sub_mul]
    by_cases hnM : n < M₀
    · rw [h_eq n hnM, sub_self, zero_mul, abs_zero]
      positivity
    · have hMn : M₀ ≤ n := not_lt.mp hnM
      rw [abs_mul, abs_pow]
      have h1 : |(f n).val - (g n).val| * |x.val| ^ n ≤ (C * B ^ n) * |x.val| ^ n :=
        mul_le_mul_of_nonneg_right (h_bd n hMn) (by positivity)
      have h4Bx : 4 * B * |x.val| ≤ 1 := by
        have h4B_pos : (0 : Rat) < 4 * B := by positivity
        have hmul := mul_le_mul_of_nonneg_left hx (le_of_lt h4B_pos)
        rw [mul_one_div_cancel (ne_of_gt h4B_pos)] at hmul
        exact hmul
      have h4Bx_pow : (4 * B * |x.val|) ^ n ≤ 1 :=
        pow_le_one₀ (by positivity) h4Bx
      have h_id : B ^ n * |x.val| ^ n =
          (1 / 2 : Rat) ^ n * (1 / 2 : Rat) ^ n * (4 * B * |x.val|) ^ n := by
        rw [← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        ring
      have h2 : (C * B ^ n) * |x.val| ^ n ≤ C * (1 / 2 : Rat) ^ n * (1 / 2 : Rat) ^ n := by
        have h_eq' : (C * B ^ n) * |x.val| ^ n =
            (C * (1 / 2 : Rat) ^ n * (1 / 2 : Rat) ^ n) * (4 * B * |x.val|) ^ n := by
          calc (C * B ^ n) * |x.val| ^ n = C * (B ^ n * |x.val| ^ n) := by ring
            _ = (C * (1 / 2 : Rat) ^ n * (1 / 2 : Rat) ^ n) * (4 * B * |x.val|) ^ n := by
              rw [h_id]; ring
        rw [h_eq']
        have h_pos : (0 : Rat) ≤ C * (1 / 2 : Rat) ^ n * (1 / 2 : Rat) ^ n := by positivity
        nlinarith
      have h_anti : (1 / 2 : Rat) ^ n ≤ (1 / 2 : Rat) ^ M₀ := rct_half_pow_anti hMn
      have h3 : C * (1 / 2 : Rat) ^ n * (1 / 2 : Rat) ^ n ≤
          (C * (1 / 2 : Rat) ^ M₀) * (1 / 2 : Rat) ^ n := by
        have h_pos : (0 : Rat) ≤ C * (1 / 2 : Rat) ^ n := by positivity
        nlinarith
      linarith
  rw [← Finset.mul_sum] at h_terms
  have h_sum := mul_le_mul_of_nonneg_left (rct_sum_half_pow_le_two L)
    (show (0 : Rat) ≤ C * (1 / 2 : Rat) ^ M₀ by positivity)
  linarith

/-- Tail bound between `evalPoly ⟨f⟩ L x` and `evalPoly ⟨f⟩ M₀ x` for `M₀ ≤ L` and `|x| ≤ 1 / (4 * B)`. -/
theorem rct_evalPoly_tail_bound (f : Nat → Q) {M₀ L : Nat} (hML : M₀ ≤ L) (x : Q) {C B : Rat}
    (hC : 0 ≤ C) (hB : 0 < B) (hx : |x.val| ≤ 1 / (4 * B))
    (h_bd : ∀ n, M₀ ≤ n → |(f n).val| ≤ C * B ^ n) :
    |(Jet.evalPoly ⟨f⟩ L x).val - (Jet.evalPoly ⟨f⟩ M₀ x).val| ≤
      2 * C * (1 / 2 : Rat) ^ M₀ := by
  rw [← rct_evalPoly_trunc_eq M₀ f x,
      ← rct_evalPoly_eq_of_supp hML (rctTrunc M₀ f) (rctSuppAt_trunc M₀ f) x]
  refine rct_evalPoly_diff_bound f (rctTrunc M₀ f) L M₀ x hC hB hx
    (fun n hn ↦ by rw [rctTrunc_lt hn]) (fun n hn ↦ ?_)
  rw [rctTrunc_ge hn, Q.val_zero, sub_zero]
  exact h_bd n hn

theorem rct_abs_chain (zL dL cN cM cL : Rat) :
    |zL - cL| ≤ |zL - dL| + |cN - dL| + |cM - cN| + |cM - cL| := by
  have h : zL - cL = ((zL - dL) - (cN - dL)) + ((cM - cL) - (cM - cN)) := by ring
  rw [h]
  have h1 := abs_add_le ((zL - dL) - (cN - dL)) ((cM - cL) - (cM - cN))
  have h2 := abs_sub (zL - dL) (cN - dL)
  have h3 := abs_sub (cM - cL) (cM - cN)
  linarith

theorem rct_abs_chain_le {zL dL cN cM cL A : Rat}
    (h1 : |zL - dL| ≤ 4 * A) (h2 : |cN - dL| ≤ 4 * A)
    (h3 : |cM - cN| ≤ 2 * A) (h4 : |cM - cL| ≤ 2 * A) :
    |zL - cL| ≤ 12 * A := by
  have hc := rct_abs_chain zL dL cN cM cL
  linarith

theorem rct_twelve_half_pow_lt {A ε : Rat} {M_eps : Nat}
    (hε : 0 < ε) (hM_eps : (12 * A + 1) / ε ≤ (2 : Rat) ^ M_eps) :
    12 * (A * (1 / 2 : Rat) ^ M_eps) < ε := by
  have h_eps_mul : 12 * A + 1 ≤ (2 : Rat) ^ M_eps * ε :=
    (div_le_iff₀ hε).mp hM_eps
  have h_eps_strict : 12 * A < (2 : Rat) ^ M_eps * ε := by linarith
  have h_half_pos : (0 : Rat) < (1 / 2 : Rat) ^ M_eps := by positivity
  have h_mul_lt := mul_lt_mul_of_pos_right h_eps_strict h_half_pos
  have h_cancel : (2 : Rat) ^ M_eps * (1 / 2 : Rat) ^ M_eps = 1 := by
    rw [← mul_pow]
    norm_num
  have h_two_half : ((2 : Rat) ^ M_eps * ε) * (1 / 2 : Rat) ^ M_eps = ε := by
    calc ((2 : Rat) ^ M_eps * ε) * (1 / 2 : Rat) ^ M_eps
        = ε * ((2 : Rat) ^ M_eps * (1 / 2 : Rat) ^ M_eps) := by ring
      _ = ε := by rw [h_cancel, mul_one]
  linarith

theorem rct_scale_delta {X K₀ B₀ : Rat} {a b : Nat} (hK₀ : 0 ≤ K₀) (hB₀ : 0 ≤ B₀)
    (hab : b ≤ a) (hX : X ≤ 2 * (2 * (K₀ * B₀) * (1 / 2 : Rat) ^ a)) :
    X ≤ 4 * (K₀ * B₀ * (1 / 2 : Rat) ^ b) := by
  have h_anti := rct_half_pow_anti hab
  have h1 := mul_le_mul_of_nonneg_left h_anti (show (0 : Rat) ≤ 4 * (K₀ * B₀) by positivity)
  linarith

theorem rct_scale_half_pow {X K₀ B₀ : Rat} {a b : Nat} (hK₀ : 0 ≤ K₀) (hB₀ : 1 ≤ B₀)
    (hab : b ≤ a) (hX : X ≤ 2 * (2 * K₀) * (1 / 2 : Rat) ^ a) :
    X ≤ 4 * (K₀ * B₀ * (1 / 2 : Rat) ^ b) := by
  have h_anti := rct_half_pow_anti hab
  have h1 : (1 / 2 : Rat) ^ a ≤ B₀ * (1 / 2 : Rat) ^ b := by
    have : (0 : Rat) ≤ (1 / 2 : Rat) ^ b := by positivity
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : Rat) ≤ 4 * K₀ by positivity)
  linarith

theorem rct_scale_half_pow_two {X K₀ B₀ : Rat} {a b : Nat} (hK₀ : 0 ≤ K₀) (hB₀ : 1 ≤ B₀)
    (hab : b ≤ a) (hX : X ≤ 2 * K₀ * (1 / 2 : Rat) ^ a) :
    X ≤ 2 * (K₀ * B₀ * (1 / 2 : Rat) ^ b) := by
  have h_anti := rct_half_pow_anti hab
  have h1 : (1 / 2 : Rat) ^ a ≤ B₀ * (1 / 2 : Rat) ^ b := by
    have : (0 : Rat) ≤ (1 / 2 : Rat) ^ b := by positivity
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : Rat) ≤ 2 * K₀ by positivity)
  linarith

/-- **Step 4: Main assembly of `recenter_overlap` for any table `z x₀ N`** satisfying the
    re-centered initial condition and ODE recurrence. -/
theorem rct_overlap_of_table (sys : List (Tm [] JetTy × JExprN)) (h : GPACSys sys)
    (hflat : ∀ p ∈ sys, p.2.NoInteg)
    (z : Q → Nat → Nat → Nat → Q)
    (hz_zero : ∀ (x₀ : Q) (N v : Nat), v < sys.length →
      (z x₀ N v 0).val = (Jet.evalPoly ⟨solFast sys v⟩ N x₀).val)
    (hz_succ : ∀ (x₀ : Q) (N v : Nat) (hv : v < sys.length) (k : Nat),
      (z x₀ N v (k + 1)).val = (sbdEvalExpr sys[v].2 (z x₀ N) k).val / ((k + 1 : Nat) : Rat)) :
    ∃ R : Nat, ∀ x₀ t : Q,
      |x₀.val| ≤ 1 / (2 : Rat) ^ (R + 2) → |t.val| ≤ 1 / (2 : Rat) ^ (R + 2) →
      ∀ ε : Rat, 0 < ε → ∃ N₀ : Nat, ∀ N L : Nat, N₀ ≤ N → N₀ ≤ L →
        ∀ v, v < sys.length →
          |(Jet.evalPoly ⟨z x₀ N v⟩ L t).val
            - (Jet.evalPoly ⟨solFast sys v⟩ L (Q.add x₀ t)).val| < ε := by
  let K₀ : Rat := (2 : Rat) ^ (sysParams sys).1
  let B₀ : Rat := (2 : Rat) ^ (sysParams sys).2
  let K : Rat := 2 * K₀
  have hK₀_nonneg : (0 : Rat) ≤ K₀ := by positivity
  have hB₀_ge_4 : (4 : Rat) ≤ B₀ := rct_sysParams_B_ge_four sys
  have hB₀_ge_1 : (1 : Rat) ≤ B₀ := by linarith
  have hB₀_pos : (0 : Rat) < B₀ := by linarith
  have hK_pos : (0 : Rat) < K := by positivity
  rcases sbd_exists_two_pow_ge
    (max (32 * B₀) (max (4 * sbdMaxPhi K sys / K) (4 * (sptMaxPsi K 1 (sys.map Prod.snd) + 1))))
    with ⟨R, hR⟩
  let B : Rat := (2 : Rat) ^ R
  have hB_32 : 32 * B₀ ≤ B := le_trans (le_max_left _ _) hR
  have hB_pos : (0 : Rat) < B := by linarith
  have hR_right : max (4 * sbdMaxPhi K sys / K) (4 * (sptMaxPsi K 1 (sys.map Prod.snd) + 1)) ≤ B :=
    le_trans (le_max_right _ _) hR
  have hStep : ∀ p ∈ sys, 4 * sbdExprBound p.2 K ≤ K * B := by
    intro p hp
    have h1 := sbdMaxPhi_mem K hp
    have h2 : 4 * sbdMaxPhi K sys / K ≤ B := le_trans (le_max_left _ _) hR_right
    have h3 : 4 * sbdMaxPhi K sys ≤ B * K := (div_le_iff₀ hK_pos).mp h2
    linarith
  have hDiffStep : ∀ p ∈ sys, 4 * (sptDiffBound p.2 K 1 + 1) ≤ B := by
    intro p hp
    have hpF : p.2 ∈ sys.map Prod.snd := List.mem_map_of_mem hp
    have h1 := sptMaxPsi_mem K 1 hpF
    have h2 : 4 * (sptMaxPsi K 1 (sys.map Prod.snd) + 1) ≤ B := le_trans (le_max_right _ _) hR_right
    linarith
  refine ⟨R, fun x₀ t hx₀_in ht_in ε hε ↦ ?_⟩
  have hpow_R2 : (2 : Rat) ^ (R + 2) = 4 * B := by
    change (2 : Rat) ^ (R + 2) = 4 * (2 : Rat) ^ R
    rw [pow_add]
    ring
  have hx₀_4B : |x₀.val| ≤ 1 / (4 * B) := by rwa [hpow_R2] at hx₀_in
  have ht_4B : |t.val| ≤ 1 / (4 * B) := by rwa [hpow_R2] at ht_in
  have hx₀_8B₀ : |x₀.val| ≤ 1 / (8 * B₀) :=
    le_trans hx₀_4B (one_div_le_one_div_of_le (by positivity) (by linarith))
  have ht_32B₀ : |t.val| ≤ 1 / (4 * (8 * B₀)) :=
    le_trans ht_4B (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hxt_4B₀ : |(Q.add x₀ t).val| ≤ 1 / (4 * B₀) := by
    rw [Q.val_add]
    have h_sum : |x₀.val + t.val| ≤ 1 / (2 * B) := by
      have h_tri := abs_add_le x₀.val t.val
      have h_eq : 1 / (4 * B) + 1 / (4 * B) = 1 / (2 * B) := by ring
      linarith
    exact le_trans h_sum (one_div_le_one_div_of_le (by positivity) (by linarith))
  rcases sbd_exists_two_pow_ge ((12 * (K₀ * B₀) + 1) / ε) with ⟨M_eps, hM_eps⟩
  refine ⟨M_eps + 1, fun N L hN₀N hN₀L v hv ↦ ?_⟩
  have hN1 : 1 ≤ N := by omega
  let d : Nat → Q := rctShift x₀.val N (rctTrunc N (solFast sys v))
  let δ : Rat := 2 * (K₀ * B₀) * (1 / 2 : Rat) ^ (N - 1)
  have h_term1 : |(Jet.evalPoly ⟨z x₀ N v⟩ L t).val - (Jet.evalPoly ⟨d⟩ L t).val| ≤
      4 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_z_d_coeff : ∀ n, 0 ≤ n → |(z x₀ N v n).val - (d n).val| ≤ δ * B ^ n := by
      intro n _
      have hw := rct_z_diff_weighted_bound sys h hflat (z x₀ N) x₀ hN1 hx₀_8B₀
        hB_32 hStep hDiffStep (hz_zero x₀ N) (hz_succ x₀ N) n v hv
      have hdrop : δ * 1 * B ^ n / sbdSq n ≤ δ * B ^ n := by
        rw [mul_one]
        exact div_le_self (by positivity) (sbdSq_ge_one n)
      exact le_trans hw hdrop
    have h_raw := rct_evalPoly_diff_bound (z x₀ N v) d L 0 t
      (by positivity) hB_pos ht_4B (fun _ hn ↦ absurd hn (Nat.not_lt_zero _)) h_z_d_coeff
    rw [pow_zero, mul_one] at h_raw
    exact rct_scale_delta hK₀_nonneg (le_of_lt hB₀_pos) (by omega) h_raw
  have h_term2 :
      |(Jet.evalPoly ⟨solFast sys v⟩ N (Q.add x₀ t)).val - (Jet.evalPoly ⟨d⟩ L t).val| ≤
      4 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_raw := rct_evalPoly_tail_bound d (le_max_right N L) t
      (by positivity) (by positivity) ht_32B₀
      (fun n _ ↦ rct_d_geom_bound sys h x₀ N hx₀_8B₀ v hv n)
    have h_shift_id :
        (Jet.evalPoly ⟨d⟩ (max N L) t).val =
          (Jet.evalPoly ⟨solFast sys v⟩ N (Q.add x₀ t)).val := by
      dsimp [d]
      rw [rct_evalPoly_shift x₀ t N (max N L) (le_max_left N L) (rctTrunc N (solFast sys v)),
          rct_evalPoly_trunc_eq N (solFast sys v) (Q.add x₀ t)]
    rw [h_shift_id] at h_raw
    exact rct_scale_half_pow hK₀_nonneg hB₀_ge_1 (by omega) h_raw
  have h_c_bd : ∀ n : Nat, |(solFast sys v n).val| ≤ K₀ * B₀ ^ n := by
    intro n
    exact le_trans (rct_solFast_weighted_bound sys h v hv n)
      (div_le_self (by positivity) (sbdSq_ge_one n))
  have h_term3 :
      |(Jet.evalPoly ⟨solFast sys v⟩ (max N L) (Q.add x₀ t)).val -
        (Jet.evalPoly ⟨solFast sys v⟩ N (Q.add x₀ t)).val| ≤
      2 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_raw := rct_evalPoly_tail_bound (solFast sys v) (le_max_left N L) (Q.add x₀ t)
      hK₀_nonneg hB₀_pos hxt_4B₀ (fun n _ ↦ h_c_bd n)
    exact rct_scale_half_pow_two hK₀_nonneg hB₀_ge_1 (by omega) h_raw
  have h_term4 :
      |(Jet.evalPoly ⟨solFast sys v⟩ (max N L) (Q.add x₀ t)).val -
        (Jet.evalPoly ⟨solFast sys v⟩ L (Q.add x₀ t)).val| ≤
      2 * (K₀ * B₀ * (1 / 2 : Rat) ^ M_eps) := by
    have h_raw := rct_evalPoly_tail_bound (solFast sys v) (le_max_right N L) (Q.add x₀ t)
      hK₀_nonneg hB₀_pos hxt_4B₀ (fun n _ ↦ h_c_bd n)
    exact rct_scale_half_pow_two hK₀_nonneg hB₀_ge_1 (by omega) h_raw
  exact lt_of_le_of_lt
    (rct_abs_chain_le h_term1 h_term2 h_term3 h_term4)
    (rct_twelve_half_pow_lt hε hM_eps)

end HAomega
