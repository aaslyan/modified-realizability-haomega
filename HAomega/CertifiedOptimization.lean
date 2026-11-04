/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ComputationalAdequacy

/-!
# Certified Normalization, Representation Compression, and ODE Tower Optimization

This module establishes the fourth pillar of computational adequacy in $\mathsf{HA}^\omega$:
**mathematical identities translate into certified computational simplifications without losing
correctness or convergence certificates**.

We maintain a strict separation between four distinct concepts:
1. **Normalization (`UExpr.normalize`)**:
   A constructive, structurally terminating, bottom-up syntax-directed rewriter on `UExpr`
   that eliminates stacked calculus and algebraic inverse pairs (`deriv (integ e) ⟶ e`,
   `inv (inv e) ⟶ e`, `comp e .x ⟶ e`, `comp (.const q) b ⟶ .const q`,
   `deriv (.const q) ⟶ 0`, `deriv .x ⟶ 1`, `deriv .exp ⟶ .exp`, `deriv .sin ⟶ .cos`, and
   additive/multiplicative neutral elements), proved to:
   - preserve definedness (`UExpr.Defined.normalize`),
   - preserve exact rational Taylor coefficients (`UExpr.normalize_eval_eq`) and infinite real
     power-series values (`UExpr.normalize_analyticValue_eq`),
   - never increase AST size (`UExpr.normalize_astSize_le`),
   - reach an idempotent normal form in one bottom-up pass (`UExpr.normalize_idempotent`),
     collapsing arbitrarily deep towers (`iterDerivInteg`, `iterCompX`, `iterInvPair`).
2. **Representation Compression (`PolyODEProof.SemEq`, `PolyODEProof.compress_of_coeff_eq`)**:
   Replacing a bloated ODE representation $P_1$ by a semantically equivalent representation $P_2$
   ($\forall n,\; c_{P_1}(n) = c_{P_2}(n)$), carefully distinguishing:
   - **Common-disk evaluation**: on $|x| \le \min(2^{-(R_1+1)}, 2^{-(R_2+1)})$, evaluating $P_2$
     via `GPACSys.approxFast` directly certifies $P_1.\operatorname{analyticValue}(x)$ within $2^{-k}$;
   - **Certified analytic continuation**: when $R_2 \le R_1$, $P_2.\operatorname{analyticValue}$
     agrees with $P_1.\operatorname{analyticValue}$ on $P_1$'s disk and extends certified $2^{-k}$
     evaluation to the larger disk $|x| \le 2^{-(R_2+1)}$.
3. **Certified Cost-Guided Optimization (`PolyODEProof.BetterRep`, `PolyODEProof.selectBetter`, `UExpr.optimizeToPolyODEProof`)**:
   An explicit multi-parameter representation quality preorder (`BetterRep P₂ P₁` comparing ODE state
   dimension `sys.length`, majorant exponent $M$, and radius exponent $R$) together with a
   verified candidate selector `selectBetter` that accepts a semantically equivalent candidate $P_2$
   if and only if it improves or preserves the certified cost.
4. **Autonomous-Inverse Tower Compression (`UExpr.autoInverse_comp_compress_to_varX`)**:
   Demonstrates that composing the compiled ODE of $\operatorname{autoInverse}(F)$ with a 1D
   autonomous ODE solution $Y$ is semantically equivalent (`SemEq`) to the 1-state identity ODE
   `PolyODEProof.varX` and compresses to it whenever `BetterRep` holds.
-/

namespace HAomega

open Rat

deriving instance DecidableEq for UExpr

/-! ## Section 1: Jet Composition Congruence & Identity Lemmas -/

/-- `mulShift` respects value equality in its first argument `G`. -/
theorem mulShift_congr_left_val (G G' A : Jet)
    (hG : ∀ m, (G.coeff m).val = (G'.coeff m).val) (n : Nat) :
    ((mulShift G A).coeff n).val = ((mulShift G' A).coeff n).val := by
  cases n with
  | zero => rfl
  | succ k =>
    dsimp [mulShift]
    rw [TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp [Jet.shift]
    rw [hG (j + 1)]

/-- `hPow G r` respects value equality in `G`. -/
theorem hPow_congr_val (G G' : Jet) (hG : ∀ m, (G.coeff m).val = (G'.coeff m).val) :
    ∀ (r n : Nat), ((hPow G r).coeff n).val = ((hPow G' r).coeff n).val
  | 0, _ => rfl
  | r + 1, n => by
    dsimp [hPow]
    exact (mulShift_congr_left_val G G' (hPow G r) hG n).trans
      (chain_mulShift_congr_val G' (hPow G r) (hPow G' r) (hPow_congr_val G G' hG r) n)

/-- `Jet.compZero F G` respects value equality in both `F` and `G`. -/
theorem compZero_congr_both_val (F F' G G' : Jet)
    (hF : ∀ m, (F.coeff m).val = (F'.coeff m).val)
    (hG : ∀ m, (G.coeff m).val = (G'.coeff m).val) (n : Nat) :
    ((Jet.compZero F G).coeff n).val = ((Jet.compZero F' G').coeff n).val := by
  rw [compZero_coeff_val_eq_sum F G n n (le_refl _),
      compZero_coeff_val_eq_sum F' G' n n (le_refl _)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [hF r, hPow_congr_val G G' hG r n]

/-- Multiplying any jet `A` by `Jet.varX - Jet.varX(0) = x` shifts coefficients by 1 in value. -/
theorem mulShift_varX_coeff_succ_val (A : Jet) (k : Nat) :
    ((mulShift Jet.varX A).coeff (k + 1)).val = (A.coeff k).val := by
  dsimp [mulShift]
  rw [TrigPoly.cauchyConvAux_val, Finset.sum_range_succ']
  have h0 : ∑ j ∈ Finset.range k,
      (Jet.varX.shift.coeff (j + 1)).val * (A.coeff (k - (j + 1))).val = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    change Q.zero.val * _ = 0
    rw [Q.val_zero, zero_mul]
  rw [h0, zero_add, Nat.sub_zero]
  change (Q.ofNat 1).val * (A.coeff k).val = (A.coeff k).val
  rw [Q.val_ofNat]
  ring

/-- The `r`-th formal power of `Jet.varX` has coefficient `1` at `n = r` and `0` otherwise. -/
theorem hPow_varX_coeff_val : ∀ (r n : Nat),
    ((hPow Jet.varX r).coeff n).val = if n = r then 1 else 0
  | 0, 0 => by
    dsimp [hPow]
    rw [Q.val_ofNat]
    norm_num
  | 0, k + 1 => by
    dsimp [hPow]
    rw [Q.val_zero]
  | r + 1, 0 => by
    dsimp [hPow, mulShift]
    rw [Q.val_zero]
  | r + 1, k + 1 => by
    dsimp [hPow]
    rw [mulShift_varX_coeff_succ_val, hPow_varX_coeff_val r k]
    by_cases hkr : k = r
    · subst hkr; simp
    · have hne : k + 1 ≠ r + 1 := by omega
      rw [if_neg hkr, if_neg hne]

/-- **Right Identity of Composition (`compZero_varX_right_val`)**:
    Composing any jet `F` with `Jet.varX` yields `F` at every coefficient in value:
    `((Jet.compZero F Jet.varX).coeff n).val = (F.coeff n).val`. -/
theorem compZero_varX_right_val (F : Jet) (n : Nat) :
    ((Jet.compZero F Jet.varX).coeff n).val = (F.coeff n).val := by
  rw [compZero_coeff_val_eq_sum F Jet.varX n n (le_refl _)]
  rw [Finset.sum_eq_single n]
  · rw [hPow_varX_coeff_val n n, if_pos rfl, mul_one]
  · intro r _ hrn
    rw [hPow_varX_coeff_val r n, if_neg (Ne.symm hrn), mul_zero]
  · intro hnot
    exfalso
    exact hnot (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- **Left Composition with `Jet.varX` (`compZero_varX_left_val`)**:
    Because `Jet.compZero F G` represents $F(G(x) - G(0))$, composing `Jet.varX` on the left
    with `G` yields `G(x) - G(0)`: `0` at $n = 0$ and `(G.coeff n).val` for $n \ge 1$. -/
theorem compZero_varX_left_val (G : Jet) (n : Nat) :
    ((Jet.compZero Jet.varX G).coeff n).val =
      ((G.sub (Jet.const (G.coeff 0))).coeff n).val := by
  cases n with
  | zero =>
    rw [compZero_coeff_val_eq_sum Jet.varX G 0 0 (le_refl _), Finset.sum_range_one]
    change Q.zero.val * ((hPow G 0).coeff 0).val = (Q.sub (G.coeff 0) (G.coeff 0)).val
    rw [Q.val_zero, zero_mul, Q.val_sub, sub_self]
  | succ k =>
    rw [compZero_coeff_val_eq_sum Jet.varX G (k + 1) (k + 1) (le_refl _)]
    rw [Finset.sum_eq_single 1]
    · have h1 : (Jet.varX.coeff 1).val = 1 := by
        change (Q.ofNat 1).val = 1
        rw [Q.val_ofNat]; norm_num
      have hh1 : ((hPow G 1).coeff (k + 1)).val = (G.coeff (k + 1)).val := by
        change (Jet.cauchyConvAux G.shift (hPow G 0) k (k + 1)).val = (G.coeff (k + 1)).val
        rw [TrigPoly.cauchyConvAux_val, Finset.sum_range_succ]
        have h0 : ∑ x ∈ Finset.range k,
            (G.shift.coeff x).val * ((hPow G 0).coeff (k - x)).val = 0 := by
          refine Finset.sum_eq_zero fun x hx ↦ ?_
          rw [Finset.mem_range] at hx
          have hpos : k - x = (k - x - 1) + 1 := by omega
          rw [hpos]
          dsimp [hPow]
          rw [Q.val_zero, mul_zero]
        rw [h0, zero_add, Nat.sub_self]
        dsimp [Jet.shift, hPow]
        rw [Q.val_ofNat]
        ring
      rw [h1, hh1, one_mul]
      change (G.coeff (k + 1)).val = (Q.sub (G.coeff (k + 1)) Q.zero).val
      rw [Q.val_sub, Q.val_zero, sub_zero]
    · intro r _ hr1
      rcases r with _ | _ | m
      · change Q.zero.val * _ = 0
        rw [Q.val_zero, zero_mul]
      · exact absurd rfl hr1
      · change Q.zero.val * _ = 0
        rw [Q.val_zero, zero_mul]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_range]
      omega

/-- **Double Reciprocal Cancellation (`Jet.recip_recip_val`)**:
    Whenever `(f 0).val ≠ 0`, taking `Jet.recip` twice recovers `(f n).val` at every degree $n$. -/
theorem Jet.recip_recip_val (f : Nat → Q) (h0 : (f 0).val ≠ 0) (n : Nat) :
    (Jet.recip (Jet.recip f) n).val = (f n).val := by
  have hr0 : (Jet.recip f 0).val ≠ 0 := by
    change (Q.div (Q.ofNat 1) (f 0)).val ≠ 0
    rw [Q.val_div _ _ (inv_num_ne_zero h0), Q.val_ofNat]
    exact one_div_ne_zero h0
  refine ux_inv_unique_val (Jet.recip f) f hr0 (fun m ↦ ?_) n
  rw [inv_jetMul_comm_val (Jet.recip f) f m]
  exact Jet.recip_spec f h0 m

/-- `Jet.recip` respects coefficientwise `.val` equality. -/
theorem Jet.recip_congr_val (f g : Nat → Q) (hfg : ∀ m, (f m).val = (g m).val)
    (h0 : (f 0).val ≠ 0) (n : Nat) :
    (Jet.recip f n).val = (Jet.recip g n).val := by
  have hg0 : (g 0).val ≠ 0 := by rwa [← hfg 0]
  refine ux_inv_unique_val f (Jet.recip g) h0 (fun m ↦ ?_) n
  have hmul : (((tmJetMul (Γ := [])).eval Env.nil) f (Jet.recip g) m).val =
      (((tmJetMul (Γ := [])).eval Env.nil) g (Jet.recip g) m).val :=
    tmJetMul_agreeV Env.nil Env.nil (m + 1) f g (Jet.recip g) (Jet.recip g)
      (fun i _ ↦ hfg i) (fun _ _ ↦ rfl) m (Nat.lt_succ_self m)
  rw [hmul]
  exact Jet.recip_spec g hg0 m

/-! ## Section 2: Constructive Bottom-Up Normalization (`UExpr.normalize`) -/

/-- Structural AST node count of a `UExpr`. -/
def UExpr.astSize : UExpr → Nat
  | .const _ | .x | .exp | .sin | .cos => 1
  | .inv a | .integ a | .deriv a => a.astSize + 1
  | .add a b | .sub a b | .mul a b | .comp a b => a.astSize + b.astSize + 1

/-- Smart constructor for `UExpr.add`: eliminates syntactic zero constants `.const ⟨0, _⟩`. -/
def UExpr.normAdd : UExpr → UExpr → UExpr
  | a, .const ⟨0, _⟩ => a
  | .const ⟨0, _⟩, b => b
  | a, b => .add a b

/-- Smart constructor for `UExpr.sub`: eliminates syntactic zero on the right `a - 0 ⟶ a`. -/
def UExpr.normSub : UExpr → UExpr → UExpr
  | a, .const ⟨0, _⟩ => a
  | a, b => .sub a b

/-- Smart constructor for `UExpr.mul`: eliminates syntactic unit `.const ⟨1, 0⟩`. -/
def UExpr.normMul : UExpr → UExpr → UExpr
  | a, .const ⟨1, 0⟩ => a
  | .const ⟨1, 0⟩, b => b
  | a, b => .mul a b

/-- Smart constructor for `UExpr.inv`: cancels double reciprocal `inv (inv a) ⟶ a`. -/
def UExpr.normInv : UExpr → UExpr
  | .inv a => a
  | a => .inv a

/-- Smart constructor for `UExpr.deriv`:
    - `deriv (integ a) ⟶ a` (FTC1 cancellation)
    - `deriv (const q) ⟶ const 0`
    - `deriv x ⟶ const 1`
    - `deriv exp ⟶ exp`
    - `deriv sin ⟶ cos` -/
def UExpr.normDeriv : UExpr → UExpr
  | .integ a => a
  | .const _ => .const Q.zero
  | .x => .const (Q.ofNat 1)
  | .exp => .exp
  | .sin => .cos
  | a => .deriv a

/-- Smart constructor for `UExpr.comp`:
    - `comp a x ⟶ a` (right identity of zero-normalized composition)
    - `comp (const q) b ⟶ const q` (left constant absorption) -/
def UExpr.normComp : UExpr → UExpr → UExpr
  | a, .x => a
  | .const q, _ => .const q
  | a, b => .comp a b

/-- **Bottom-Up Normalizer (`UExpr.normalize`)**:
    Recursively normalizes subexpressions and applies the algebraic, differential,
    and compositional cancellation rules at each node. -/
def UExpr.normalize : UExpr → UExpr
  | .const q => .const q
  | .x => .x
  | .exp => .exp
  | .sin => .sin
  | .cos => .cos
  | .add a b => UExpr.normAdd a.normalize b.normalize
  | .sub a b => UExpr.normSub a.normalize b.normalize
  | .mul a b => UExpr.normMul a.normalize b.normalize
  | .inv a => UExpr.normInv a.normalize
  | .integ a => .integ a.normalize
  | .deriv a => UExpr.normDeriv a.normalize
  | .comp a b => UExpr.normComp a.normalize b.normalize

theorem UExpr.normAdd_astSize_le (a b : UExpr) :
    (UExpr.normAdd a b).astSize ≤ a.astSize + b.astSize + 1 := by
  unfold UExpr.normAdd
  split <;> dsimp [UExpr.astSize] <;> omega

theorem UExpr.normSub_astSize_le (a b : UExpr) :
    (UExpr.normSub a b).astSize ≤ a.astSize + b.astSize + 1 := by
  unfold UExpr.normSub
  split <;> dsimp [UExpr.astSize] <;> omega

theorem UExpr.normMul_astSize_le (a b : UExpr) :
    (UExpr.normMul a b).astSize ≤ a.astSize + b.astSize + 1 := by
  unfold UExpr.normMul
  split <;> dsimp [UExpr.astSize] <;> omega

theorem UExpr.normInv_astSize_le (a : UExpr) :
    (UExpr.normInv a).astSize ≤ a.astSize + 1 := by
  unfold UExpr.normInv
  split <;> dsimp [UExpr.astSize] <;> omega

theorem UExpr.normDeriv_astSize_le (a : UExpr) :
    (UExpr.normDeriv a).astSize ≤ a.astSize + 1 := by
  unfold UExpr.normDeriv
  split <;> dsimp [UExpr.astSize] <;> omega

theorem UExpr.normComp_astSize_le (a b : UExpr) :
    (UExpr.normComp a b).astSize ≤ a.astSize + b.astSize + 1 := by
  unfold UExpr.normComp
  split <;> dsimp [UExpr.astSize] <;> omega

/-- **AST Size Monotonicity (`UExpr.normalize_astSize_le`)**:
    Normalization never increases the syntactic AST size of an expression. -/
theorem UExpr.normalize_astSize_le : ∀ e : UExpr, e.normalize.astSize ≤ e.astSize
  | .const _ | .x | .exp | .sin | .cos => le_rfl
  | .add a b => by
    dsimp [UExpr.normalize, UExpr.astSize]
    have ha := a.normalize_astSize_le
    have hb := b.normalize_astSize_le
    have h := UExpr.normAdd_astSize_le a.normalize b.normalize
    omega
  | .sub a b => by
    dsimp [UExpr.normalize, UExpr.astSize]
    have ha := a.normalize_astSize_le
    have hb := b.normalize_astSize_le
    have h := UExpr.normSub_astSize_le a.normalize b.normalize
    omega
  | .mul a b => by
    dsimp [UExpr.normalize, UExpr.astSize]
    have ha := a.normalize_astSize_le
    have hb := b.normalize_astSize_le
    have h := UExpr.normMul_astSize_le a.normalize b.normalize
    omega
  | .inv a => by
    dsimp [UExpr.normalize, UExpr.astSize]
    have ha := a.normalize_astSize_le
    have h := UExpr.normInv_astSize_le a.normalize
    omega
  | .integ a => by
    dsimp [UExpr.normalize, UExpr.astSize]
    have ha := a.normalize_astSize_le
    omega
  | .deriv a => by
    dsimp [UExpr.normalize, UExpr.astSize]
    have ha := a.normalize_astSize_le
    have h := UExpr.normDeriv_astSize_le a.normalize
    omega
  | .comp a b => by
    dsimp [UExpr.normalize, UExpr.astSize]
    have ha := a.normalize_astSize_le
    have hb := b.normalize_astSize_le
    have h := UExpr.normComp_astSize_le a.normalize b.normalize
    omega

/-- **Idempotence of `UExpr.normalize` (`UExpr.normalize_idempotent`)**:
    Because every smart constructor inspects already-normalized children and either
    returns one of those children, returns a normal primitive, or constructs a node
    whose normalized children cannot trigger the top-level rule, a single bottom-up
    pass reaches a fixed point of `UExpr.normalize`. -/
theorem UExpr.normalize_idempotent : ∀ e : UExpr, e.normalize.normalize = e.normalize
  | .const _ | .x | .exp | .sin | .cos => rfl
  | .integ a => by
    dsimp [UExpr.normalize]
    rw [a.normalize_idempotent]
  | .add a b => by
    have iha := a.normalize_idempotent
    have ihb := b.normalize_idempotent
    dsimp [UExpr.normalize]
    generalize a.normalize = a' at iha ⊢
    generalize b.normalize = b' at ihb ⊢
    unfold UExpr.normAdd
    split
    · exact iha
    · exact ihb
    · dsimp [UExpr.normalize]
      rw [iha, ihb]
      unfold UExpr.normAdd
      split <;> first | rfl | simp_all
  | .sub a b => by
    have iha := a.normalize_idempotent
    have ihb := b.normalize_idempotent
    dsimp [UExpr.normalize]
    generalize a.normalize = a' at iha ⊢
    generalize b.normalize = b' at ihb ⊢
    unfold UExpr.normSub
    split
    · exact iha
    · dsimp [UExpr.normalize]
      rw [iha, ihb]
      unfold UExpr.normSub
      split <;> first | rfl | simp_all
  | .mul a b => by
    have iha := a.normalize_idempotent
    have ihb := b.normalize_idempotent
    dsimp [UExpr.normalize]
    generalize a.normalize = a' at iha ⊢
    generalize b.normalize = b' at ihb ⊢
    unfold UExpr.normMul
    split
    · exact iha
    · exact ihb
    · dsimp [UExpr.normalize]
      rw [iha, ihb]
      unfold UExpr.normMul
      split <;> first | rfl | simp_all
  | .inv a => by
    have iha := a.normalize_idempotent
    dsimp [UExpr.normalize]
    generalize a.normalize = a' at iha ⊢
    cases a' with
    | inv c =>
      dsimp [UExpr.normInv]
      change UExpr.normInv c.normalize = .inv c at iha
      have hsz := c.normalize_astSize_le
      cases hc : c.normalize with
      | inv d =>
        rw [hc] at iha hsz
        dsimp [UExpr.normInv] at iha
        subst iha
        dsimp [UExpr.astSize] at hsz
        omega
      | _ =>
        rw [hc] at iha
        dsimp [UExpr.normInv] at iha
        injection iha
    | const _ | x | exp | sin | cos | add _ _ | sub _ _ | mul _ _ | integ _ | deriv _ | comp _ _ =>
      dsimp [UExpr.normInv]
      rw [UExpr.normalize, iha]
      rfl
  | .deriv a => by
    have iha := a.normalize_idempotent
    dsimp [UExpr.normalize]
    generalize a.normalize = a' at iha ⊢
    cases a' with
    | integ c =>
      dsimp [UExpr.normDeriv]
      dsimp [UExpr.normalize] at iha
      injection iha
    | const _ | x | exp | sin => rfl
    | cos | add _ _ | sub _ _ | mul _ _ | inv _ | deriv _ | comp _ _ =>
      dsimp [UExpr.normDeriv]
      rw [UExpr.normalize, iha]
      rfl
  | .comp a b => by
    have iha := a.normalize_idempotent
    have ihb := b.normalize_idempotent
    dsimp [UExpr.normalize]
    generalize a.normalize = a' at iha ⊢
    generalize b.normalize = b' at ihb ⊢
    cases b' with
    | x =>
      change (UExpr.normComp a' .x).normalize = UExpr.normComp a' .x
      cases a' <;> exact iha
    | const _ | exp | sin | cos | add _ _ | sub _ _ | mul _ _ | inv _ | integ _ | deriv _ | comp _ _ =>
      cases a' with
      | const q => rfl
      | x | exp | sin | cos | add _ _ | sub _ _ | mul _ _ | inv _ | integ _ | deriv _ | comp _ _ =>
        dsimp [UExpr.normComp]
        rw [UExpr.normalize]
        simp only [iha, ihb]
        rfl

/-! ### Soundness of Each Smart Constructor -/

theorem UExpr.normAdd_eval_val (a b : UExpr) (n : Nat) :
    ((UExpr.normAdd a b).eval n).val = ((UExpr.add a b).eval n).val := by
  unfold UExpr.normAdd
  split
  · rename_i _ d
    change (a.eval n).val = (Q.add (a.eval n) ((Jet.const ⟨0, d⟩).coeff n)).val
    rw [Q.val_add]
    cases n with
    | zero =>
      change (a.eval 0).val = (a.eval 0).val + (⟨0, d⟩ : Q).val
      have h0 : (⟨0, d⟩ : Q).val = 0 := by unfold Q.val; simp
      rw [h0, add_zero]
    | succ k =>
      change (a.eval (k + 1)).val = (a.eval (k + 1)).val + Q.zero.val
      rw [Q.val_zero, add_zero]
  · rename_i _ d _
    change (b.eval n).val = (Q.add ((Jet.const ⟨0, d⟩).coeff n) (b.eval n)).val
    rw [Q.val_add]
    cases n with
    | zero =>
      change (b.eval 0).val = (⟨0, d⟩ : Q).val + (b.eval 0).val
      have h0 : (⟨0, d⟩ : Q).val = 0 := by unfold Q.val; simp
      rw [h0, zero_add]
    | succ k =>
      change (b.eval (k + 1)).val = Q.zero.val + (b.eval (k + 1)).val
      rw [Q.val_zero, zero_add]
  · rfl

theorem UExpr.normAdd_defined {a b : UExpr} (ha : a.Defined) (hb : b.Defined) :
    (UExpr.normAdd a b).Defined := by
  unfold UExpr.normAdd
  split
  · exact ha
  · exact hb
  · exact ⟨ha, hb⟩

theorem UExpr.normSub_eval_val (a b : UExpr) (n : Nat) :
    ((UExpr.normSub a b).eval n).val = ((UExpr.sub a b).eval n).val := by
  unfold UExpr.normSub
  split
  · rename_i _ d
    change (a.eval n).val = (Q.sub (a.eval n) ((Jet.const ⟨0, d⟩).coeff n)).val
    rw [Q.val_sub]
    cases n with
    | zero =>
      change (a.eval 0).val = (a.eval 0).val - (⟨0, d⟩ : Q).val
      have h0 : (⟨0, d⟩ : Q).val = 0 := by unfold Q.val; simp
      rw [h0, sub_zero]
    | succ k =>
      change (a.eval (k + 1)).val = (a.eval (k + 1)).val - Q.zero.val
      rw [Q.val_zero, sub_zero]
  · rfl

theorem UExpr.normSub_defined {a b : UExpr} (ha : a.Defined) (hb : b.Defined) :
    (UExpr.normSub a b).Defined := by
  unfold UExpr.normSub
  split
  · exact ha
  · exact ⟨ha, hb⟩

theorem UExpr.normMul_eval_val (a b : UExpr) (n : Nat) :
    ((UExpr.normMul a b).eval n).val = ((UExpr.mul a b).eval n).val := by
  unfold UExpr.normMul
  split
  · change (a.eval n).val = (((tmJetMul (Γ := [])).eval Env.nil) a.eval (Jet.const (Q.ofNat 1)).coeff n).val
    rw [inv_jetMul_val, inv_mul_one_val]
  · change (b.eval n).val = (((tmJetMul (Γ := [])).eval Env.nil) (Jet.const (Q.ofNat 1)).coeff b.eval n).val
    rw [inv_jetMul_comm_val (Jet.const (Q.ofNat 1)).coeff b.eval n, inv_jetMul_val, inv_mul_one_val]
  · rfl

theorem UExpr.normMul_defined {a b : UExpr} (ha : a.Defined) (hb : b.Defined) :
    (UExpr.normMul a b).Defined := by
  unfold UExpr.normMul
  split
  · exact ha
  · exact hb
  · exact ⟨ha, hb⟩

theorem UExpr.normInv_eval_val (a : UExpr)
    (ha_inv : ∀ c, a = .inv c → (c.eval 0).val ≠ 0) (n : Nat) :
    ((UExpr.normInv a).eval n).val = ((UExpr.inv a).eval n).val := by
  cases a with
  | inv c =>
    dsimp [UExpr.normInv, UExpr.eval]
    exact (Jet.recip_recip_val c.eval (ha_inv c rfl) n).symm
  | _ => rfl

theorem UExpr.normInv_defined {a : UExpr} (ha : a.Defined) (h0 : (a.eval 0).val ≠ 0) :
    (UExpr.normInv a).Defined := by
  cases a with
  | inv c =>
    dsimp [UExpr.normInv]
    exact ha.1
  | _ =>
    exact ⟨ha, h0⟩

theorem UExpr.normDeriv_eval_val (a : UExpr) (n : Nat) :
    ((UExpr.normDeriv a).eval n).val = ((UExpr.deriv a).eval n).val := by
  cases a with
  | integ c =>
    dsimp [UExpr.normDeriv]
    rw [nwt_deriv_eval_val (.integ c) n]
    change (c.eval n).val = ((n + 1 : Nat) : Rat) * (Q.div (c.eval n) (Q.ofNat (n + 1))).val
    have hn_nz : (Q.ofNat (n + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n)
    have hn_rat : ((n + 1 : Nat) : Rat) ≠ 0 := by positivity
    rw [Q.val_div _ _ hn_nz, Q.val_ofNat]
    field_simp
  | const q =>
    dsimp [UExpr.normDeriv]
    rw [nwt_deriv_eval_val (.const q) n]
    change ((Jet.const Q.zero).coeff n).val = ((n + 1 : Nat) : Rat) * Q.zero.val
    rw [Q.val_zero, mul_zero]
    cases n <;> exact Q.val_zero
  | x =>
    dsimp [UExpr.normDeriv]
    rw [nwt_deriv_eval_val .x n]
    cases n with
    | zero =>
      change (Q.ofNat 1).val = ((1 : Nat) : Rat) * (Q.ofNat 1).val
      rw [Q.val_ofNat]
      norm_num
    | succ k =>
      change Q.zero.val = ((k + 1 + 1 : Nat) : Rat) * Q.zero.val
      rw [Q.val_zero, mul_zero]
  | exp =>
    dsimp [UExpr.normDeriv]
    rw [nwt_deriv_eval_val .exp n]
    have he := Jet.exp_deriv_val n
    dsimp [Jet.deriv] at he
    rw [Q.val_mul, Q.val_ofNat] at he
    exact he.symm
  | sin =>
    dsimp [UExpr.normDeriv]
    rw [nwt_deriv_eval_val .sin n]
    have hs := (Jet.sin_cos_deriv_val n).1
    dsimp [Jet.deriv] at hs
    rw [Q.val_mul, Q.val_ofNat] at hs
    exact hs.symm
  | _ => rfl

theorem UExpr.normDeriv_defined {a : UExpr} (ha : a.Defined) :
    (UExpr.normDeriv a).Defined := by
  cases a with
  | const _ | x | exp | sin => trivial
  | integ _ | cos | add _ _ | sub _ _ | mul _ _ | inv _ | deriv _ | comp _ _ => exact ha

theorem UExpr.normComp_eval_val (a b : UExpr) (n : Nat) :
    ((UExpr.normComp a b).eval n).val = ((UExpr.comp a b).eval n).val := by
  unfold UExpr.normComp
  split
  · exact (compZero_varX_right_val ⟨a.eval⟩ n).symm
  · rename_i _ q _
    exact (compZero_const_val (Jet.const q) ⟨b.eval⟩ (fun _ ↦ Q.val_zero) n).symm
  · rfl

theorem UExpr.normComp_defined {a b : UExpr} (ha : a.Defined) (hb : b.Defined) :
    (UExpr.normComp a b).Defined := by
  unfold UExpr.normComp
  split
  · exact ha
  · trivial
  · exact ⟨ha, hb⟩

/-- **Simultaneous Definedness Preservation and Exact Coefficient Soundness (`UExpr.normalize_spec`)**:
    For every well-defined expression `e : UExpr`:
    1. `e.normalize.Defined` holds;
    2. `∀ n, (e.normalize.eval n).val = (e.eval n).val`. -/
theorem UExpr.normalize_spec : ∀ (e : UExpr), e.Defined →
    e.normalize.Defined ∧ ∀ n : Nat, (e.normalize.eval n).val = (e.eval n).val
  | .const _, _ => ⟨trivial, fun _ ↦ rfl⟩
  | .x, _ => ⟨trivial, fun _ ↦ rfl⟩
  | .exp, _ => ⟨trivial, fun _ ↦ rfl⟩
  | .sin, _ => ⟨trivial, fun _ ↦ rfl⟩
  | .cos, _ => ⟨trivial, fun _ ↦ rfl⟩
  | .add a b, ⟨ha, hb⟩ => by
    obtain ⟨ha_def, ha_val⟩ := a.normalize_spec ha
    obtain ⟨hb_def, hb_val⟩ := b.normalize_spec hb
    refine ⟨UExpr.normAdd_defined ha_def hb_def, fun n ↦ ?_⟩
    dsimp [UExpr.normalize]
    rw [UExpr.normAdd_eval_val]
    change (Q.add (a.normalize.eval n) (b.normalize.eval n)).val =
      (Q.add (a.eval n) (b.eval n)).val
    rw [Q.val_add, Q.val_add, ha_val n, hb_val n]
  | .sub a b, ⟨ha, hb⟩ => by
    obtain ⟨ha_def, ha_val⟩ := a.normalize_spec ha
    obtain ⟨hb_def, hb_val⟩ := b.normalize_spec hb
    refine ⟨UExpr.normSub_defined ha_def hb_def, fun n ↦ ?_⟩
    dsimp [UExpr.normalize]
    rw [UExpr.normSub_eval_val]
    change (Q.sub (a.normalize.eval n) (b.normalize.eval n)).val =
      (Q.sub (a.eval n) (b.eval n)).val
    rw [Q.val_sub, Q.val_sub, ha_val n, hb_val n]
  | .mul a b, ⟨ha, hb⟩ => by
    obtain ⟨ha_def, ha_val⟩ := a.normalize_spec ha
    obtain ⟨hb_def, hb_val⟩ := b.normalize_spec hb
    refine ⟨UExpr.normMul_defined ha_def hb_def, fun n ↦ ?_⟩
    dsimp [UExpr.normalize]
    rw [UExpr.normMul_eval_val]
    exact tmJetMul_agreeV Env.nil Env.nil (n + 1)
      a.normalize.eval a.eval b.normalize.eval b.eval
      (fun i _ ↦ ha_val i) (fun i _ ↦ hb_val i) n (Nat.lt_succ_self n)
  | .inv a, ⟨ha, h0⟩ => by
    obtain ⟨ha_def, ha_val⟩ := a.normalize_spec ha
    have h0_norm : (a.normalize.eval 0).val ≠ 0 := by rwa [ha_val 0]
    have ha_inv : ∀ c, a.normalize = .inv c → (c.eval 0).val ≠ 0 := by
      intro c hc
      rw [hc] at ha_def
      exact ha_def.2
    refine ⟨UExpr.normInv_defined ha_def h0_norm, fun n ↦ ?_⟩
    dsimp [UExpr.normalize]
    rw [UExpr.normInv_eval_val a.normalize ha_inv n]
    exact Jet.recip_congr_val a.normalize.eval a.eval ha_val h0_norm n
  | .integ a, ha => by
    obtain ⟨ha_def, ha_val⟩ := a.normalize_spec ha
    refine ⟨ha_def, fun n ↦ ?_⟩
    dsimp [UExpr.normalize]
    cases n with
    | zero => rfl
    | succ k =>
      have hn_nz : (Q.ofNat (k + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero k)
      change (Q.div (a.normalize.eval k) (Q.ofNat (k + 1))).val =
        (Q.div (a.eval k) (Q.ofNat (k + 1))).val
      rw [Q.val_div _ _ hn_nz, Q.val_div _ _ hn_nz, ha_val k]
  | .deriv a, ha => by
    obtain ⟨ha_def, ha_val⟩ := a.normalize_spec ha
    refine ⟨UExpr.normDeriv_defined ha_def, fun n ↦ ?_⟩
    dsimp [UExpr.normalize]
    rw [UExpr.normDeriv_eval_val, nwt_deriv_eval_val, nwt_deriv_eval_val, ha_val (n + 1)]
  | .comp a b, ⟨ha, hb⟩ => by
    obtain ⟨ha_def, ha_val⟩ := a.normalize_spec ha
    obtain ⟨hb_def, hb_val⟩ := b.normalize_spec hb
    refine ⟨UExpr.normComp_defined ha_def hb_def, fun n ↦ ?_⟩
    dsimp [UExpr.normalize]
    rw [UExpr.normComp_eval_val]
    exact compZero_congr_both_val ⟨a.normalize.eval⟩ ⟨a.eval⟩ ⟨b.normalize.eval⟩ ⟨b.eval⟩
      ha_val hb_val n

/-- **Definedness Preservation (`UExpr.Defined.normalize`)**. -/
theorem UExpr.Defined.normalize {e : UExpr} (he : e.Defined) : e.normalize.Defined :=
  (e.normalize_spec he).1

/-- **Exact Coefficient Equivalence of `UExpr.normalize` (`UExpr.normalize_eval_eq`)**. -/
theorem UExpr.normalize_eval_eq (e : UExpr) (he : e.Defined) (n : Nat) :
    (e.normalize.eval n).val = (e.eval n).val :=
  (e.normalize_spec he).2 n

/-- **Infinite Real Power-Series Equivalence of `UExpr.normalize` (`UExpr.normalize_analyticValue_eq`)**:
    For every well-defined expression `e : UExpr` and every rational point `x : Q`,
    the true infinite real power series of `e.normalize` and `e` coincide:
    $$(e.\operatorname{normalize}.\operatorname{toCertifiedAnalyticRep}\;\dots).\operatorname{analyticValue}(x)
      = (e.\operatorname{toCertifiedAnalyticRep}\;h_e).\operatorname{analyticValue}(x).$$ -/
theorem UExpr.normalize_analyticValue_eq (e : UExpr) (he : e.Defined) (x : Q) :
    (e.normalize.toCertifiedAnalyticRep he.normalize).analyticValue x =
      (e.toCertifiedAnalyticRep he).analyticValue x := by
  refine CertifiedAnalyticRep.analyticValue_congr _ _ (fun n ↦ ?_) x
  rw [← (e.normalize.toCertifiedAnalyticRep he.normalize).fast_correct n,
      ← (e.toCertifiedAnalyticRep he).fast_correct n]
  change (solFast e.normalize.compile.sys e.normalize.compile.v n).val =
    (solFast e.compile.sys e.compile.v n).val
  rw [← (e.normalize.eval_eq_extracted_and_fast he.normalize n).2,
      ← (e.eval_eq_extracted_and_fast he n).2]
  exact e.normalize_eval_eq he n

/-! ### Multi-Layer Tower Cancellations -/

/-- $m$-fold nested derivative-of-integral tower:
    $\frac{d}{dx}\int_0^x \cdots \frac{d}{dt}\int_0^t e(s)\,ds\cdots dx$. -/
def UExpr.iterDerivInteg : Nat → UExpr → UExpr
  | 0, e => e
  | m + 1, e => .deriv (.integ (UExpr.iterDerivInteg m e))

/-- $m$-fold nested right-composition with `.x`:
    $(\cdots((e \circ x) \circ x)\cdots \circ x)$. -/
def UExpr.iterCompX : Nat → UExpr → UExpr
  | 0, e => e
  | m + 1, e => .comp (UExpr.iterCompX m e) .x

/-- $m$-fold nested double-reciprocal tower:
    $1 / (1 / (\cdots (1 / (1 / e))\cdots))$. -/
def UExpr.iterInvPair : Nat → UExpr → UExpr
  | 0, e => e
  | m + 1, e => .inv (.inv (UExpr.iterInvPair m e))

/-- **Arbitrary-Depth Calculus Tower Collapse (`UExpr.iterDerivInteg_normalize`)**:
    For every depth $m \in \mathbb{N}$ and expression `e`, normalizing the $m$-fold
    $\frac{d}{dx}\int_0^x$ tower collapses all the way to `e.normalize`. -/
theorem UExpr.iterDerivInteg_normalize : ∀ (m : Nat) (e : UExpr),
    (UExpr.iterDerivInteg m e).normalize = e.normalize
  | 0, _ => rfl
  | m + 1, e => by
    change UExpr.normDeriv (.integ (UExpr.iterDerivInteg m e).normalize) = e.normalize
    dsimp [UExpr.normDeriv]
    exact UExpr.iterDerivInteg_normalize m e

/-- **Arbitrary-Depth Composition-Identity Tower Collapse (`UExpr.iterCompX_normalize`)**:
    For every depth $m \in \mathbb{N}$ and expression `e`, normalizing the $m$-fold
    composition tower $(\cdots(e \circ x)\cdots \circ x)$ collapses all the way to `e.normalize`. -/
theorem UExpr.iterCompX_normalize : ∀ (m : Nat) (e : UExpr),
    (UExpr.iterCompX m e).normalize = e.normalize
  | 0, _ => rfl
  | m + 1, e => by
    change UExpr.normComp (UExpr.iterCompX m e).normalize .x = e.normalize
    rw [UExpr.iterCompX_normalize m e]
    cases e.normalize <;> rfl

/-- **Arbitrary-Depth Double-Reciprocal Tower Collapse (`UExpr.iterInvPair_normalize`)**:
    For every depth $m \in \mathbb{N}$ and expression `e` whose normal form is not itself
    an outer `.inv`, normalizing $m$ nested double reciprocals collapses to `e.normalize`. -/
theorem UExpr.iterInvPair_normalize (e : UExpr)
    (he : ∀ c, e.normalize ≠ .inv c) : ∀ m : Nat,
    (UExpr.iterInvPair m e).normalize = e.normalize
  | 0 => rfl
  | m + 1 => by
    change UExpr.normInv (UExpr.normInv (UExpr.iterInvPair m e).normalize) = e.normalize
    rw [UExpr.iterInvPair_normalize e he m]
    cases h : e.normalize with
    | inv c => exact absurd h (he c)
    | _ => rfl

/-! ## Section 3: Semantic Equivalence & Certified Representation Compression -/

/-- **Semantic Equivalence of Certified ODE Representations (`PolyODEProof.SemEq`)**:
    Two `PolyODEProof` representations $P_1$ and $P_2$ are semantically equivalent if they
    define the exact same formal Taylor germ at $0$:
    $$\forall n \in \mathbb{N},\quad P_1.\mathrm{coeff}\;n = P_2.\mathrm{coeff}\;n.$$ -/
def PolyODEProof.SemEq (P₁ P₂ : PolyODEProof) : Prop :=
  ∀ n : Nat, P₁.toCertifiedAnalyticRep.coeff n = P₂.toCertifiedAnalyticRep.coeff n

@[refl]
theorem PolyODEProof.SemEq.refl (P : PolyODEProof) : P.SemEq P :=
  fun _ ↦ rfl

@[symm]
theorem PolyODEProof.SemEq.symm {P₁ P₂ : PolyODEProof} (h : P₁.SemEq P₂) : P₂.SemEq P₁ :=
  fun n ↦ (h n).symm

@[trans]
theorem PolyODEProof.SemEq.trans {P₁ P₂ P₃ : PolyODEProof}
    (h12 : P₁.SemEq P₂) (h23 : P₂.SemEq P₃) : P₁.SemEq P₃ :=
  fun n ↦ (h12 n).trans (h23 n)

/-- Every well-defined expression `e : UExpr` is semantically equivalent (`SemEq`) to its
    normalized compilation `e.normalize.toPolyODEProof`. -/
theorem UExpr.semEq_normalize (e : UExpr) (he : e.Defined) :
    (e.toPolyODEProof he).SemEq (e.normalize.toPolyODEProof he.normalize) := by
  intro n
  change (e.toCertifiedAnalyticRep he).coeff n =
    (e.normalize.toCertifiedAnalyticRep he.normalize).coeff n
  rw [← (e.toCertifiedAnalyticRep he).fast_correct n,
      ← (e.normalize.toCertifiedAnalyticRep he.normalize).fast_correct n]
  change (solFast e.compile.sys e.compile.v n).val =
    (solFast e.normalize.compile.sys e.normalize.compile.v n).val
  rw [← (e.eval_eq_extracted_and_fast he n).2,
      ← (e.normalize.eval_eq_extracted_and_fast he.normalize n).2]
  exact (e.normalize_eval_eq he n).symm

/-- **Analytic Germ Agreement (`PolyODEProof.SemEq.analyticValue_eq`)**:
    If `P₁.SemEq P₂`, then their infinite power-series sums in $\mathbb{R}$ are equal at every `x : Q`. -/
theorem PolyODEProof.SemEq.analyticValue_eq {P₁ P₂ : PolyODEProof}
    (h : P₁.SemEq P₂) (x : Q) :
    P₁.toCertifiedAnalyticRep.analyticValue x = P₂.toCertifiedAnalyticRep.analyticValue x :=
  CertifiedAnalyticRep.analyticValue_congr _ _ h x

/-- **Representation Compression Theorem (`PolyODEProof.compress_of_coeff_eq`)**:
    Given `h : P₁.SemEq P₂` ($\forall n,\;c_{P_1}(n) = c_{P_2}(n)$):
    1. **Common-Disk Certified Evaluation**: For any `x : Q` in the certified disk of `P₂`
       ($|x.\mathrm{val}| \le 2^{-(R_2 + 1)}$), evaluating the compressed representation `P₂`
       via `GPACSys.approxFast P₂.sys P₂.v x k` approximates `P₁.toCertifiedAnalyticRep.analyticValue x`
       within $2^{-k}$ in $\mathbb{R}$ (using `P₂`'s truncation modulus $k + M_2 + 3$).
    2. **Certified Analytic Continuation**: If $R_2 \le R_1$, then every point `x` in `P₁`'s
       certified disk $|x.\mathrm{val}| \le 2^{-(R_1 + 1)}$ automatically lies in `P₂`'s larger
       certified disk $|x.\mathrm{val}| \le 2^{-(R_2 + 1)}$, so `P₂` provides both a drop-in
       evaluator on `P₁`'s disk and a certified analytic continuation to $|x.\mathrm{val}| \le 2^{-(R_2 + 1)}$. -/
theorem PolyODEProof.compress_of_coeff_eq {P₁ P₂ : PolyODEProof}
    (h : P₁.SemEq P₂) (k : Nat) :
    (∀ x : Q, |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P₂.sys).2 + 1) →
      |((GPACSys.approxFast P₂.sys P₂.v x k).val : ℝ) -
          P₁.toCertifiedAnalyticRep.analyticValue x| ≤ 1 / (2 : ℝ) ^ k) ∧
    ((sysParams P₂.sys).2 ≤ (sysParams P₁.sys).2 →
      ∀ x : Q, |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P₁.sys).2 + 1) →
        |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P₂.sys).2 + 1) ∧
        |((GPACSys.approxFast P₂.sys P₂.v x k).val : ℝ) -
            P₁.toCertifiedAnalyticRep.analyticValue x| ≤ 1 / (2 : ℝ) ^ k) := by
  have hcommon : ∀ x : Q, |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P₂.sys).2 + 1) →
      |((GPACSys.approxFast P₂.sys P₂.v x k).val : ℝ) -
          P₁.toCertifiedAnalyticRep.analyticValue x| ≤ 1 / (2 : ℝ) ^ k := by
    intro x hx
    rw [PolyODEProof.SemEq.analyticValue_eq h x]
    exact certified_evaluation P₂ x k hx
  refine ⟨hcommon, fun hR x hxP ↦ ?_⟩
  have hpow : (2 : Rat) ^ ((sysParams P₂.sys).2 + 1) ≤ (2 : Rat) ^ ((sysParams P₁.sys).2 + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv : 1 / (2 : Rat) ^ ((sysParams P₁.sys).2 + 1) ≤
      1 / (2 : Rat) ^ ((sysParams P₂.sys).2 + 1) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hxQ : |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P₂.sys).2 + 1) := le_trans hxP hdiv
  exact ⟨hxQ, hcommon x hxQ⟩

/-! ## Section 4: Explicit Representation Cost & Certified Optimizing Compiler -/

/-- State dimension (number of ODE equations) of a `PolyODEProof`. -/
def PolyODEProof.dim (P : PolyODEProof) : Nat := P.sys.length

/-- Majorant exponent $M$ where $|c_n| \le 2^M \cdot (2^R)^n$ and $N(k) = k + M + 3$. -/
def PolyODEProof.majM (P : PolyODEProof) : Nat := (sysParams P.sys).1

/-- Radius exponent $R$ where the certified convergence disk is $|x| \le 2^{-(R+1)}$. -/
def PolyODEProof.radR (P : PolyODEProof) : Nat := (sysParams P.sys).2

/-- Combined structural cost metric `dim + M + R` of a `PolyODEProof`. -/
def PolyODEProof.RepCost (P : PolyODEProof) : Nat :=
  P.dim + P.majM + P.radR

/-- **Multi-Parameter Representation Dominance (`PolyODEProof.BetterRep P₂ P₁`)**:
    `P₂` is a better (or equal) certified representation than `P₁` if:
    1. `P₂` has no more ODE equations (`P₂.dim ≤ P₁.dim`),
    2. `P₂` requires no higher truncation degree (`P₂.majM ≤ P₁.majM`), and
    3. `P₂` has a certified convergence disk at least as large (`P₂.radR ≤ P₁.radR`). -/
def PolyODEProof.BetterRep (P₂ P₁ : PolyODEProof) : Prop :=
  P₂.dim ≤ P₁.dim ∧ P₂.majM ≤ P₁.majM ∧ P₂.radR ≤ P₁.radR

instance (P₂ P₁ : PolyODEProof) : Decidable (PolyODEProof.BetterRep P₂ P₁) := by
  unfold PolyODEProof.BetterRep
  infer_instance

@[refl]
theorem PolyODEProof.BetterRep.refl (P : PolyODEProof) : P.BetterRep P :=
  ⟨le_rfl, le_rfl, le_rfl⟩

@[trans]
theorem PolyODEProof.BetterRep.trans {A B C : PolyODEProof}
    (hAB : A.BetterRep B) (hBC : B.BetterRep C) : A.BetterRep C :=
  ⟨le_trans hAB.1 hBC.1, le_trans hAB.2.1 hBC.2.1, le_trans hAB.2.2 hBC.2.2⟩

theorem PolyODEProof.BetterRep.repCost_le {P₂ P₁ : PolyODEProof}
    (h : P₂.BetterRep P₁) : P₂.RepCost ≤ P₁.RepCost := by
  unfold PolyODEProof.RepCost
  have := h.1; have := h.2.1; have := h.2.2
  omega

/-- **Certified Candidate Selector (`PolyODEProof.selectBetter`)**:
    Given a baseline representation `P₁` and a semantically equivalent candidate `P₂`
    (`_hsem : P₁.SemEq P₂`), accepts `P₂` if `P₂.BetterRep P₁` holds, and keeps `P₁` otherwise. -/
def PolyODEProof.selectBetter (P₁ P₂ : PolyODEProof) (_hsem : P₁.SemEq P₂) : PolyODEProof :=
  if P₂.BetterRep P₁ then P₂ else P₁

/-- **Correctness & Cost Monotonicity of `selectBetter` (`PolyODEProof.selectBetter_spec`)**:
    1. `P₁.SemEq (P₁.selectBetter P₂ hsem)` (semantic equivalence is preserved),
    2. `(P₁.selectBetter P₂ hsem).BetterRep P₁` (none of `dim`, `majM`, `radR` ever worsens),
    3. `(P₁.selectBetter P₂ hsem).RepCost ≤ P₁.RepCost`, and
    4. whenever `P₂.BetterRep P₁` holds, `P₁.selectBetter P₂ hsem = P₂`. -/
theorem PolyODEProof.selectBetter_spec (P₁ P₂ : PolyODEProof) (hsem : P₁.SemEq P₂) :
    P₁.SemEq (P₁.selectBetter P₂ hsem) ∧
    (P₁.selectBetter P₂ hsem).BetterRep P₁ ∧
    (P₁.selectBetter P₂ hsem).RepCost ≤ P₁.RepCost ∧
    (P₂.BetterRep P₁ → P₁.selectBetter P₂ hsem = P₂) := by
  unfold PolyODEProof.selectBetter
  split_ifs with hbetter
  · exact ⟨hsem, hbetter, hbetter.repCost_le, fun _ ↦ rfl⟩
  · exact ⟨PolyODEProof.SemEq.refl P₁, PolyODEProof.BetterRep.refl P₁, le_rfl,
      fun h ↦ absurd h hbetter⟩

/-- **Certified Optimizing Compiler (`UExpr.optimizeToPolyODEProof`)**:
    Normalizes `e` via `UExpr.normalize`, compiles both `e` and `e.normalize` to
    `PolyODEProof`, and selects the better certified representation via `selectBetter`. -/
def UExpr.optimizeToPolyODEProof (e : UExpr) (he : e.Defined) : PolyODEProof :=
  (e.toPolyODEProof he).selectBetter
    (e.normalize.toPolyODEProof he.normalize)
    (e.semEq_normalize he)

/-- **Master Theorem for `UExpr.optimizeToPolyODEProof` (`UExpr.optimizeToPolyODEProof_spec`)**:
    For every well-defined expression `e : UExpr`:
    1. **Semantic Equivalence**: `(e.toPolyODEProof he).SemEq (e.optimizeToPolyODEProof he)`;
    2. **Dominance**: `(e.optimizeToPolyODEProof he).BetterRep (e.toPolyODEProof he)`
       (ODE dimension, majorant $M$, and radius exponent $R$ never worsen);
    3. **Certified Evaluation on Original Disk**: For every `x` in the original disk of `e`
       ($|x.\mathrm{val}| \le 2^{-(R_e + 1)}$) and precision `k : Nat`, evaluating the
       optimized ODE system `e.optimizeToPolyODEProof he` via `GPACSys.approxFast`
       approximates `(e.toCertifiedAnalyticRep he).analyticValue x` within $2^{-k}$ in $\mathbb{R}$. -/
theorem UExpr.optimizeToPolyODEProof_spec (e : UExpr) (he : e.Defined) :
    let P := e.toPolyODEProof he
    let P_opt := e.optimizeToPolyODEProof he
    P.SemEq P_opt ∧
    P_opt.BetterRep P ∧
    P_opt.RepCost ≤ P.RepCost ∧
    (∀ (x : Q) (k : Nat),
      |x.val| ≤ 1 / (2 : Rat) ^ ((sysParams P.sys).2 + 1) →
      |((GPACSys.approxFast P_opt.sys P_opt.v x k).val : ℝ) -
          P.toCertifiedAnalyticRep.analyticValue x| ≤ 1 / (2 : ℝ) ^ k) := by
  dsimp only
  obtain ⟨hsem, hbetter, hcost, _⟩ :=
    PolyODEProof.selectBetter_spec (e.toPolyODEProof he)
      (e.normalize.toPolyODEProof he.normalize) (e.semEq_normalize he)
  refine ⟨hsem, hbetter, hcost, fun x k hx ↦ ?_⟩
  exact ((PolyODEProof.compress_of_coeff_eq hsem k).2 hbetter.2.2 x hx).2

/-! ## Section 5: Concrete Demonstration — Autonomous-Inverse Compression to `.x` -/

/-- The 1-state identity ODE representation `y' = 1, y(0) = 0` (`UExpr.x.toPolyODEProof trivial`). -/
def PolyODEProof.varX : PolyODEProof :=
  UExpr.x.toPolyODEProof trivial

theorem PolyODEProof.varX_dim : PolyODEProof.varX.dim = 1 := rfl
theorem PolyODEProof.varX_majM : PolyODEProof.varX.majM = 1 := rfl
theorem PolyODEProof.varX_radR : PolyODEProof.varX.radR = 4 := rfl

/-- `PolyODEProof.varX` has minimal state dimension `1 ≤ P.dim` for every `P : PolyODEProof`. -/
theorem PolyODEProof.varX_dim_le (P : PolyODEProof) :
    PolyODEProof.varX.dim ≤ P.dim := by
  change 1 ≤ P.sys.length
  have := P.hv
  omega

/-- **Autonomous-Inverse Composition Compression Theorem (`UExpr.autoInverse_comp_compress_to_varX`)**:
    Let $F : \mathrm{UExpr}$ be well-defined with $F(0) \neq 0$, and let $P_Y : \mathrm{PolyODEProof}$
    represent the solution $Y(x)$ of the autonomous 1D ODE $Y'(x) = F(Y(x))$, $Y(0) = 0$.
    Let $P_{\mathrm{comp}} := ((\operatorname{UExpr.autoInverse}\;F).\operatorname{toPolyODEProof}\;\dots).\operatorname{comp}\;P_Y$
    be the compiled composition $(\operatorname{autoInverse}(F) \circ Y)$.
    Then:
    1. **Exact Semantic Equivalence (`SemEq`)**: $P_{\mathrm{comp}}.\operatorname{SemEq}\;\mathrm{PolyODEProof.varX}$;
    2. **Dimension Minimality**: $\mathrm{PolyODEProof.varX}.\mathrm{dim} = 1 \le P_{\mathrm{comp}}.\mathrm{dim}$;
    3. **Certified Selection**: `P_comp.selectBetter PolyODEProof.varX hsem` is semantically
       equivalent to `PolyODEProof.varX`, dominates `P_comp` (`BetterRep`), and equals
       `PolyODEProof.varX` whenever `PolyODEProof.varX.BetterRep P_comp` holds. -/
theorem UExpr.autoInverse_comp_compress_to_varX (F : UExpr) (hF : F.Defined)
    (hF0 : (F.eval 0).val ≠ 0) (P_Y : PolyODEProof)
    (hY0 : (solFast P_Y.sys P_Y.v 0).val = 0)
    (hY_ode : ∀ n : Nat,
      ((Jet.mk (solFast P_Y.sys P_Y.v)).deriv.coeff n).val =
        ((Jet.compZero ⟨F.eval⟩ (Jet.mk (solFast P_Y.sys P_Y.v))).coeff n).val) :
    let P_inv := UExpr.autoInverse_toPolyODEProof F hF hF0
    let P_comp := P_inv.comp P_Y
    ∃ hsem : P_comp.SemEq PolyODEProof.varX,
      PolyODEProof.varX.dim ≤ P_comp.dim ∧
      (P_comp.selectBetter PolyODEProof.varX hsem).BetterRep P_comp ∧
      (PolyODEProof.varX.BetterRep P_comp →
        P_comp.selectBetter PolyODEProof.varX hsem = PolyODEProof.varX) ∧
      (∀ x : Q, P_comp.toCertifiedAnalyticRep.analyticValue x =
        PolyODEProof.varX.toCertifiedAnalyticRep.analyticValue x) := by
  intro P_inv P_comp
  have hsem : P_comp.SemEq PolyODEProof.varX := by
    intro n
    change (P_inv.comp P_Y).toCertifiedAnalyticRep.coeff n =
      PolyODEProof.varX.toCertifiedAnalyticRep.coeff n
    rw [P_inv.comp_coeff P_Y n, ← PolyODEProof.varX.toCertifiedAnalyticRep.fast_correct n]
    dsimp [PolyODEProof.toCertifiedAnalyticRep, PolyODEProof.varX, UExpr.toPolyODEProof]
    have hcongr :
        ((Jet.compZero ⟨solN P_inv.sys P_inv.v⟩ ⟨solN P_Y.sys P_Y.v⟩).coeff n).val =
        ((Jet.compZero ⟨(UExpr.autoInverse F).eval⟩ ⟨solFast P_Y.sys P_Y.v⟩).coeff n).val := by
      refine compZero_congr_both_val ⟨solN P_inv.sys P_inv.v⟩ ⟨(UExpr.autoInverse F).eval⟩
        ⟨solN P_Y.sys P_Y.v⟩ ⟨solFast P_Y.sys P_Y.v⟩ (fun m ↦ ?_) (fun m ↦ ?_) n
      · rw [← solFast_val P_inv.sys P_inv.wf P_inv.v P_inv.hv m]
        exact ((UExpr.autoInverse F).eval_eq_extracted_and_fast
          (UExpr.autoInverse_defined F hF hF0) m).2.symm
      · exact (solFast_val P_Y.sys P_Y.wf P_Y.v P_Y.hv m).symm
    rw [hcongr, UExpr.autoInverse_comp_sol_eq_varX F hF0 ⟨solFast P_Y.sys P_Y.v⟩ hY0 hY_ode n]
    exact (UExpr.x.eval_eq_extracted_and_fast trivial n).2
  have hspec := PolyODEProof.selectBetter_spec P_comp PolyODEProof.varX hsem
  exact ⟨hsem, PolyODEProof.varX_dim_le P_comp, hspec.2.1, hspec.2.2.2,
    fun x ↦ PolyODEProof.SemEq.analyticValue_eq hsem x⟩

/-! ## Kernel Checks (`#guard`)

Verify in Lean's kernel that normalizing a 5-deep stacked tower
`iterDerivInteg 5 (iterCompX 5 .exp)` collapses its compiled ODE system back to
1 equation and $(M, R) = (1, 4)$! -/

def towerExample : UExpr :=
  UExpr.iterDerivInteg 5 (UExpr.iterCompX 5 .exp)

theorem towerExample_defined : towerExample.Defined := by
  repeat' constructor

#guard decide (towerExample.normalize = .exp)
#guard towerExample.normalize.compile.sys.length = 1
#guard sysParams towerExample.normalize.compile.sys = (1, 4)
#guard decide ((towerExample.normalize.toPolyODEProof towerExample_defined.normalize).BetterRep
  (towerExample.toPolyODEProof towerExample_defined))

#print axioms UExpr.normalize_astSize_le
#print axioms UExpr.normalize_idempotent
#print axioms UExpr.normalize_spec
#print axioms UExpr.normalize_analyticValue_eq
#print axioms UExpr.iterDerivInteg_normalize
#print axioms UExpr.iterCompX_normalize
#print axioms UExpr.iterInvPair_normalize
#print axioms PolyODEProof.compress_of_coeff_eq
#print axioms PolyODEProof.selectBetter_spec
#print axioms UExpr.optimizeToPolyODEProof_spec
#print axioms UExpr.autoInverse_comp_compress_to_varX

end HAomega
