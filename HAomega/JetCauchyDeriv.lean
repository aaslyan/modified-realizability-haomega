/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.MajorantDom
import HAomega.GcdStage2
import HAomega.GcdFull
import HAomega.HsSemantics

/-!
# Proof-Computed Jet Cauchy Modulus via Telescoping Induction in `Deriv` (`JetCauchyDeriv.lean`)

In `MajorantDom.lean`, the initial `jetCauchyModulusD` took a witness-style multi-step tail
hypothesis (`jetTailPremise`) that already mentioned $k + (B + 2) + d_1$.

This module replaces that with a **genuine proof-computed derivation** (`jetCauchyModulusGenuineD`)
whose jet hypothesis (`jetTermPremise`) is **per-term and $N$-free**:
$$\forall n : \mathbb{N},\quad |S_n(x) - S_{n+1}(x)| < 2^{B+3} \cdot \bigl(2^{-(n+1)} - 2^{-(n+2)}\bigr) = 2^{B+1-n},$$
which is the single-term majorant $|c_n x^n| < 2^{B+1-n}$ read at $x$.

Inside `Deriv`, `jetCauchyModulusGenuineD`:
1. Proves the multi-step geometric tail bound
   $$|S_m(x) - S_{m+d_2}(x)| < 2^{B+3} \cdot \bigl(2^{-m} - 2^{-(m + d_2 + 1)}\bigr)$$
   by **mathematical induction (`Deriv.ind`) on the span $d_2$**:
   - **Base case ($d_2 = 0$):** reduces $m + 0 = m$ (`Deriv.convAddZero`) and
     $S_m(x) - S_m(x) = 0$ (`Deriv.convQSubSelf`).
   - **Inductive step ($d_2 \to d_2 + 1$):** instantiates the per-term bound at $n = m + d_2$,
     adds it to the induction hypothesis via **`qAddLtAdd`** (the same object-language lemma designed
     for `EFTC1`), applies the triangle inequality via **`Deriv.convQLeLtTrans`**, and cancels the
     telescoping midpoint $2^{-(m + d_2 + 1)}$ via **`Deriv.qltEqRight`**.
2. Reassociates $(k + (B + 3)) + d_1 = (k + d_1) + (B + 3)$ inside `Deriv` via `plusAssocT` and
   `plusCommT`, cancels $2^{B+3} \cdot 2^{-((k+d_1)+(B+3))} = 2^{-(k+d_1)}$ via
   **`Deriv.convQLtTrans`**, folds `qclose` via three **`Deriv.convBeta`** steps, and weakens
   scale $k + d_1$ to $k$ via **`Deriv.convQCloseMono`**.
3. Discharges `jetTermPremise` for **every** `F : AnalyticJet` on $[-1, 1]$ (at $B = F.\mathrm{expBound}$)
   and for **every** `F : RadiusJet` on $[-2^{-(F.R + 1)}, 2^{-(F.R + 1)}]$ (at $B = F.M$),
   and discharges `jetLipPremise` and `jetDiffPremise` for **every** `F : RadiusJet` on its
   `toE1` disk $[-2^{-(F.R + 3)}, 2^{-(F.R + 3)}]$.
-/

namespace HAomega

open Rat

/-! ## 1. Object-Language Congruence, `qclose` Beta-Expansion, and Term-Form `qAddLtAdd` -/

/-- Congruence for `Tm.qsub` in both arguments, derived from `Deriv.eqSubst`. -/
def qsubCong {Γ as : List Ty} {Δ : Ctx Γ as} {u u' v v' : Tm Γ .rat}
    (hu : Deriv Δ (.eq u u')) (hv : Deriv Δ (.eq v v')) :
    Deriv Δ (.eq (.qsub u v) (.qsub u' v')) := by
  have hs1 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qsub u.wk (.var .here)) (Tm.qsub u v).wk).subst1 z
        = Formula.eq (.qsub u z) (.qsub u v) := by
    intro z
    show Formula.eq (.qsub (u.wk.subst1 z) z) (.qsub (u.wk.subst1 z) (v.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h1 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qsub u.wk (.var .here)) (Tm.qsub u v).wk) hv
    (by rw [hs1]; exact Deriv.eqRefl _)
  rw [hs1] at h1
  have hs2 : ∀ z : Tm Γ .rat,
      (Formula.eq (.qsub (.var .here) v'.wk) (Tm.qsub u v').wk).subst1 z
        = Formula.eq (.qsub z v') (.qsub u v') := by
    intro z
    show Formula.eq (.qsub z (v'.wk.subst1 z)) (.qsub (u.wk.subst1 z) (v'.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have h2 := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.qsub (.var .here) v'.wk) (Tm.qsub u v').wk) hu
    (by rw [hs2]; exact Deriv.eqRefl _)
  rw [hs2] at h2
  exact Deriv.transE h1.symmE h2.symmE

/-- Congruence for `Tm.add` in the right argument, derived from `Deriv.eqSubst`. -/
def addCongRight {Γ as : List Ty} {Δ : Ctx Γ as} (a : Tm Γ .nat) {b b' : Tm Γ .nat}
    (h : Deriv Δ (.eq b b')) : Deriv Δ (.eq (.add a b) (.add a b')) := by
  have hs : ∀ z : Tm Γ .nat,
      (Formula.eq (.add a.wk (.var .here)) (Tm.add a b).wk).subst1 z
        = Formula.eq (.add a z) (.add a b) := by
    intro z
    show Formula.eq (.add (a.wk.subst1 z) z) (.add (a.wk.subst1 z) (b.wk.subst1 z)) = _
    rw [Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (.add a.wk (.var .here)) (Tm.add a b).wk) h
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key
  exact key.symmE

/-- Term-level wrapper around `qAddLtAdd` (`a < c → b < d → a + b < c + d` in `Deriv`). -/
def qAddLtAddT {Γ as : List Ty} {Δ : Ctx Γ as} (a b c d : Tm Γ .rat)
    (hac : Deriv Δ (.eq (.qlt a c) (.succ .zero)))
    (hbd : Deriv Δ (.eq (.qlt b d) (.succ .zero))) :
    Deriv Δ (.eq (.qlt (.qadd a b) (.qadd c d)) (.succ .zero)) := by
  have h1 := Deriv.allE a (qAddLtAdd (Δ := Δ))
  deriv_norm at h1
  have h2 := Deriv.allE b h1
  deriv_norm at h2
  have h3 := Deriv.allE c h2
  deriv_norm at h3
  have h4 := Deriv.allE d h3
  deriv_norm at h4
  exact Deriv.impE (Deriv.impE h4 hac) hbd

/-- Three-step `convBeta` unfolding of `qclose s u v` in `Deriv`. -/
def qcloseBeta {Γ as : List Ty} {Δ : Ctx Γ as} (s : Tm Γ .nat) (u v : Tm Γ .rat) :
    Deriv Δ (.eq (.app (.app (.app qclose s) u) v)
                 (.qlt (.app qabsT (.qsub u v)) (.app qpow2 s))) := by
  have hb1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.lam (.lam (.qlt (.app qabsT (.qsub (.var (.there .here)) (.var .here)))
      (.app qpow2 (.var (.there (.there .here))))))) s
  deriv_norm at hb1
  have hb1_u := Deriv.congFun hb1 u
  have hb2 := Deriv.convBeta (Δ := Δ) (c := .rat)
    (.lam (.qlt (.app qabsT (.qsub (.var (.there .here)) (.var .here)))
      (.app qpow2 (s.wk.wk)))) u
  deriv_norm at hb2
  have hb12_v := Deriv.congFun (Deriv.transE hb1_u hb2) v
  have hb3 := Deriv.convBeta (Δ := Δ) (c := .rat)
    (.qlt (.app qabsT (.qsub u.wk (.var .here))) (.app qpow2 s.wk)) v
  deriv_norm at hb3
  exact Deriv.transE hb12_v hb3

/-- Fold `qlt (qabsT (u - v)) (qpow2 s) = 1` into `qclose s u v = 1` in `Deriv`. -/
def qcloseIntro {Γ as : List Ty} {Δ : Ctx Γ as} (s : Tm Γ .nat) (u v : Tm Γ .rat)
    (h : Deriv Δ (.eq (.qlt (.app qabsT (.qsub u v)) (.app qpow2 s)) (.succ .zero))) :
    Deriv Δ (.eq (.app (.app (.app qclose s) u) v) (.succ .zero)) := by
  have hs : ∀ z : Tm Γ .nat,
      (Formula.eq (.var .here) (.succ .zero)).subst1 z = Formula.eq z (.succ .zero) :=
    fun _ ↦ rfl
  have key := Deriv.eqSubst (Δ := Δ) (Formula.eq (.var .here) (.succ .zero))
    (qcloseBeta s u v).symmE (by rw [hs]; exact h)
  rw [hs] at key
  exact key

/-- Arithmetic rearrangement `((k + B3) + d1) = ((k + d1) + B3)` in `Deriv`. -/
def addSwapRightT {Γ as : List Ty} {Δ : Ctx Γ as} (k B3 d1 : Tm Γ .nat) :
    Deriv Δ (.eq (.add (.add k B3) d1) (.add (.add k d1) B3)) := by
  have h1 := plusAssocT (Δ := Δ) k B3 d1
  have h2 := addCongRight k (plusCommT (Δ := Δ) B3 d1)
  have h3 := (plusAssocT (Δ := Δ) k d1 B3).symmE
  exact Deriv.transE h1 (Deriv.transE h2 h3)

/-! ## 2. Per-Term Majorant Premise and Telescoping Geometric Targets in `Tm` -/

/-- Single-term geometric upper target $2^{B+3} \cdot (2^{-(n+1)} - 2^{-(n+2)}) = 2^{B+1-n}$. -/
abbrev jetStepBound {Γ : List Ty} (B n : Tm Γ .nat) : Tm Γ .rat :=
  .qmul (.app qpow2pos (.succ (.succ (.succ B))))
        (.qsub (.app qpow2 (.succ n)) (.app qpow2 (.succ (.succ n))))

/-- Multi-step telescoping upper target $2^{B+3} \cdot (2^{-m} - 2^{-(m + d_2 + 1)})$. -/
abbrev jetTailBound {Γ : List Ty} (B m d2 : Tm Γ .nat) : Tm Γ .rat :=
  .qmul (.app qpow2pos (.succ (.succ (.succ B))))
        (.qsub (.app qpow2 m) (.app qpow2 (.succ (.add m d2))))

/-- Congruence for `jetTailBound` in its degree argument `m`. -/
def jetTailBoundCongM {Γ as : List Ty} {Δ : Ctx Γ as}
    (B : Tm Γ .nat) {m m' : Tm Γ .nat} (d2 : Tm Γ .nat)
    (hm : Deriv Δ (.eq m m')) :
    Deriv Δ (.eq (jetTailBound B m d2) (jetTailBound B m' d2)) := by
  have hs : ∀ z : Tm Γ .nat,
      (Formula.eq (jetTailBound B.wk (.var .here) d2.wk) (jetTailBound B m d2).wk).subst1 z
        = Formula.eq (jetTailBound B z d2) (jetTailBound B m d2) := by
    intro z
    show Formula.eq
      (.qmul (.app qpow2pos (.succ (.succ (.succ (B.wk.subst1 z)))))
        (.qsub (.app qpow2 z) (.app qpow2 (.succ (.add z (d2.wk.subst1 z))))))
      (.qmul (.app qpow2pos (.succ (.succ (.succ (B.wk.subst1 z)))))
        (.qsub (.app qpow2 (m.wk.subst1 z)) (.app qpow2 (.succ (.add (m.wk.subst1 z) (d2.wk.subst1 z)))))) = _
    rw [Tm.subst1_wk, Tm.subst1_wk, Tm.subst1_wk]
  have key := Deriv.eqSubst (Δ := Δ)
    (Formula.eq (jetTailBound B.wk (.var .here) d2.wk) (jetTailBound B m d2).wk) hm
    (by rw [hs]; exact Deriv.eqRefl _)
  rw [hs] at key
  exact key.symmE

/-- **Per-Term Majorant Premise (`jetTermPremise`)**:
    For a coefficient stream $c : \mathrm{JetTy}$, majorant exponent $B : \mathrm{nat}$, and point
    $x : \mathrm{rat}$, asserts ONLY the single-step bound
    $$\forall n : \mathrm{nat},\quad |S_n(x) - S_{n+1}(x)| < 2^{B+3} \cdot \bigl(2^{-(n+1)} - 2^{-(n+2)}\bigr),$$
    which is $|c_n x^n| < 2^{B+1-n}$.
    Completely free of $k$, $N$, $d_1$, and $d_2$! -/
abbrev jetTermPremise (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ) (.arrow .nat .unit) :=
  let ctx1 : List Ty := .nat :: .rat :: .nat :: JetTy :: Γ
  let n : Tm ctx1 .nat := .var .here
  let x : Tm ctx1 .rat := .var (.there .here)
  let B : Tm ctx1 .nat := .var (.there (.there .here))
  let c : Tm ctx1 JetTy := .var (.there (.there (.there .here)))
  .all .nat
    (.eq (.qlt (.app qabsT (.qsub (jetEvalAt c n x) (jetEvalAt c (.succ n) x)))
               (jetStepBound B n))
         (.succ .zero))

/-- Unconditional $\mathbb{Q}$-positivity of the $d_2 = 0$ telescoping bound:
    $\forall m : \mathrm{nat},\; |0| < 2^{B+3} \cdot (2^{-m} - 2^{-(m+1)})$. -/
abbrev qGeomZeroPremise (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ) (.arrow .nat .unit) :=
  let ctx1 : List Ty := .nat :: .rat :: .nat :: JetTy :: Γ
  let m : Tm ctx1 .nat := .var .here
  let B : Tm ctx1 .nat := .var (.there (.there .here))
  .all .nat
    (.eq (.qlt (.app qabsT (.qnat .zero)) (jetTailBound B m .zero)) (.succ .zero))

/-- Unconditional $\mathbb{Q}$-triangle inequality:
    $\forall u, v, w : \mathrm{rat},\; |u - w| \le |u - v| + |v - w|$. -/
abbrev qTrianglePremise (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ) (.arrow .rat (.arrow .rat (.arrow .rat .unit))) :=
  let ctx3 : List Ty := .rat :: .rat :: .rat :: .rat :: .nat :: JetTy :: Γ
  let w : Tm ctx3 .rat := .var .here
  let v : Tm ctx3 .rat := .var (.there .here)
  let u : Tm ctx3 .rat := .var (.there (.there .here))
  .all .rat (.all .rat (.all .rat
    (.eq (.qlt (.qadd (.app qabsT (.qsub u v)) (.app qabsT (.qsub v w)))
               (.app qabsT (.qsub u w)))
         .zero)))

/-- Unconditional $\mathbb{Q}$-telescoping equality (true propositionally on `Q` via `Q.of_inj_val`):
    $\forall m, d_2 : \mathrm{nat},\; \mathrm{jetTailBound}\;B\;m\;d_2 + \mathrm{jetStepBound}\;B\;(m + d_2) = \mathrm{jetTailBound}\;B\;m\;(d_2 + 1)$. -/
abbrev qTelescopePremise (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ) (.arrow .nat (.arrow .nat .unit)) :=
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx2 .nat := .var .here
  let m  : Tm ctx2 .nat := .var (.there .here)
  let B  : Tm ctx2 .nat := .var (.there (.there (.there .here)))
  .all .nat (.all .nat
    (.eq (.qadd (jetTailBound B m d2) (jetStepBound B (.add m d2)))
         (jetTailBound B m (.succ d2))))

/-- Unconditional dyadic scale cancellation:
    $\forall s, d_2 : \mathrm{nat},\; \mathrm{jetTailBound}\;B\;(s + (B + 3))\;d_2 < 2^{-s}$. -/
abbrev qScaleCancelPremise (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ) (.arrow .nat (.arrow .nat .unit)) :=
  let ctx2 : List Ty := .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx2 .nat := .var .here
  let s  : Tm ctx2 .nat := .var (.there .here)
  let B  : Tm ctx2 .nat := .var (.there (.there (.there .here)))
  .all .nat (.all .nat
    (.eq (.qlt (jetTailBound B (.add s (.succ (.succ (.succ B)))) d2) (.app qpow2 s))
         (.succ .zero)))

/-- Bundled unconditional $\mathbb{Q}$-arithmetic laws used by the $d_2$-induction.
    Does not mention $c$, $x$, $k$, or $N$, and is proved unconditionally for all $B$ below. -/
abbrev qGeomArithPremise (Γ : List Ty) :
    Formula (.rat :: .nat :: JetTy :: Γ)
      (.prod (.arrow .nat .unit)
        (.prod (.arrow .rat (.arrow .rat (.arrow .rat .unit)))
          (.prod (.arrow .nat (.arrow .nat .unit))
                 (.arrow .nat (.arrow .nat .unit))))) :=
  .and (qGeomZeroPremise Γ)
    (.and (qTrianglePremise Γ)
      (.and (qTelescopePremise Γ) (qScaleCancelPremise Γ)))

/-! ## 3. Unconditional Proofs of the $\mathbb{Q}$-Arithmetic Telescoping Laws -/

/-- `qGeomZeroPremise` holds unconditionally for all $B, m \in \mathbb{N}$. -/
theorem satisfies_qGeomZero (B m : Nat) :
    Q.ltN (Q.abs (Q.ofNat 0))
      (Q.mul (qpow2posVal (B + 3))
        (Q.sub (D.toQ (D.pow2neg m)) (D.toQ (D.pow2neg (m + 0 + 1))))) = 1 := by
  rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_ofNat, Q.val_mul, qpow2posVal_val,
      Q.val_sub, toQ_pow2neg_val, toQ_pow2neg_val]
  have h0 : |((0 : Nat) : Rat)| = 0 := by norm_num
  rw [h0]
  have h1 : (0 : Rat) < (2 : Rat) ^ (B + 3) := by positivity
  have h2 : (1 : Rat) / (2 : Rat) ^ (m + 0 + 1) < 1 / (2 : Rat) ^ m := by
    have hp : (0 : Rat) < 1 / (2 : Rat) ^ (m + 1) := by positivity
    have hsplit : (1 : Rat) / (2 : Rat) ^ m = 1 / (2 : Rat) ^ (m + 1) + 1 / (2 : Rat) ^ (m + 1) := by
      rw [pow_succ (2 : Rat) m]; field_simp; ring
    linarith
  exact mul_pos h1 (sub_pos.mpr h2)

/-- `qTrianglePremise` holds unconditionally for all $u, v, w \in \mathbb{Q}$. -/
theorem satisfies_qTriangle (u v w : Q) :
    Q.ltN (Q.add (Q.abs (Q.sub u v)) (Q.abs (Q.sub v w))) (Q.abs (Q.sub u w)) = 0 := by
  rw [Q.ltN_eq_zero_iff, Q.val_add, Q.val_abs, Q.val_sub, Q.val_abs, Q.val_sub,
      Q.val_abs, Q.val_sub]
  have h_id : u.val - w.val = (u.val - v.val) + (v.val - w.val) := by ring
  rw [h_id]
  exact abs_add_le' (u.val - v.val) (v.val - w.val)

/-- `qTelescopePremise` holds as a **true propositional equality `=` on `Q`** for all $B, m, d_2 \in \mathbb{N}$,
    by `Q.of_inj_val` and `ring`. -/
theorem satisfies_qTelescope (B m d2 : Nat) :
    Q.add
      (Q.mul (qpow2posVal (B + 3))
        (Q.sub (D.toQ (D.pow2neg m)) (D.toQ (D.pow2neg (m + d2 + 1)))))
      (Q.mul (qpow2posVal (B + 3))
        (Q.sub (D.toQ (D.pow2neg (m + d2 + 1))) (D.toQ (D.pow2neg (m + d2 + 2))))) =
    Q.mul (qpow2posVal (B + 3))
      (Q.sub (D.toQ (D.pow2neg m)) (D.toQ (D.pow2neg (m + (d2 + 1) + 1)))) := by
  let lhs1 := Q.mul (qpow2posVal (B + 3))
    (Q.sub (D.toQ (D.pow2neg m)) (D.toQ (D.pow2neg (m + d2 + 1))))
  let lhs2 := Q.mul (qpow2posVal (B + 3))
    (Q.sub (D.toQ (D.pow2neg (m + d2 + 1))) (D.toQ (D.pow2neg (m + d2 + 2))))
  let rhs1 := qpow2posVal (B + 3)
  let rhs2 := Q.sub (D.toQ (D.pow2neg m)) (D.toQ (D.pow2neg (m + (d2 + 1) + 1)))
  refine Q.of_inj_val (Nat.mul_ne_zero lhs1.den_ne_zero lhs2.den_ne_zero)
    (Nat.mul_ne_zero rhs1.den_ne_zero rhs2.den_ne_zero) ?_
  rw [show Q.of _ _ = Q.add lhs1 lhs2 from rfl,
      show Q.of _ _ = Q.mul rhs1 rhs2 from rfl]
  dsimp [lhs1, lhs2, rhs1, rhs2]
  simp only [Q.val_add, Q.val_mul, Q.val_sub, qpow2posVal_val, toQ_pow2neg_val]
  have h_idx : m + (d2 + 1) + 1 = m + d2 + 2 := by omega
  rw [h_idx]
  ring

/-- `qScaleCancelPremise` holds unconditionally for all $B, s, d_2 \in \mathbb{N}$. -/
theorem satisfies_qScaleCancel (B s d2 : Nat) :
    Q.ltN
      (Q.mul (qpow2posVal (B + 3))
        (Q.sub (D.toQ (D.pow2neg (s + (B + 3))))
               (D.toQ (D.pow2neg (s + (B + 3) + d2 + 1)))))
      (D.toQ (D.pow2neg s)) = 1 := by
  rw [Q.ltN_eq_one_iff, Q.val_mul, qpow2posVal_val, Q.val_sub,
      toQ_pow2neg_val, toQ_pow2neg_val, toQ_pow2neg_val]
  have h_prod : (2 : Rat) ^ (B + 3) * (1 / (2 : Rat) ^ (s + (B + 3))) = 1 / (2 : Rat) ^ s := by
    rw [pow_add (2 : Rat) s (B + 3)]
    field_simp
  have h_pos : (0 : Rat) < (2 : Rat) ^ (B + 3) * (1 / (2 : Rat) ^ (s + (B + 3) + d2 + 1)) := by
    positivity
  linarith

/-! ## 4. Proof-Computed Jet Cauchy Modulus by `Deriv.ind` on $d_2$ (`jetCauchyModulusGenuineD`) -/

/-- Context at the innermost point of `jetCauchyModulusGenuineD`. -/
abbrev jetCauchyGenuineInnerCtx (Γ : List Ty) {as : List Ty} (Δ : Ctx Γ as) :
    Ctx (.nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ)
      ((.prod (.arrow .nat .unit)
        (.prod (.arrow .rat (.arrow .rat (.arrow .rat .unit)))
          (.prod (.arrow .nat (.arrow .nat .unit))
                 (.arrow .nat (.arrow .nat .unit))))) ::
       (.arrow .nat .unit) :: as) :=
  .cons ((((qGeomArithPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
    (.cons ((((jetTermPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat))
      ((((((Δ.wk).wk).wk).wk).wk).wk))

/-- **Theorem (Proof-Computed $\forall k\, \exists N$ Jet Cauchy Modulus in `Deriv`, `jetCauchyModulusGenuineD`)**:
    For every coefficient stream $c : \mathrm{JetTy}$, majorant exponent $B : \mathrm{nat}$, and point
    $x : \mathrm{rat}$ satisfying the **per-term majorant bound** `jetTermPremise`:
    $$\forall n : \mathrm{nat},\quad |S_n(x) - S_{n+1}(x)| < 2^{B+3} \cdot \bigl(2^{-(n+1)} - 2^{-(n+2)}\bigr),$$
    derives in $\mathrm{HA}^\omega$ **by mathematical induction (`Deriv.ind`) on $d_2$** (summing the
    telescoping geometric series via `qAddLtAdd`, triangle inequality `convQLeLtTrans`, and telescoping
    cancellation) that the partial sums `tmJetEvalPoly c` are Cauchy with synthesized modulus
    $N(k) = k + (B + 3)$. -/
def jetCauchyModulusGenuineD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all JetTy (.all .nat (.all .rat
      (.imp (jetTermPremise Γ)
        (.imp (qGeomArithPremise Γ)
          (jetCauchyConcl Γ)))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI (Deriv.allI ?_)))))
  -- Synthesized Cauchy modulus witness: N(k) = k + (B + 3)
  refine Deriv.exI (τ := .nat)
    (.add (.var .here) (.succ (.succ (.succ (.var (.there (.there .here))))))) ?_
  refine Deriv.allI (Deriv.allI ?_)
  let ctx3 : List Ty := .nat :: .nat :: .nat :: .rat :: .nat :: JetTy :: Γ
  let d2 : Tm ctx3 .nat := .var .here
  let d1 : Tm ctx3 .nat := .var (.there .here)
  let k  : Tm ctx3 .nat := .var (.there (.there .here))
  let x  : Tm ctx3 .rat := .var (.there (.there (.there .here)))
  let B  : Tm ctx3 .nat := .var (.there (.there (.there (.there .here))))
  let c  : Tm ctx3 JetTy := .var (.there (.there (.there (.there (.there .here)))))
  let B3 : Tm ctx3 .nat := .succ (.succ (.succ B))
  let m  : Tm ctx3 .nat := .add (.add k B3) d1
  let innerCtx := jetCauchyGenuineInnerCtx Γ Δ
  -- Inductive invariant in d2_var (.var .here in .nat :: ctx3):
  -- |S_m(x) - S_{m + d2_var}(x)| < jetTailBound B m d2_var
  let tailInv : Formula (.nat :: ctx3) .unit :=
    let d2_v : Tm (.nat :: ctx3) .nat := .var .here
    let m_v  : Tm (.nat :: ctx3) .nat := m.wk (σ := .nat)
    let x_v  : Tm (.nat :: ctx3) .rat := x.wk (σ := .nat)
    let B_v  : Tm (.nat :: ctx3) .nat := B.wk (σ := .nat)
    let c_v  : Tm (.nat :: ctx3) JetTy := c.wk (σ := .nat)
    .eq (.qlt (.app qabsT (.qsub (jetEvalAt c_v m_v x_v) (jetEvalAt c_v (.add m_v d2_v) x_v)))
              (jetTailBound B_v m_v d2_v))
        (.succ .zero)
  have hInd : Deriv innerCtx (.all .nat tailInv) := by
    refine Deriv.ind ?_ ?_
    · -- Base case: d2 = 0
      deriv_norm
      have hAdd0 : Deriv innerCtx (.eq (.add m .zero) m) := Deriv.convAddZero m
      have hEval0 : Deriv innerCtx (.eq (jetEvalAt c (.add m .zero) x) (jetEvalAt c m x)) :=
        Deriv.congFun (Deriv.congArg (.app tmJetEvalPoly c) hAdd0) x
      have hSub0 : Deriv innerCtx
          (.eq (.qsub (jetEvalAt c m x) (jetEvalAt c (.add m .zero) x)) (.qnat .zero)) :=
        Deriv.transE (qsubCong (Deriv.eqRefl _) hEval0) (Deriv.convQSubSelf (jetEvalAt c m x))
      have hAbs0 : Deriv innerCtx
          (.eq (.app qabsT (.qsub (jetEvalAt c m x) (jetEvalAt c (.add m .zero) x)))
               (.app qabsT (.qnat .zero))) :=
        Deriv.congArg qabsT hSub0
      have hArith : Deriv innerCtx ((((qGeomArithPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)) :=
        Deriv.ax
      have hZeroPrem := Deriv.andE₁ hArith
      have hZeroInst := Deriv.allE (τ := .nat) m hZeroPrem
      deriv_norm at hZeroInst
      exact Deriv.qltEqLeft hAbs0.symmE hZeroInst
    · -- Inductive step: d2_s -> d2_s + 1, summing via qAddLtAdd
      refine Deriv.allI (Deriv.impI ?_)
      let stepCtxTy : List Ty := .nat :: ctx3
      let d2_s : Tm stepCtxTy .nat := .var .here
      let m_s  : Tm stepCtxTy .nat := m.wk (σ := .nat)
      let x_s  : Tm stepCtxTy .rat := x.wk (σ := .nat)
      let B_s  : Tm stepCtxTy .nat := B.wk (σ := .nat)
      let c_st : Tm stepCtxTy JetTy := c.wk (σ := .nat)
      let stepCtx := Ctx.cons tailInv innerCtx.wk
      have hIH : Deriv stepCtx tailInv := Deriv.ax
      have hTermPrem : Deriv stepCtx
          (((((jetTermPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)) :=
        Deriv.wk (Deriv.wk Deriv.ax)
      have hTermInst := Deriv.allE (τ := .nat) (.add m_s d2_s) hTermPrem
      deriv_norm at hTermInst
      -- Combine IH and single-term majorant bound via qAddLtAddT:
      have hSum := qAddLtAddT
        (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.add m_s d2_s) x_s)))
        (.app qabsT (.qsub (jetEvalAt c_st (.add m_s d2_s) x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)))
        (jetTailBound B_s m_s d2_s)
        (jetStepBound B_s (.add m_s d2_s))
        hIH hTermInst
      -- Apply triangle inequality on the LHS via convQLeLtTrans:
      have hArithS : Deriv stepCtx
          (((((qGeomArithPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)) :=
        Deriv.wk Deriv.ax
      have hTriPrem := Deriv.andE₁ (Deriv.andE₂ hArithS)
      have hTri1 := Deriv.allE (τ := .rat) (jetEvalAt c_st m_s x_s) hTriPrem
      deriv_norm at hTri1
      have hTri2 := Deriv.allE (τ := .rat) (jetEvalAt c_st (.add m_s d2_s) x_s) hTri1
      deriv_norm at hTri2
      have hTri3 := Deriv.allE (τ := .rat) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s) hTri2
      deriv_norm at hTri3
      have hTriStep := Deriv.convQLeLtTrans
        (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)))
        (.qadd (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.add m_s d2_s) x_s)))
               (.app qabsT (.qsub (jetEvalAt c_st (.add m_s d2_s) x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s))))
        (.qadd (jetTailBound B_s m_s d2_s) (jetStepBound B_s (.add m_s d2_s)))
        hTri3 hSum
      -- Telescope the RHS via qTelescopePremise and qltEqRight:
      have hTelPrem := Deriv.andE₁ (Deriv.andE₂ (Deriv.andE₂ hArithS))
      have hTel1 := Deriv.allE (τ := .nat) m_s hTelPrem
      deriv_norm at hTel1
      have hTel2 := Deriv.allE (τ := .nat) d2_s hTel1
      deriv_norm at hTel2
      have hTelStep := Deriv.qltEqRight hTel2 hTriStep
      -- Rewrite .succ (.add m_s d2_s) to .add m_s (.succ d2_s) on the LHS via convAddSucc:
      have hAddSucc : Deriv stepCtx (.eq (.succ (.add m_s d2_s)) (.add m_s (.succ d2_s))) :=
        (Deriv.convAddSucc m_s d2_s).symmE
      have hEvalSucc : Deriv stepCtx
          (.eq (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)
               (jetEvalAt c_st (.add m_s (.succ d2_s)) x_s)) :=
        Deriv.congFun (Deriv.congArg (.app tmJetEvalPoly c_st) hAddSucc) x_s
      have hAbsSucc : Deriv stepCtx
          (.eq (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.succ (.add m_s d2_s)) x_s)))
               (.app qabsT (.qsub (jetEvalAt c_st m_s x_s) (jetEvalAt c_st (.add m_s (.succ d2_s)) x_s)))) :=
        Deriv.congArg qabsT (qsubCong (Deriv.eqRefl _) hEvalSucc)
      exact Deriv.qltEqLeft hAbsSucc hTelStep
  -- Instantiate the d2-induction at d2:
  have hTailD2 := Deriv.allE (τ := .nat) d2 hInd
  deriv_norm at hTailD2
  -- Reassociate m = ((k + B3) + d1) = ((k + d1) + B3) inside Deriv:
  have heqM : Deriv innerCtx (.eq m (.add (.add k d1) B3)) := addSwapRightT k B3 d1
  have hTailReassoc := Deriv.qltEqRight (jetTailBoundCongM B d2 heqM) hTailD2
  -- Cancel the dyadic scale via qScaleCancelPremise and convQLtTrans:
  have hArith : Deriv innerCtx ((((qGeomArithPremise Γ).wk (σ := .nat)).wk (σ := .nat)).wk (σ := .nat)) :=
    Deriv.ax
  have hCancelPrem := Deriv.andE₂ (Deriv.andE₂ (Deriv.andE₂ hArith))
  have hCancel1 := Deriv.allE (τ := .nat) (.add k d1) hCancelPrem
  deriv_norm at hCancel1
  have hCancel2 := Deriv.allE (τ := .nat) d2 hCancel1
  deriv_norm at hCancel2
  have hLtPow := Deriv.convQLtTrans
    (.app qabsT (.qsub (jetEvalAt c m x) (jetEvalAt c (.add m d2) x)))
    (jetTailBound B (.add (.add k d1) B3) d2)
    (.app qpow2 (.add k d1))
    hTailReassoc hCancel2
  -- Fold into qclose (k + d1) and weaken to k via convQCloseMono:
  have hCloseKD1 := qcloseIntro (.add k d1) (jetEvalAt c m x) (jetEvalAt c (.add m d2) x) hLtPow
  exact Deriv.convQCloseMono k d1 (jetEvalAt c m x) (jetEvalAt c (.add m d2) x) hCloseKD1

/-! ## 5. Extracted System T Realizer, Kleene–Kreisel Continuity, and Premise Discharges -/

/-- **The Proof-Computed Extracted System T Jet Cauchy Modulus (`extractedJetCauchyModulusGenuine`)**:
    Extracted directly via `extractClosed jetCauchyModulusGenuineD` (`[propext, Quot.sound]`). -/
def extractedJetCauchyModulusGenuine (c : Nat → Q) (B : Nat) (x : Q) (k : Nat) : Nat :=
  ((((extractClosed (jetCauchyModulusGenuineD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    c B x (fun _ ↦ ()) (⟨fun _ ↦ (), ⟨fun _ _ _ ↦ (), ⟨fun _ _ ↦ (), fun _ _ ↦ ()⟩⟩⟩)) k).1

theorem extractedJetCauchyModulusGenuine_eq (c : Nat → Q) (B : Nat) (x : Q) (k : Nat) :
    extractedJetCauchyModulusGenuine c B x k = k + (B + 3) :=
  rfl

/-- **Kleene–Kreisel Continuity (`Tracked`) of `jetCauchyModulusGenuineD`**:
    The extracted Cauchy modulus functional is tracked by a continuous `Mod` tree. -/
theorem jetCauchyModulusGenuine_tracked :
    Tracked (.arrow JetTy (.arrow .nat (.arrow .rat
      (.arrow (.arrow .nat .unit)
        (.arrow (.prod (.arrow .nat .unit)
          (.prod (.arrow .rat (.arrow .rat (.arrow .rat .unit)))
            (.prod (.arrow .nat (.arrow .nat .unit))
                   (.arrow .nat (.arrow .nat .unit)))))
          (.arrow .nat (.prod .nat (.arrow .nat (.arrow .nat .unit)))))))))
      (fun _ ↦ (extractClosed (jetCauchyModulusGenuineD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) :=
  extract_tracked (jetCauchyModulusGenuineD (Γ := []) (Δ := Ctx.nil))

/-- **Certified Haskell Emission Correctness for `jetCauchyModulusGenuineD`**: -/
theorem jetCauchyModulusGenuine_hsOf_correct :
    ∃ v, HsEval (hsOf (extractClosed (jetCauchyModulusGenuineD (Γ := []) (Δ := Ctx.nil)))) [] v ∧
      Rel _ ((extractClosed (jetCauchyModulusGenuineD (Γ := []) (Δ := Ctx.nil))).eval Env.nil) v :=
  hsOf_correct (extractClosed (jetCauchyModulusGenuineD (Γ := []) (Δ := Ctx.nil))) (by decide)
    Env.nil [] (fun _ v ↦ nomatch v)

/-- **Discharging `jetTermPremise` for Every `F : AnalyticJet` on $[-1, 1]$**:
    For every exponential-type jet `F : AnalyticJet`, every point $x \in [-1, 1]$, and every degree
    $n \in \mathbb{N}$, the single-term truncation step satisfies:
    $$|S_n(x) - S_{n+1}(x)| < 2^{F.\mathrm{expBound} + 3} \cdot \bigl(2^{-(n+1)} - 2^{-(n+2)}\bigr).$$ -/
theorem AnalyticJet.satisfies_jetTermPremise (F : AnalyticJet) (x : Q)
    (hxa : Qle (Q.of (-1) 1) x = true) (hxb : Qle x (Q.ofNat 1) = true) (n : Nat) :
    Q.ltN
      (Q.abs (Q.sub (F.toJet.evalPoly n x) (F.toJet.evalPoly (n + 1) x)))
      (Q.mul (qpow2posVal (F.expBound + 3))
        (Q.sub (D.toQ (D.pow2neg (n + 1))) (D.toQ (D.pow2neg (n + 2))))) = 1 := by
  rw [Qle_eq_true_iff] at hxa hxb
  have ha_val : (Q.of (-1) 1).val = -1 := by rw [Q.val_of (-1) 1 (by decide)]; norm_num
  have hb_val : (Q.ofNat 1).val = 1 := by rw [Q.val_ofNat]; norm_num
  rw [ha_val] at hxa
  rw [hb_val] at hxb
  have hx : |x.val| ≤ 1 := abs_le.mpr ⟨hxa, hxb⟩
  rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_mul, qpow2posVal_val,
      Q.val_sub, toQ_pow2neg_val, toQ_pow2neg_val]
  have h_step : (F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + 1) x).val =
      -((F.coeff n).val * x.val ^ n) := by
    rw [F.toJet.evalPoly_succ n x]; ring
  rw [h_step, abs_neg, abs_mul, abs_pow]
  have hx_pow : |x.val| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have h_term1 : |(F.coeff n).val| * |x.val| ^ n ≤ |(F.coeff n).val| := by
    nlinarith [abs_nonneg (F.coeff n).val]
  have h_term2 := F.coeff_telescope_step n
  have h_rhs : (2 : Rat) ^ (F.expBound + 3) * (1 / (2 : Rat) ^ (n + 1) - 1 / (2 : Rat) ^ (n + 2)) =
      2 * ((2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1))) := by
    rw [show F.expBound + 3 = (F.expBound + 1) + 2 by omega,
        pow_add (2 : Rat) (F.expBound + 1) 2,
        pow_succ (2 : Rat) n, pow_succ (2 : Rat) (n + 1)]
    field_simp
    ring
  have h_pos : (0 : Rat) < (2 : Rat) ^ (F.expBound + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1)) := by
    have hp1 : (0 : Rat) < (2 : Rat) ^ (F.expBound + 1) := by positivity
    have hp2 : (1 : Rat) / (2 : Rat) ^ (n + 1) < 1 / (2 : Rat) ^ n := by
      have hp3 : (0 : Rat) < 1 / (2 : Rat) ^ (n + 1) := by positivity
      have hsplit : (1 : Rat) / (2 : Rat) ^ n = 1 / (2 : Rat) ^ (n + 1) + 1 / (2 : Rat) ^ (n + 1) := by
        rw [pow_succ (2 : Rat) n]; field_simp; ring
      linarith
    exact mul_pos hp1 (sub_pos.mpr hp2)
  linarith

/-- **Discharging `jetTermPremise` for Every `F : RadiusJet` on $[-2^{-(F.R + 1)}, 2^{-(F.R + 1)}]$**:
    For every Cauchy–Hadamard jet `F : RadiusJet`, every point $x$ in the half-radius disk
    $|x| \le 2^{-(F.R + 1)}$, and every degree $n \in \mathbb{N}$, the single-term truncation step
    satisfies `jetTermPremise` with majorant parameter $B = F.M$! -/
theorem RadiusJet.satisfies_jetTermPremise (F : RadiusJet) (x : Q)
    (hxa : Qle (Q.neg (D.toQ (D.pow2neg (F.R + 1)))) x = true)
    (hxb : Qle x (D.toQ (D.pow2neg (F.R + 1))) = true) (n : Nat) :
    Q.ltN
      (Q.abs (Q.sub (F.toJet.evalPoly n x) (F.toJet.evalPoly (n + 1) x)))
      (Q.mul (qpow2posVal (F.M + 3))
        (Q.sub (D.toQ (D.pow2neg (n + 1))) (D.toQ (D.pow2neg (n + 2))))) = 1 := by
  rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val] at hxa
  rw [Qle_eq_true_iff, toQ_pow2neg_val] at hxb
  have hx : |x.val| ≤ 1 / (2 : Rat) ^ (F.R + 1) := abs_le.mpr ⟨hxa, hxb⟩
  rw [Q.ltN_eq_one_iff, Q.val_abs, Q.val_sub, Q.val_mul, qpow2posVal_val,
      Q.val_sub, toQ_pow2neg_val, toQ_pow2neg_val]
  have h_step : (F.toJet.evalPoly n x).val - (F.toJet.evalPoly (n + 1) x).val =
      -((F.toJet.coeff n).val * x.val ^ n) := by
    rw [F.toJet.evalPoly_succ n x]; ring
  rw [h_step, abs_neg, abs_mul, abs_pow]
  have h_term := F.term_telescope_disk x hx n
  have h_rhs : (2 : Rat) ^ (F.M + 3) * (1 / (2 : Rat) ^ (n + 1) - 1 / (2 : Rat) ^ (n + 2)) =
      2 * ((2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1))) := by
    rw [show F.M + 3 = (F.M + 1) + 2 by omega,
        pow_add (2 : Rat) (F.M + 1) 2,
        pow_succ (2 : Rat) n, pow_succ (2 : Rat) (n + 1)]
    field_simp
    ring
  have h_pos : (0 : Rat) < (2 : Rat) ^ (F.M + 1) * (1 / (2 : Rat) ^ n - 1 / (2 : Rat) ^ (n + 1)) := by
    have hp1 : (0 : Rat) < (2 : Rat) ^ (F.M + 1) := by positivity
    have hp2 : (1 : Rat) / (2 : Rat) ^ (n + 1) < 1 / (2 : Rat) ^ n := by
      have hp3 : (0 : Rat) < 1 / (2 : Rat) ^ (n + 1) := by positivity
      have hsplit : (1 : Rat) / (2 : Rat) ^ n = 1 / (2 : Rat) ^ (n + 1) + 1 / (2 : Rat) ^ (n + 1) := by
        rw [pow_succ (2 : Rat) n]; field_simp; ring
      linarith
    exact mul_pos hp1 (sub_pos.mpr hp2)
  linarith

/-! ## 6. `RadiusJet` Discharges for `jetContModulusD` (`jetLipPremise`) and `jetDiffModulusD` (`jetDiffPremise`) -/

/-- Exact agreement between the `Deriv`-extracted continuity modulus `extractedJetContModulus`
    (at $B_1 = F.\mathrm{deriv}.M = F.M + F.R + 1$) and `F.omegaE1` for every `F : RadiusJet`. -/
theorem RadiusJet.extractedJetContModulus_eq_omegaE1 (F : RadiusJet) (x y : Q) (k : Nat) :
    extractedJetContModulus F.toJet.coeff F.deriv.M x y k = F.omegaE1 k := by
  change k + ((F.M + F.R + 1) + 1) = (F.M + F.R + 1) + 1 + k
  omega

/-- **Discharging `jetLipPremise` for Every `F : RadiusJet` on $[-2^{-(F.R + 3)}, 2^{-(F.R + 3)}]$**:
    For every Cauchy–Hadamard jet `F : RadiusJet` and all $x, y$ in its `toE1` disk
    $[-2^{-(F.R + 3)}, 2^{-(F.R + 3)}]$, every polynomial truncation `F.toJet.evalPoly m`
    satisfies `jetLipPremise` with Lipschitz exponent $B_1 = F.\mathrm{deriv}.M$. -/
theorem RadiusJet.satisfies_jetLipPremise (F : RadiusJet) (x y : Q)
    (hxa : Qle F.toE1.a x = true) (hxb : Qle x F.toE1.b = true)
    (hya : Qle F.toE1.a y = true) (hyb : Qle y F.toE1.b = true)
    (m : Nat) :
    Q.ltN (Q.mul (qpow2posVal (F.deriv.M + 1)) (Q.abs (Q.sub x y)))
          (Q.abs (Q.sub (F.toJet.evalPoly m x) (F.toJet.evalPoly m y))) = 0 := by
  dsimp [RadiusJet.toE1] at hxa hxb hya hyb
  rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val] at hxa hya
  rw [Qle_eq_true_iff, toQ_pow2neg_val] at hxb hyb
  rw [Q.ltN_eq_zero_iff, Q.val_mul, qpow2posVal_val, Q.val_abs, Q.val_sub, Q.val_abs, Q.val_sub]
  let r : Q := D.toQ (D.pow2neg (F.R + 3))
  have hr_val : |r.val| = 1 / (2 : Rat) ^ (F.R + 3) := by
    dsimp [r]; rw [toQ_pow2neg_val, abs_of_pos (by positivity)]
  have hr_le : |r.val| ≤ 1 / (2 : Rat) ^ (F.R + 2) := by
    rw [hr_val]; exact inv_pow_le (by omega)
  have hx : |x.val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hxa, hxb⟩
  have hy : |y.val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hya, hyb⟩
  exact F.evalPoly_lip_disk r x y hr_le hx hy m

/-- Exact agreement between the `Deriv`-extracted differentiability modulus `extractedJetDiffModulus`
    (at $B_2 = F.\mathrm{deriv.mulIdxSucc}.M + (F.R + 3)$) and `F.deltaE1` for every `F : RadiusJet`. -/
theorem RadiusJet.extractedJetDiffModulus_eq_deltaE1 (F : RadiusJet) (x h : Q) (k : Nat) :
    extractedJetDiffModulus F.toJet.coeff (F.deriv.mulIdxSucc.M + (F.R + 3)) x h k = F.deltaE1 k := by
  change k + ((F.M + F.R + 1 + 1 + (F.R + 3)) + 1) = ((F.M + F.R + 1 + 1) + 1 + (F.R + 3)) + k
  omega

/-- **Discharging `jetDiffPremise` for Every `F : RadiusJet` on $[-2^{-(F.R + 3)}, 2^{-(F.R + 3)}]$**:
    For every Cauchy–Hadamard jet `F : RadiusJet` and all $x, x + h$ in its `toE1` disk
    $[-2^{-(F.R + 3)}, 2^{-(F.R + 3)}]$ ($h \ne 0$), every difference quotient satisfies
    `jetDiffPremise` with exponent $B_2 = F.\mathrm{deriv.mulIdxSucc}.M + (F.R + 3)$. -/
theorem RadiusJet.satisfies_jetDiffPremise (F : RadiusJet) (x h : Q)
    (hxa : Qle F.toE1.a x = true) (hxb : Qle x F.toE1.b = true)
    (hha : Qle F.toE1.a (Q.add x h) = true) (hhb : Qle (Q.add x h) F.toE1.b = true)
    (hnum : h.num ≠ 0) (m : Nat) :
    Q.ltN (Q.mul (qpow2posVal (F.deriv.mulIdxSucc.M + (F.R + 3) + 1)) (Q.abs (Q.sub h (Q.ofNat 0))))
          (Q.abs (Q.sub
            (Q.div (Q.sub (F.toJet.evalPoly (m + 1) (Q.add x h)) (F.toJet.evalPoly (m + 1) x)) h)
            (F.deriv.toJet.evalPoly m x))) = 0 := by
  dsimp [RadiusJet.toE1] at hxa hxb hha hhb
  rw [Qle_eq_true_iff, Q.val_neg, toQ_pow2neg_val] at hxa hha
  rw [Qle_eq_true_iff, toQ_pow2neg_val] at hxb hhb
  rw [Q.ltN_eq_zero_iff, Q.val_mul, qpow2posVal_val, Q.val_abs, Q.val_sub,
      Q.val_abs, Q.val_sub, Q.val_ofNat]
  push_cast
  rw [sub_zero]
  let r : Q := D.toQ (D.pow2neg (F.R + 3))
  have hr_pos : 0 < r.val := by dsimp [r]; rw [toQ_pow2neg_val]; positivity
  have hr_val : |r.val| = 1 / (2 : Rat) ^ (F.R + 3) := by
    dsimp [r]; rw [toQ_pow2neg_val, abs_of_pos (by positivity)]
  have hx : |x.val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hxa, hxb⟩
  have hxh : |(Q.add x h).val| ≤ |r.val| := by rw [hr_val]; exact abs_le.mpr ⟨hha, hhb⟩
  have h_dq := F.evalPoly_diff_disk m r x h hr_pos (le_of_eq hr_val) hx hxh hnum
  have h_div_r : |h.val| / |r.val| = (2 : Rat) ^ (F.R + 3) * |h.val| := by
    rw [hr_val]; field_simp
  rw [h_div_r] at h_dq
  have h_combine : (2 : Rat) ^ (F.deriv.mulIdxSucc.M + 1) * ((2 : Rat) ^ (F.R + 3) * |h.val|) =
      (2 : Rat) ^ (F.deriv.mulIdxSucc.M + (F.R + 3) + 1) * |h.val| := by
    rw [show F.deriv.mulIdxSucc.M + (F.R + 3) + 1 = (F.deriv.mulIdxSucc.M + 1) + (F.R + 3) by omega,
        pow_add (2 : Rat) (F.deriv.mulIdxSucc.M + 1) (F.R + 3)]
    ring
  linarith

#guard (List.range 5).map
  (extractedJetCauchyModulusGenuine AnalyticJet.exp.toJet.coeff AnalyticJet.exp.expBound (Q.of 1 2)) ==
  [5, 6, 7, 8, 9]

#guard (List.range 5).map
  (extractedJetCauchyModulusGenuine RadiusJet.geomOneMinusX.toJet.coeff RadiusJet.geomOneMinusX.M (Q.of 1 4)) ==
  [3, 4, 5, 6, 7]

#guard (List.range 5).map
  (extractedJetContModulus RadiusJet.tan.toJet.coeff RadiusJet.tan.deriv.M (Q.of 1 16) (Q.of 1 32)) ==
  (List.range 5).map RadiusJet.tan.omegaE1

#guard (List.range 5).map
  (extractedJetDiffModulus RadiusJet.tan.toJet.coeff (RadiusJet.tan.deriv.mulIdxSucc.M + (RadiusJet.tan.R + 3)) (Q.of 1 16) (Q.of 1 64)) ==
  (List.range 5).map RadiusJet.tan.deltaE1

#print axioms jetCauchyModulusGenuineD
#print axioms extractedJetCauchyModulusGenuine
#print axioms jetCauchyModulusGenuine_tracked
#print axioms jetCauchyModulusGenuine_hsOf_correct
#print axioms AnalyticJet.satisfies_jetTermPremise
#print axioms RadiusJet.satisfies_jetTermPremise
#print axioms RadiusJet.satisfies_jetLipPremise
#print axioms RadiusJet.satisfies_jetDiffPremise

end HAomega
