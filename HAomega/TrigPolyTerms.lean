/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.JetModuliComputed

/-!
# The Fourier layer in System T

Closed-universe pillar 6, second half. `TrigPoly.lean` defines trigonometric
polynomials and their operations at the value level. Here the operations are
System T terms, so they can occur inside derivations and be extracted, emitted
and tracked like every other term.

A polynomial of degree `≤ N` is encoded as the stream `j ↦ c_{j−N}`
(`j ≤ 2N`) of pairs `(Re, Im)` of rationals, type `TrigTy`. The terms
`tmTrigAdd`, `tmTrigDeriv N`, `tmTrigInteg N`, `tmTrigMul N M` and
`tmTrigToJet N` are specified by the pinned theorems below: on encoded inputs
they evaluate to the encoding of the value-level operation (as rational values).
The terms themselves are implementation; the theorems are the contract.
-/

namespace HAomega

/-- Encoded trigonometric polynomials: `j ↦ (Re c_{j−N}, Im c_{j−N})`. -/
abbrev TrigTy : Ty := .arrow .nat (.prod .rat .rat)

/-- The encoding of `p` at degree bound `N`. -/
def TrigPoly.enc (N : Nat) (p : TrigPoly) : Nat → Q × Q :=
  fun j ↦ let z := p.coeff ((j : Int) - N); (z.re, z.im)

/-- Value equality of encoded streams on the indices `j ≤ 2N`. -/
def TrigEqV (N : Nat) (u v : Nat → Q × Q) : Prop :=
  ∀ j ≤ 2 * N, (u j).1.val = (v j).1.val ∧ (u j).2.val = (v j).2.val

/-- The complex zero `(0, 0)` as a System T term. -/
def tmCZero {Γ : List Ty} : Tm Γ (.prod .rat .rat) :=
  .pair (.qnat .zero) (.qnat .zero)

/-- Complex addition `(a₁ + b₁, a₂ + b₂)` on rational pairs in System T. -/
def tmCAdd {Γ : List Ty} (z w : Tm Γ (.prod .rat .rat)) : Tm Γ (.prod .rat .rat) :=
  .pair (.qadd (.fst z) (.fst w)) (.qadd (.snd z) (.snd w))

/-- Complex multiplication `(a₁b₁ - a₂b₂, a₁b₂ + a₂b₁)` on rational pairs in System T. -/
def tmCMul {Γ : List Ty} (z w : Tm Γ (.prod .rat .rat)) : Tm Γ (.prod .rat .rat) :=
  .pair (.qsub (.qmul (.fst z) (.fst w)) (.qmul (.snd z) (.snd w)))
        (.qadd (.qmul (.fst z) (.snd w)) (.qmul (.snd z) (.fst w)))

/-- Single guarded convolution summand at index `j` for output index `n` with second degree bound `M`. -/
def tmTrigMulTerm (M : Nat) {Γ : List Ty}
    (u v : Tm Γ TrigTy) (n j : Tm Γ .nat) : Tm Γ (.prod .rat .rat) :=
  .recNat (tmCMul (.app u j) (.app v (tmNatSub n j)))
    (.lam (.lam tmCZero))
    (.add (tmNatSub j n) (tmNatSub (tmNatSub n j) (natTm (2 * M))))

/-- Complex power `(i · k)^n` in System T by recursion on `n`. -/
def tmIKPow {Γ : List Ty} (k : Tm Γ .rat) (n : Tm Γ .nat) : Tm Γ (.prod .rat .rat) :=
  .recNat (.pair (.qnat (.succ .zero)) (.qnat .zero))
    (.lam (.lam (tmCMul (.var .here) (.pair (.qnat .zero) (k.wk.wk)))))
    n

/-- Factorial `n!` as a rational term in System T. -/
def tmQFact {Γ : List Ty} (n : Tm Γ .nat) : Tm Γ .rat :=
  .recNat (.qnat (.succ .zero))
    (.lam (.lam (.qmul (.qnat (.succ (.var (.there .here)))) (.var .here))))
    n

def tmTrigAdd {Γ : List Ty} : Tm Γ (.arrow TrigTy (.arrow TrigTy TrigTy)) :=
  .lam (.lam (.lam (
    let u : Tm (.nat :: TrigTy :: TrigTy :: Γ) TrigTy := .var (.there (.there .here))
    let v : Tm (.nat :: TrigTy :: TrigTy :: Γ) TrigTy := .var (.there .here)
    let j : Tm (.nat :: TrigTy :: TrigTy :: Γ) .nat := .var .here
    tmCAdd (.app u j) (.app v j)
  )))

def tmTrigDeriv (N : Nat) {Γ : List Ty} : Tm Γ (.arrow TrigTy TrigTy) :=
  .lam (.lam (
    let u : Tm (.nat :: TrigTy :: Γ) TrigTy := .var (.there .here)
    let j : Tm (.nat :: TrigTy :: Γ) .nat := .var .here
    let k : Tm (.nat :: TrigTy :: Γ) .rat := .qsub (.qnat j) (.qnat (natTm N))
    let z : Tm (.nat :: TrigTy :: Γ) (.prod .rat .rat) := .app u j
    .pair (.qsub (.qnat .zero) (.qmul k (.snd z))) (.qmul k (.fst z))
  ))

def tmTrigInteg (N : Nat) {Γ : List Ty} : Tm Γ (.arrow TrigTy TrigTy) :=
  .lam (.lam (
    let j_out : Tm (.nat :: TrigTy :: Γ) .nat := .var .here
    let u_in : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) TrigTy :=
      .var (.there (.there (.there .here)))
    let j_in : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) .nat :=
      .var (.there (.there .here))
    let k : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) .rat :=
      .qsub (.qnat j_in) (.qnat (natTm N))
    let z : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) (.prod .rat .rat) :=
      .app u_in j_in
    .recNat tmCZero
      (.lam (.lam (.pair (.qdiv (.snd z) k)
                         (.qsub (.qnat .zero) (.qdiv (.fst z) k)))))
      (.add (tmNatSub j_out (natTm N)) (tmNatSub (natTm N) j_out))
  ))

def tmTrigMul (N M : Nat) {Γ : List Ty} : Tm Γ (.arrow TrigTy (.arrow TrigTy TrigTy)) :=
  .lam (.lam (.lam (
    let u : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: TrigTy :: Γ) TrigTy :=
      .var (.there (.there (.there (.there .here))))
    let v : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: TrigTy :: Γ) TrigTy :=
      .var (.there (.there (.there .here)))
    let n : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: TrigTy :: Γ) .nat :=
      .var (.there (.there .here))
    let j : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: TrigTy :: Γ) .nat :=
      .var (.there .here)
    let acc : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: TrigTy :: Γ) (.prod .rat .rat) :=
      .var .here
    .recNat tmCZero
      (.lam (.lam (tmCAdd acc (tmTrigMulTerm M u v n j))))
      (.succ (natTm (2 * N)))
  )))

def tmTrigToJet (N : Nat) {Γ : List Ty} : Tm Γ (.arrow TrigTy JetTy) :=
  .lam (.lam (
    let u : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) TrigTy :=
      .var (.there (.there (.there .here)))
    let n_in : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) .nat :=
      .var (.there (.there .here))
    let j : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) .nat :=
      .var (.there .here)
    let acc : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) (.prod .rat .rat) :=
      .var .here
    let k : Tm ((.prod .rat .rat) :: .nat :: .nat :: TrigTy :: Γ) .rat :=
      .qsub (.qnat j) (.qnat (natTm N))
    let n_out : Tm (.nat :: TrigTy :: Γ) .nat := .var .here
    .qdiv
      (.fst (.recNat tmCZero
        (.lam (.lam (tmCAdd acc (tmCMul (.app u j) (tmIKPow k n_in)))))
        (.succ (natTm (2 * N)))))
      (tmQFact n_out)
  ))

/-- Map a pair `Q × Q` to its `TrigPoly.CRat` value. -/
def pairToCRat (z : Q × Q) : TrigPoly.CRat := ⟨z.1.val, z.2.val⟩

/-- Value equality of two `Q × Q` pairs is equality in `TrigPoly.CRat`. -/
theorem pairToCRat_ext_iff (u v : Q × Q) :
    (u.1.val = v.1.val ∧ u.2.val = v.2.val) ↔ pairToCRat u = pairToCRat v :=
  ⟨fun ⟨h1, h2⟩ ↦ TrigPoly.CRat.ext h1 h2,
   fun h ↦ ⟨congrArg TrigPoly.CRat.re h, congrArg TrigPoly.CRat.im h⟩⟩

/-- Evaluating `tmCZero` maps to `0` in `TrigPoly.CRat`. -/
theorem pairToCRat_tmCZero {Γ : List Ty} (e : Env Γ) :
    pairToCRat ((tmCZero (Γ := Γ)).eval e) = 0 := by
  ext <;> exact Q.val_ofNat 0

/-- Evaluating `tmCAdd` commutes with addition in `TrigPoly.CRat`. -/
theorem pairToCRat_tmCAdd {Γ : List Ty} (z w : Tm Γ (.prod .rat .rat)) (e : Env Γ) :
    pairToCRat ((tmCAdd z w).eval e) = pairToCRat (z.eval e) + pairToCRat (w.eval e) := by
  ext <;> exact Q.val_add _ _

/-- Evaluating `tmCMul` commutes with multiplication in `TrigPoly.CRat`. -/
theorem pairToCRat_tmCMul {Γ : List Ty} (z w : Tm Γ (.prod .rat .rat)) (e : Env Γ) :
    pairToCRat ((tmCMul z w).eval e) = pairToCRat (z.eval e) * pairToCRat (w.eval e) := by
  ext
  · show (Q.sub (Q.mul (z.eval e).1 (w.eval e).1) (Q.mul (z.eval e).2 (w.eval e).2)).val = _
    rw [Q.val_sub, Q.val_mul, Q.val_mul]
    rfl
  · show (Q.add (Q.mul (z.eval e).1 (w.eval e).2) (Q.mul (z.eval e).2 (w.eval e).1)).val = _
    rw [Q.val_add, Q.val_mul, Q.val_mul]
    rfl

/-- The rational difference `Q.sub (Q.ofNat j) (Q.ofNat N)` has value `((j : Int) - N : Rat)`. -/
theorem qsub_ofNat_val (j N : Nat) :
    (Q.sub (Q.ofNat j) (Q.ofNat N)).val = (((j : Int) - N : Int) : Rat) := by
  rw [Q.val_sub, Q.val_ofNat, Q.val_ofNat]
  push_cast
  rfl

/-- `TrigPoly.toCRat` commutes with `TrigPoly.add` at every frequency `k`. -/
theorem toCRat_add_coeff (p q : TrigPoly) (k : Int) :
    TrigPoly.toCRat ((p.add q).coeff k) =
      TrigPoly.toCRat (p.coeff k) + TrigPoly.toCRat (q.coeff k) := by
  by_cases h : k.natAbs ≤ max p.deg q.deg
  · have h1 : (p.add q).coeff k = CQ.add (p.coeff k) (q.coeff k) := if_pos h
    rw [h1, TrigPoly.toCRat_add]
  · have hp0 : ¬ (k.natAbs ≤ p.deg) := fun hp ↦ h (le_trans hp (Nat.le_max_left _ _))
    have hq0 : ¬ (k.natAbs ≤ q.deg) := fun hq ↦ h (le_trans hq (Nat.le_max_right _ _))
    have h1 : (p.add q).coeff k = CQ.zero := if_neg h
    have h2 : p.coeff k = CQ.zero := if_neg hp0
    have h3 : q.coeff k = CQ.zero := if_neg hq0
    rw [h1, h2, h3, TrigPoly.toCRat_zero, add_zero]

theorem tmTrigAdd_spec (N : Nat) (p q : TrigPoly) (hp : p.deg ≤ N) (hq : q.deg ≤ N) :
    TrigEqV N ((tmTrigAdd (Γ := [])).eval Env.nil (p.enc N) (q.enc N)) ((p.add q).enc N) := by
  have _ := hp
  have _ := hq
  intro j _
  rw [pairToCRat_ext_iff]
  let e : Env [.nat, TrigTy, TrigTy] :=
    Env.cons (σ := .nat) j (Env.cons (σ := TrigTy) (q.enc N) (Env.cons (σ := TrigTy) (p.enc N) Env.nil))
  change pairToCRat ((tmCAdd (.app (.var (.there (.there .here))) (.var .here))
    (.app (.var (.there .here)) (.var .here))).eval e) =
    TrigPoly.toCRat ((p.add q).coeff ((j : Int) - N))
  rw [pairToCRat_tmCAdd, toCRat_add_coeff]
  rfl

theorem tmTrigDeriv_spec (N : Nat) (p : TrigPoly) (hp : p.deg ≤ N) :
    TrigEqV N ((tmTrigDeriv N (Γ := [])).eval Env.nil (p.enc N)) (p.deriv.enc N) := by
  let _ := hp
  intro j _
  rw [pairToCRat_ext_iff]
  let e : Env [.nat, TrigTy] :=
    Env.cons (σ := .nat) j (Env.cons (σ := TrigTy) (p.enc N) Env.nil)
  have hN : (natTm N).eval e = N := natTm_eval e N
  change pairToCRat
    (Q.sub (Q.ofNat 0) (Q.mul (Q.sub (Q.ofNat j) (Q.ofNat ((natTm N).eval e))) (p.enc N j).2),
     Q.mul (Q.sub (Q.ofNat j) (Q.ofNat ((natTm N).eval e))) (p.enc N j).1) =
    TrigPoly.toCRat (p.deriv.coeff ((j : Int) - N))
  rw [hN, TrigPoly.toCRat_deriv_coeff]
  ext
  · show (Q.sub (Q.ofNat 0) (Q.mul (Q.sub (Q.ofNat j) (Q.ofNat N)) (p.enc N j).2)).val = _
    rw [Q.val_sub, Q.val_ofNat, Q.val_mul, qsub_ofNat_val]
    dsimp [TrigPoly.ikCRat, TrigPoly.toCRat, TrigPoly.enc]
    ring
  · show (Q.mul (Q.sub (Q.ofNat j) (Q.ofNat N)) (p.enc N j).1).val = _
    rw [Q.val_mul, qsub_ofNat_val]
    dsimp [TrigPoly.ikCRat, TrigPoly.toCRat, TrigPoly.enc]
    ring

/-- `TrigPoly.toCRat` of `(p.integ).coeff k` for `k ≠ 0` is `⟨(p.coeff k).im / k, -(p.coeff k).re / k⟩`. -/
theorem toCRat_integ_coeff_ne (p : TrigPoly) {k : Int} (hk : k ≠ 0) :
    TrigPoly.toCRat (p.integ.coeff k) =
      ⟨(p.coeff k).im.val / (k : Rat), -((p.coeff k).re.val / (k : Rat))⟩ := by
  by_cases hdeg : k.natAbs ≤ p.deg
  · have h1 : p.integ.coeff k =
        if k = 0 then CQ.zero
        else CQ.mul ⟨Q.zero, Q.sub Q.zero (Q.invInt k)⟩ (p.coeff k) := if_pos hdeg
    rw [h1, if_neg hk, TrigPoly.toCRat_mul]
    ext
    · show (Q.zero.val * (p.coeff k).re.val -
        (Q.sub Q.zero (Q.invInt k)).val * (p.coeff k).im.val) = _
      rw [Q.val_zero, Q.val_sub, Q.val_zero, TrigPoly.invInt_val hk]
      ring
    · show (Q.zero.val * (p.coeff k).im.val +
        (Q.sub Q.zero (Q.invInt k)).val * (p.coeff k).re.val) = _
      rw [Q.val_zero, Q.val_sub, Q.val_zero, TrigPoly.invInt_val hk]
      ring
  · have h1 : p.integ.coeff k = CQ.zero := if_neg hdeg
    have h2 : p.coeff k = CQ.zero := if_neg hdeg
    rw [h1, h2, TrigPoly.toCRat_zero]
    ext
    · show (0 : Rat) = Q.zero.val / (k : Rat)
      rw [Q.val_zero, zero_div]
    · show (0 : Rat) = -(Q.zero.val / (k : Rat))
      rw [Q.val_zero, zero_div, neg_zero]

theorem tmTrigInteg_spec (N : Nat) (p : TrigPoly) (hp : p.deg ≤ N) :
    TrigEqV N ((tmTrigInteg N (Γ := [])).eval Env.nil (p.enc N)) (p.integ.enc N) := by
  let _ := hp
  intro j _
  rw [pairToCRat_ext_iff]
  let e : Env [.nat, TrigTy] :=
    Env.cons (σ := .nat) j (Env.cons (σ := TrigTy) (p.enc N) Env.nil)
  have hscrut : ((Tm.add (tmNatSub (.var .here) (natTm N)) (tmNatSub (natTm N) (.var .here))).eval e) =
      (j - N) + (N - j) := by
    change (tmNatSub (.var .here) (natTm N)).eval e + (tmNatSub (natTm N) (.var .here)).eval e = _
    rw [tmNatSub_eval, tmNatSub_eval, natTm_eval]
    rfl
  let stepFn : Nat → Q × Q → Q × Q := fun m acc ↦
    let em : Env ((.prod .rat .rat) :: .nat :: [.nat, TrigTy]) :=
      Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) m e)
    (Q.div (p.enc N j).2 (Q.sub (Q.ofNat j) (Q.ofNat ((natTm N).eval em))),
     Q.sub (Q.ofNat 0)
       (Q.div (p.enc N j).1 (Q.sub (Q.ofNat j) (Q.ofNat ((natTm N).eval em)))))
  change pairToCRat (Nat.rec (motive := fun _ ↦ Q × Q)
    ((tmCZero (Γ := [.nat, TrigTy])).eval e) stepFn
    ((Tm.add (tmNatSub (.var .here) (natTm N)) (tmNatSub (natTm N) (.var .here))).eval e)) =
    TrigPoly.toCRat (p.integ.coeff ((j : Int) - N))
  rw [hscrut]
  by_cases hj : j = N
  · subst hj
    rw [Nat.sub_self, Nat.add_zero]
    change pairToCRat ((tmCZero (Γ := [.nat, TrigTy])).eval e) =
      TrigPoly.toCRat (p.integ.coeff ((j : Int) - j))
    rw [pairToCRat_tmCZero, Int.sub_self]
    have h0 : p.integ.coeff 0 = CQ.zero := by
      unfold TrigPoly.coeff TrigPoly.integ
      split_ifs <;> rfl
    rw [h0, TrigPoly.toCRat_zero]
  · have hm : (j - N) + (N - j) = ((j - N) + (N - j) - 1) + 1 := by omega
    rw [hm]
    change pairToCRat (stepFn ((j - N) + (N - j) - 1) _) = _
    dsimp only [stepFn]
    rw [natTm_eval]
    have hk_ne : ((j : Int) - N : Int) ≠ 0 := by omega
    have hk_val : (Q.sub (Q.ofNat j) (Q.ofNat N)).val = (((j : Int) - N : Int) : Rat) :=
      qsub_ofNat_val j N
    have hk_num : (Q.sub (Q.ofNat j) (Q.ofNat N)).num ≠ 0 := by
      apply Q.num_ne_zero_of_val_ne_zero
      rw [hk_val]
      exact Int.cast_ne_zero.mpr hk_ne
    rw [toCRat_integ_coeff_ne p hk_ne]
    ext
    · show (Q.div (p.enc N j).2 (Q.sub (Q.ofNat j) (Q.ofNat N))).val = _
      rw [Q.val_div _ _ hk_num, hk_val]
      rfl
    · show (Q.sub (Q.ofNat 0) (Q.div (p.enc N j).1 (Q.sub (Q.ofNat j) (Q.ofNat N)))).val = _
      rw [Q.val_sub, Q.val_ofNat, Q.val_div _ _ hk_num, hk_val]
      dsimp [TrigPoly.enc]
      ring

/-- Evaluating `tmTrigMulTerm M` on `p.enc N` and `q.enc M` at `(n, j)` gives `p_j * q_{n-j}` in `TrigPoly.CRat`. -/
theorem pairToCRat_tmTrigMulTerm_eval (N M : Nat) (p q : TrigPoly) (hq : q.deg ≤ M)
    (n j : Nat) {Γ : List Ty} (u v : Tm Γ TrigTy) (tn tj : Tm Γ .nat) (e : Env Γ)
    (hu : u.eval e = p.enc N) (hv : v.eval e = q.enc M)
    (hn : tn.eval e = n) (hj : tj.eval e = j) :
    pairToCRat ((tmTrigMulTerm M u v tn tj).eval e) =
      TrigPoly.toCRat (p.coeff ((j : Int) - N)) *
        TrigPoly.toCRat (q.coeff (((n : Int) - (N + M)) - ((j : Int) - N))) := by
  have hscrut : ((Tm.add (tmNatSub tj tn) (tmNatSub (tmNatSub tn tj) (natTm (2 * M)))).eval e) =
      (j - n) + ((n - j) - 2 * M) := by
    change (tmNatSub tj tn).eval e + (tmNatSub (tmNatSub tn tj) (natTm (2 * M))).eval e = _
    rw [tmNatSub_eval, tmNatSub_eval, tmNatSub_eval, natTm_eval, hn, hj]
  unfold tmTrigMulTerm
  change pairToCRat (Nat.rec (motive := fun _ ↦ Q × Q)
    ((tmCMul (.app u tj) (.app v (tmNatSub tn tj))).eval e)
    (fun m acc ↦ (tmCZero (Γ := (.prod .rat .rat) :: .nat :: Γ)).eval
      (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) m e)))
    ((Tm.add (tmNatSub tj tn) (tmNatSub (tmNatSub tn tj) (natTm (2 * M)))).eval e)) = _
  rw [hscrut]
  rcases Nat.eq_zero_or_pos ((j - n) + ((n - j) - 2 * M)) with h0 | hpos
  · rw [h0]
    change pairToCRat ((tmCMul (.app u tj) (.app v (tmNatSub tn tj))).eval e) = _
    rw [pairToCRat_tmCMul]
    have hsub : (tmNatSub tn tj).eval e = n - j := by
      rw [tmNatSub_eval, hn, hj]
    have h1 : (Tm.app u tj).eval e = p.enc N j := by
      change (u.eval e) (tj.eval e) = p.enc N j
      rw [hu, hj]
    have h2 : (Tm.app v (tmNatSub tn tj)).eval e = q.enc M (n - j) := by
      change (v.eval e) ((tmNatSub tn tj).eval e) = q.enc M (n - j)
      rw [hv, hsub]
    rw [h1, h2]
    have hidx : ((n - j : Nat) : Int) - M = ((n : Int) - (N + M)) - ((j : Int) - N) := by omega
    change TrigPoly.toCRat (p.coeff ((j : Int) - N)) *
      TrigPoly.toCRat (q.coeff (((n - j : Nat) : Int) - M)) = _
    rw [hidx]
  · have hm : (j - n) + ((n - j) - 2 * M) = ((j - n) + ((n - j) - 2 * M) - 1) + 1 := by omega
    rw [hm]
    change pairToCRat ((tmCZero (Γ := (.prod .rat .rat) :: .nat :: Γ)).eval _) = _
    rw [pairToCRat_tmCZero]
    have hq_out : ¬ ((((n : Int) - (N + M)) - ((j : Int) - N)).natAbs ≤ q.deg) := by omega
    have hq0 : q.coeff (((n : Int) - (N + M)) - ((j : Int) - N)) = CQ.zero := if_neg hq_out
    rw [hq0, TrigPoly.toCRat_zero, mul_zero]

/-- Evaluating the `recNat` convolution sum inside `tmTrigMul N M` up to `r` yields the partial sum in `TrigPoly.CRat`. -/
theorem tmTrigMul_rec_val (N M : Nat) (p q : TrigPoly) (hq : q.deg ≤ M) (n : Nat) (r : Nat) :
    let e : Env [.nat, TrigTy, TrigTy] :=
      Env.cons (σ := .nat) n (Env.cons (σ := TrigTy) (q.enc M) (Env.cons (σ := TrigTy) (p.enc N) Env.nil))
    let step : Tm ((.prod .rat .rat) :: .nat :: [.nat, TrigTy, TrigTy]) (.prod .rat .rat) :=
      tmCAdd (.var .here)
        (tmTrigMulTerm M
          (.var (.there (.there (.there (.there .here)))))
          (.var (.there (.there (.there .here))))
          (.var (.there (.there .here)))
          (.var (.there .here)))
    pairToCRat (Nat.rec (motive := fun _ ↦ Q × Q)
      ((tmCZero (Γ := [.nat, TrigTy, TrigTy])).eval e)
      (fun j acc ↦ step.eval (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
      r) =
    ∑ j ∈ Finset.range r,
      TrigPoly.toCRat (p.coeff ((j : Int) - N)) *
        TrigPoly.toCRat (q.coeff (((n : Int) - (N + M)) - ((j : Int) - N))) := by
  let e : Env [.nat, TrigTy, TrigTy] :=
    Env.cons (σ := .nat) n (Env.cons (σ := TrigTy) (q.enc M) (Env.cons (σ := TrigTy) (p.enc N) Env.nil))
  let step : Tm ((.prod .rat .rat) :: .nat :: [.nat, TrigTy, TrigTy]) (.prod .rat .rat) :=
    tmCAdd (.var .here)
      (tmTrigMulTerm M
        (.var (.there (.there (.there (.there .here)))))
        (.var (.there (.there (.there .here))))
        (.var (.there (.there .here)))
        (.var (.there .here)))
  induction r with
  | zero =>
    rw [Finset.sum_range_zero]
    exact pairToCRat_tmCZero e
  | succ j ih =>
    let prev := Nat.rec (motive := fun _ ↦ Q × Q)
      ((tmCZero (Γ := [.nat, TrigTy, TrigTy])).eval e)
      (fun j acc ↦ step.eval (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
      j
    let ej : Env ((.prod .rat .rat) :: .nat :: [.nat, TrigTy, TrigTy]) :=
      Env.cons (σ := .prod .rat .rat) prev (Env.cons (σ := .nat) j e)
    change pairToCRat (step.eval ej) = _
    dsimp only [step]
    rw [pairToCRat_tmCAdd, Finset.sum_range_succ, ← ih]
    congr 1
    exact pairToCRat_tmTrigMulTerm_eval N M p q hq n j
      (.var (.there (.there (.there (.there .here)))))
      (.var (.there (.there (.there .here))))
      (.var (.there (.there .here)))
      (.var (.there .here))
      ej rfl rfl rfl rfl

/-- Summing `g ((j : Int) - N)` over `j ∈ Finset.range (2 * N + 1)` equals summing `g k` over `Finset.Icc (-N) N`. -/
theorem sum_range_sub_eq_sum_Icc {β : Type} [AddCommMonoid β] (N : Nat) (g : Int → β) :
    (∑ j ∈ Finset.range (2 * N + 1), g ((j : Int) - N)) =
      ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int), g k := by
  rw [← TrigPoly.sum_range_eq_sum_Icc N g]
  unfold TrigPoly.range
  rw [TrigPoly.coe_list_nat_int, List.map_map, List.map_map]
  rfl

/-- For `p.deg ≤ N`, summing `toCRat (p.coeff k) * f k` over `Icc (-N) N` equals summing over `Icc (-p.deg) p.deg`. -/
theorem sum_Icc_deg_le (N : Nat) (p : TrigPoly) (hp : p.deg ≤ N) (f : Int → TrigPoly.CRat) :
    (∑ k ∈ Finset.Icc (-(N : Int)) (N : Int), TrigPoly.toCRat (p.coeff k) * f k) =
      ∑ k ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int), TrigPoly.toCRat (p.coeff k) * f k := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  · intro k _ hnot
    rw [Finset.mem_Icc] at hnot
    have hout : ¬ (k.natAbs ≤ p.deg) := by omega
    have hc0 : p.coeff k = CQ.zero := if_neg hout
    rw [hc0, TrigPoly.toCRat_zero, zero_mul]

/-- `TrigPoly.toCRat` of `((p.mul q).coeff k)` equals the convolution sum over `Icc (-p.deg) p.deg`. -/
theorem toCRat_mul_coeff (p q : TrigPoly) (k : Int) :
    TrigPoly.toCRat ((p.mul q).coeff k) =
      ∑ k1 ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
        TrigPoly.toCRat (p.coeff k1) * TrigPoly.toCRat (q.coeff (k - k1)) := by
  by_cases h : k.natAbs ≤ p.deg + q.deg
  · have h1 : (p.mul q).coeff k = (p.mul q).c k := if_pos h
    rw [h1]
    dsimp [TrigPoly.mul]
    rw [TrigPoly.toCRat_foldl_range]
    refine Finset.sum_congr rfl fun k1 _ ↦ ?_
    rw [TrigPoly.toCRat_mul]
  · have h1 : (p.mul q).coeff k = CQ.zero := if_neg h
    rw [h1, TrigPoly.toCRat_zero]
    symm
    refine Finset.sum_eq_zero fun k1 hk1 ↦ ?_
    rw [Finset.mem_Icc] at hk1
    have hq_out : ¬ ((k - k1).natAbs ≤ q.deg) := by omega
    have hq0 : q.coeff (k - k1) = CQ.zero := if_neg hq_out
    rw [hq0, TrigPoly.toCRat_zero, mul_zero]

theorem tmTrigMul_spec (N M : Nat) (p q : TrigPoly) (hp : p.deg ≤ N) (hq : q.deg ≤ M) :
    TrigEqV (N + M) ((tmTrigMul N M (Γ := [])).eval Env.nil (p.enc N) (q.enc M))
      ((p.mul q).enc (N + M)) := by
  intro n _
  rw [pairToCRat_ext_iff]
  let e : Env [.nat, TrigTy, TrigTy] :=
    Env.cons (σ := .nat) n (Env.cons (σ := TrigTy) (q.enc M) (Env.cons (σ := TrigTy) (p.enc N) Env.nil))
  have hlen : ((Tm.succ (natTm (2 * N)) : Tm [.nat, TrigTy, TrigTy] .nat).eval e) = 2 * N + 1 :=
    congrArg Nat.succ (natTm_eval e (2 * N))
  have hrec := tmTrigMul_rec_val N M p q hq n (2 * N + 1)
  change pairToCRat (Nat.rec (motive := fun _ ↦ Q × Q)
    ((tmCZero (Γ := [.nat, TrigTy, TrigTy])).eval e)
    (fun j acc ↦ (tmCAdd (.var .here)
      (tmTrigMulTerm M
        (.var (.there (.there (.there (.there .here)))))
        (.var (.there (.there (.there .here))))
        (.var (.there (.there .here)))
        (.var (.there .here)))).eval
      (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
    ((Tm.succ (natTm (2 * N)) : Tm [.nat, TrigTy, TrigTy] .nat).eval e)) =
    TrigPoly.toCRat ((p.mul q).coeff ((n : Int) - ((N + M : Nat) : Int)))
  rw [hlen, hrec,
      sum_range_sub_eq_sum_Icc N (fun k1 ↦
        TrigPoly.toCRat (p.coeff k1) * TrigPoly.toCRat (q.coeff (((n : Int) - ((N : Int) + (M : Int))) - k1))),
      sum_Icc_deg_le N p hp, toCRat_mul_coeff]
  push_cast
  rfl

/-- Evaluating `tmIKPow k n` maps to `(⟨0, (k.eval e).val⟩ : TrigPoly.CRat) ^ (n.eval e)`. -/
theorem pairToCRat_tmIKPow {Γ : List Ty} (k : Tm Γ .rat) (n : Tm Γ .nat) (e : Env Γ) :
    pairToCRat ((tmIKPow k n).eval e) = (⟨0, (k.eval e).val⟩ : TrigPoly.CRat) ^ (n.eval e) := by
  change pairToCRat (Nat.rec (motive := fun _ ↦ Q × Q)
    (Q.ofNat 1, Q.ofNat 0)
    (fun j acc ↦ (tmCMul (.var .here) (.pair (.qnat .zero) k.wk.wk)).eval
      (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
    (n.eval e)) = (⟨0, (k.eval e).val⟩ : TrigPoly.CRat) ^ (n.eval e)
  generalize n.eval e = m
  induction m with
  | zero =>
    ext
    · exact Q.val_ofNat 1
    · exact Q.val_ofNat 0
  | succ m ih =>
    let prev := Nat.rec (motive := fun _ ↦ Q × Q)
      (Q.ofNat 1, Q.ofNat 0)
      (fun j acc ↦ (tmCMul (.var .here) (.pair (.qnat .zero) k.wk.wk)).eval
        (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
      m
    let em : Env ((.prod .rat .rat) :: .nat :: Γ) :=
      Env.cons (σ := .prod .rat .rat) prev (Env.cons (σ := .nat) m e)
    change pairToCRat ((tmCMul (.var .here) (.pair (.qnat .zero) k.wk.wk)).eval em) = _
    rw [pairToCRat_tmCMul, pow_succ]
    change pairToCRat prev * pairToCRat ((Tm.pair (.qnat .zero) k.wk.wk).eval em) = _
    rw [ih]
    congr 1
    have hk : k.wk.wk.eval em = k.eval e :=
      (Tm.eval_wk (σ := .prod .rat .rat) k.wk prev (Env.cons (σ := .nat) m e)).trans
        (Tm.eval_wk (σ := .nat) k m e)
    ext
    · exact Q.val_ofNat 0
    · show (k.wk.wk.eval em).val = (k.eval e).val
      rw [hk]

/-- Evaluating `tmQFact n` has rational value `(fact (n.eval e) : Rat)`. -/
theorem tmQFact_val {Γ : List Ty} (n : Tm Γ .nat) (e : Env Γ) :
    ((tmQFact n).eval e).val = (fact (n.eval e) : Rat) := by
  change (Nat.rec (motive := fun _ ↦ Q)
    (Q.ofNat 1)
    (fun j acc ↦ Q.mul (Q.ofNat (j + 1)) acc)
    (n.eval e)).val = (fact (n.eval e) : Rat)
  generalize n.eval e = m
  induction m with
  | zero => exact Q.val_ofNat 1
  | succ m ih =>
    change (Q.mul (Q.ofNat (m + 1)) _).val = (fact (m + 1) : Rat)
    rw [Q.val_mul, Q.val_ofNat, ih]
    dsimp [fact]
    push_cast
    ring

/-- Evaluating the `recNat` sum inside `tmTrigToJet N` up to `r` yields the partial moment sum in `TrigPoly.CRat`. -/
theorem tmTrigToJet_rec_val (N : Nat) (p : TrigPoly) (n : Nat) (r : Nat) :
    let e : Env [.nat, TrigTy] :=
      Env.cons (σ := .nat) n (Env.cons (σ := TrigTy) (p.enc N) Env.nil)
    let step : Tm ((.prod .rat .rat) :: .nat :: [.nat, TrigTy]) (.prod .rat .rat) :=
      tmCAdd (.var .here)
        (tmCMul (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
          (tmIKPow (.qsub (.qnat (.var (.there .here))) (.qnat (natTm N)))
            (.var (.there (.there .here)))))
    pairToCRat (Nat.rec (motive := fun _ ↦ Q × Q)
      ((tmCZero (Γ := [.nat, TrigTy])).eval e)
      (fun j acc ↦ step.eval (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
      r) =
    ∑ j ∈ Finset.range r,
      TrigPoly.toCRat (p.coeff ((j : Int) - N)) * (TrigPoly.ikCRat ((j : Int) - N)) ^ n := by
  let e : Env [.nat, TrigTy] :=
    Env.cons (σ := .nat) n (Env.cons (σ := TrigTy) (p.enc N) Env.nil)
  let step : Tm ((.prod .rat .rat) :: .nat :: [.nat, TrigTy]) (.prod .rat .rat) :=
    tmCAdd (.var .here)
      (tmCMul (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
        (tmIKPow (.qsub (.qnat (.var (.there .here))) (.qnat (natTm N)))
          (.var (.there (.there .here)))))
  induction r with
  | zero =>
    rw [Finset.sum_range_zero]
    exact pairToCRat_tmCZero e
  | succ j ih =>
    let prev := Nat.rec (motive := fun _ ↦ Q × Q)
      ((tmCZero (Γ := [.nat, TrigTy])).eval e)
      (fun j acc ↦ step.eval (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
      j
    let ej : Env ((.prod .rat .rat) :: .nat :: [.nat, TrigTy]) :=
      Env.cons (σ := .prod .rat .rat) prev (Env.cons (σ := .nat) j e)
    change pairToCRat (step.eval ej) = _
    dsimp only [step]
    rw [pairToCRat_tmCAdd, pairToCRat_tmCMul, pairToCRat_tmIKPow, Finset.sum_range_succ, ← ih]
    congr 1
    congr 1
    have hk : ((Tm.qsub (.qnat (.var (.there .here))) (.qnat (natTm N))).eval ej).val =
        (((j : Int) - N : Int) : Rat) := by
      change (Q.sub (Q.ofNat j) (Q.ofNat ((natTm N).eval ej))).val = _
      rw [natTm_eval, qsub_ofNat_val]
    rw [hk]
    rfl

theorem tmTrigToJet_spec (N : Nat) (p : TrigPoly) (hp : p.deg ≤ N) (n : Nat) :
    ((tmTrigToJet N (Γ := [])).eval Env.nil (p.enc N) n).val = ((p.toJet).coeff n).val := by
  let e : Env [.nat, TrigTy] :=
    Env.cons (σ := .nat) n (Env.cons (σ := TrigTy) (p.enc N) Env.nil)
  have hfact_val : ((tmQFact (.var .here : Tm [.nat, TrigTy] .nat)).eval e).val = (fact n : Rat) :=
    tmQFact_val (.var .here) e
  have hfact_ne : ((tmQFact (.var .here : Tm [.nat, TrigTy] .nat)).eval e).val ≠ 0 := by
    rw [hfact_val]
    exact Nat.cast_ne_zero.mpr (ne_of_gt (fact_pos n))
  have hfact_num : ((tmQFact (.var .here : Tm [.nat, TrigTy] .nat)).eval e).num ≠ 0 :=
    Q.num_ne_zero_of_val_ne_zero hfact_ne
  have hlen : ((Tm.succ (natTm (2 * N)) : Tm [.nat, TrigTy] .nat).eval e) = 2 * N + 1 :=
    congrArg Nat.succ (natTm_eval e (2 * N))
  have hrec := tmTrigToJet_rec_val N p n (2 * N + 1)
  rw [sum_range_sub_eq_sum_Icc N (fun k ↦ TrigPoly.toCRat (p.coeff k) * (TrigPoly.ikCRat k) ^ n),
      sum_Icc_deg_le N p hp] at hrec
  have hrec_re := congrArg TrigPoly.CRat.re hrec
  change (Q.div
    (Nat.rec (motive := fun _ ↦ Q × Q)
      ((tmCZero (Γ := [.nat, TrigTy])).eval e)
      (fun j acc ↦ (tmCAdd (.var .here)
        (tmCMul (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
          (tmIKPow (.qsub (.qnat (.var (.there .here))) (.qnat (natTm N)))
            (.var (.there (.there .here)))))).eval
        (Env.cons (σ := .prod .rat .rat) acc (Env.cons (σ := .nat) j e)))
      ((Tm.succ (natTm (2 * N)) : Tm [.nat, TrigTy] .nat).eval e)).1
    ((tmQFact (.var .here : Tm [.nat, TrigTy] .nat)).eval e)).val = _
  rw [Q.val_div _ _ hfact_num, hfact_val, hlen, TrigPoly.toJet_coeff_val]
  exact congrArg (· / (fact n : Rat)) hrec_re

#print axioms tmTrigAdd
#print axioms tmTrigDeriv
#print axioms tmTrigInteg
#print axioms tmTrigMul
#print axioms tmTrigToJet
#print axioms tmTrigAdd_spec
#print axioms tmTrigDeriv_spec
#print axioms tmTrigInteg_spec
#print axioms tmTrigMul_spec
#print axioms tmTrigToJet_spec

end HAomega
