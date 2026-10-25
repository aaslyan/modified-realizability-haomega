/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.GcdFull
import HAomega.Sperner

/-!
# Bisection, as an operator extracted from a proof

    bisectD : ∀j ∀c^(ℕ→ℕ) ∀lo.  c lo ≠ c (lo + 2ʲ) → ∃i. i < 2ʲ ∧ c (lo+i) ≠ c (lo+i+1)

A coloring is a function variable, so the theorem quantifies over functions,
and its realizer is a **type-2 operator** `(ℕ → ℕ) → ℕ → ℕ`-shaped: a function
and two numbers in, a crossing out.  Nobody writes the algorithm: the proof is
induction on `j` (the logarithm of the interval length), and its step splits
the interval at `lo + 2ʲ` and decides `c lo = c (lo + 2ʲ)` by `eqDec` — so the
extracted program **is binary search**, querying `c` at `j + 1` points.
Contrast `Sperner.lean`: the same kind of crossing, proved by a forward scan,
extracts a linear scan.  Course-of-values induction is not needed: the halving
lives in the statement (intervals of length `2ʲ`), not in the recursion.

**Two proofs, two programs.** `bisectSlowD` proves the same statement with the
induction hypothesis applied inside both branches of the midpoint case split.
Its program is exponential in `j`, for two reasons that are both properties of
*extraction*, not of the mathematics: `orE` extracts to `recNat left right tag`,
whose left branch is evaluated eagerly, and `exE` extracts to
`(λλ body) (snd p) (fst p)`, which evaluates the eliminated program `p` twice.
`bsStepD` restructures the proof — first decide *which half* (a number), then
call the hypothesis once, and bind its result with an `impE`/`impI` redex before
opening it — and its program is linear in `j`: an interval of `2⁶⁰` points in
milliseconds, where `bisectSlow` already takes about 30 s at `j = 16`.  Same
theorem; the proof's shape is the algorithm's cost.

`2ʲ` is the System T term `tmPow2`, `i < n` is the defined order
`∃d. (i+1) + d = n` (as in `Sperner.lean`), `≠` is the negated equation.
-/

namespace HAomega

/-! ## `2ʲ` as a System T term -/

/-- `λj. recNat 1 (λ_ a. a + a) j`. -/
def tmPow2 {Γ : List Ty} : Tm Γ (.arrow .nat .nat) :=
  .lam (.recNat (.succ .zero) (.lam (.lam (.add (.var .here) (.var .here)))) (.var .here))

@[derivNorm] theorem tmPow2_rename {Γ Δ : List Ty} (ρ : Ren Γ Δ) :
    (tmPow2 (Γ := Γ)).rename ρ = tmPow2 := rfl

@[derivNorm] theorem tmPow2_subst {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (tmPow2 (Γ := Γ)).subst s = tmPow2 := rfl

theorem tmPow2_eval {Γ : List Ty} (e : Env Γ) (j : Nat) : (tmPow2 (Γ := Γ)).eval e j = 2 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show (tmPow2 (Γ := Γ)).eval e j + (tmPow2 (Γ := Γ)).eval e j = 2 ^ (j + 1)
      rw [ih, Nat.pow_succ, Nat.mul_two]

/-! ## The crossing formula -/

/-- `∃i. i < len ∧ c (lo+i) ≠ c (lo+i+1)` — a crossing in `[lo, lo + len]`. -/
def bsCross {Γ : List Ty} (c : Tm Γ (.arrow .nat .nat)) (lo len : Tm Γ .nat) :
    Formula Γ (.prod .nat (.prod (.prod .nat .unit) (.arrow .unit .unit))) :=
  .ex .nat (.and
    (.ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here)) len.wk.wk))
    (Formula.eq (.app c.wk (.add lo.wk (.var .here)))
      (.app c.wk (.succ (.add lo.wk (.var .here))))).neg)

attribute [derivNorm] bsCross

section Helpers

variable {Γ as : List Ty} {Δ : Ctx Γ as}

/-- Introduce a crossing from its witness `i`, its slack `d`, and the inequality. -/
def bsCrossI {c : Tm Γ (.arrow .nat .nat)} {lo len : Tm Γ .nat} (i d : Tm Γ .nat)
    (h1 : Deriv Δ (.eq (.add (.succ i) d) len))
    (h2 : Deriv Δ (Formula.eq (.app c (.add lo i)) (.app c (.succ (.add lo i)))).neg) :
    Deriv Δ (bsCross c lo len) := by
  refine Deriv.exI i ?_
  deriv_norm
  refine Deriv.andI (Deriv.exI d ?_) ?_
  · deriv_norm
    exact h1
  · deriv_norm at h2 ⊢
    exact h2

end Helpers

/-- `2⁰ = 1`. -/
def pow2ZeroD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.eq (.app tmPow2 .zero) (.succ .zero)) := by
  have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.recNat (.succ .zero) (.lam (.lam (.add (.var .here) (.var .here)))) (.var .here)) .zero
  deriv_norm at hb
  exact Deriv.transE hb (Deriv.convRecZero _ _)

/-- `2ʲ⁺¹ = 2ʲ + 2ʲ`. -/
def pow2SuccD {Γ as : List Ty} {Δ : Ctx Γ as} (j : Tm Γ .nat) :
    Deriv Δ (.eq (.app tmPow2 (.succ j)) (.add (.app tmPow2 j) (.app tmPow2 j))) := by
  let st : Tm Γ (.arrow .nat (.arrow .nat .nat)) := .lam (.lam (.add (.var .here) (.var .here)))
  have hb : ∀ m : Tm Γ .nat, Deriv Δ (.eq (.app tmPow2 m) (.recNat (.succ .zero) st m)) := by
    intro m
    have hb := Deriv.convBeta (Δ := Δ) (c := .nat)
      (.recNat (.succ .zero) (.lam (.lam (.add (.var .here) (.var .here)))) (.var .here)) m
    deriv_norm at hb
    exact hb
  have b1 := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.lam (.add (.var .here) (.var .here)) : Tm (.nat :: Γ) (.arrow .nat .nat)) j
  deriv_norm at b1
  have b2 := Deriv.convBeta (Δ := Δ) (c := .nat)
    (.add (.var .here) (.var .here)) (.recNat (.succ .zero) st j)
  deriv_norm at b2
  have h := Deriv.transE (hb _) (Deriv.transE (Deriv.convRecSucc _ st j)
    (Deriv.transE (Deriv.congFun b1 _) b2))
  have e := Deriv.symmE (hb j)
  exact Deriv.transE h (Deriv.transE (Deriv.congAddL _ e) (Deriv.congAddR _ e))

/-- The induction formula, over `j`: every interval `[lo, lo + 2ʲ]` whose ends
disagree contains a crossing.  Context `lo :: c :: j`. -/
abbrev bsPhi : Formula [.nat] (.arrow (.arrow .nat .nat) (.arrow .nat
    (.arrow (.arrow .unit .unit)
      (.prod .nat (.prod (.prod .nat .unit) (.arrow .unit .unit)))))) :=
  .all (.arrow .nat .nat) (.all .nat (.imp
    (Formula.eq (.app (.var (.there .here)) (.var .here))
      (.app (.var (.there .here)) (.add (.var .here)
        (.app tmPow2 (.var (.there (.there .here))))))).neg
    (bsCross (.var (.there .here)) (.var .here) (.app tmPow2 (.var (.there (.there .here)))))))

def bsBaseD : Deriv (Ctx.nil (Γ := [])) (bsPhi.subst1 .zero) := by
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  -- the one-step interval `[lo, lo+1]`: its crossing is at `i = 0`
  refine Deriv.exI .zero ?_
  deriv_norm
  refine Deriv.andI (Deriv.exI .zero ?_) ?_
  · deriv_norm
    exact Deriv.transE (Deriv.convAddZero _) (Deriv.symmE pow2ZeroD)
  · refine Deriv.impI (Deriv.impE (Deriv.wk Deriv.ax) ?_)
    exact Deriv.transE (Deriv.congArg _ (Deriv.symmE (Deriv.convAddZero _)))
      (Deriv.transE Deriv.ax (Deriv.congArg _ (Deriv.transE
        (Deriv.symmE (Deriv.convAddSucc _ _)) (Deriv.congAddR _ (Deriv.symmE pow2ZeroD)))))

def bsStepSlowD : Deriv (Ctx.nil (Γ := [])) (.all .nat (.imp bsPhi (bsPhi.subst Sub.succHere))) := by
  refine Deriv.allI (Deriv.impI ?_)
  simp only [bsPhi]
  deriv_norm
  simp only [Sub.succHere]
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  -- variables `lo :: c :: j`; hypotheses `H : c lo ≠ c (lo + 2ʲ⁺¹)`, the IH at `j`
  let lo : Tm [.nat, .arrow .nat .nat, .nat] .nat := .var .here
  let c : Tm [.nat, .arrow .nat .nat, .nat] (.arrow .nat .nat) := .var (.there .here)
  let L : Tm [.nat, .arrow .nat .nat, .nat] .nat := .app tmPow2 (.var (.there (.there .here)))
  -- `(lo + L) + L = lo + 2ʲ⁺¹`
  have hMid : ∀ {as'} {Δ' : Ctx [.nat, .arrow .nat .nat, .nat] as'},
      Deriv Δ' (.eq (.add (.add lo L) L) (.add lo (.app tmPow2 (.succ (.var (.there (.there .here))))))) :=
    fun {_ _} ↦ Deriv.transE (plusAssocT _ _ _) (Deriv.congAddR _ (Deriv.symmE (pow2SuccD _)))
  -- instantiate the IH at `c` (hypotheses now `IHc :: H :: IH`)
  refine Deriv.impE (Deriv.impI ?_) (Deriv.allE c (Deriv.wk Deriv.ax))
  deriv_norm
  refine Deriv.orE (Deriv.eqDec (.app c lo) (.app c (.add lo L))) ?_ ?_
  · -- `c lo = c (lo + L)`: then `c (lo+L) ≠ c (lo+2L)`, recurse on the right half
    refine Deriv.impE (Deriv.impI ?_) (Deriv.allE (.add lo L) (Deriv.wk Deriv.ax))
    deriv_norm
    -- hypotheses `ih :: e :: IHc :: H :: IH`
    refine Deriv.exE (Deriv.impE Deriv.ax ?_) ?_
    · exact Deriv.impI (Deriv.impE (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))))
        (Deriv.transE (Deriv.wk (Deriv.wk Deriv.ax))
          (Deriv.transE Deriv.ax (Deriv.congArg _ hMid))))
    deriv_norm
    refine Deriv.exE (Deriv.andE₁ Deriv.ax) ?_
    deriv_norm
    -- the witness shifts by the half length: `L + i`
    refine Deriv.exI (.add (.app tmPow2 (.var (.there (.there (.there (.there .here))))))
      (.var (.there .here))) ?_
    deriv_norm
    refine Deriv.andI (Deriv.exI (.var .here) ?_) ?_
    · deriv_norm
      exact Deriv.transE (Deriv.congAddL _ (Deriv.symmE (Deriv.convAddSucc _ _)))
        (Deriv.transE (plusAssocT _ _ _)
          (Deriv.transE (Deriv.congAddR _ Deriv.ax) (Deriv.symmE (pow2SuccD _))))
    · exact Deriv.impI (Deriv.impE (Deriv.wk (Deriv.andE₂ (Deriv.wk Deriv.ax)))
        (Deriv.transE (Deriv.congArg _ (plusAssocT _ _ _))
          (Deriv.transE Deriv.ax (Deriv.congArg _ (Deriv.congSucc
            (Deriv.symmE (plusAssocT _ _ _)))))))
  · -- `c lo ≠ c (lo + L)`: recurse on the left half
    refine Deriv.impE (Deriv.impI ?_) (Deriv.allE lo (Deriv.wk Deriv.ax))
    deriv_norm
    refine Deriv.exE (Deriv.impE Deriv.ax (Deriv.wk Deriv.ax)) ?_
    deriv_norm
    refine Deriv.exE (Deriv.andE₁ Deriv.ax) ?_
    deriv_norm
    refine Deriv.exI (.var (.there .here)) ?_
    deriv_norm
    refine Deriv.andI (Deriv.exI (.add (.var .here)
      (.app tmPow2 (.var (.there (.there (.there (.there .here))))))) ?_) (Deriv.andE₂ (Deriv.wk Deriv.ax))
    deriv_norm
    exact Deriv.transE (Deriv.symmE (plusAssocT _ _ _))
      (Deriv.transE (Deriv.congAddL _ Deriv.ax) (Deriv.symmE (pow2SuccD _)))

/-- The fast step: decide **which half** first — an offset `s ∈ {0, 2ʲ}` whose
interval `[lo+s, lo+s+2ʲ]` still has disagreeing ends — and only then apply
the induction hypothesis, **once**, at `lo + s`.  The case split now only
chooses a number, so its eagerly evaluated branch is cheap. -/
def bsStepD : Deriv (Ctx.nil (Γ := [])) (.all .nat (.imp bsPhi (bsPhi.subst Sub.succHere))) := by
  refine Deriv.allI (Deriv.impI ?_)
  simp only [bsPhi]
  deriv_norm
  simp only [Sub.succHere]
  deriv_norm
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_))
  deriv_norm
  let lo : Tm [.nat, .arrow .nat .nat, .nat] .nat := .var .here
  let c : Tm [.nat, .arrow .nat .nat, .nat] (.arrow .nat .nat) := .var (.there .here)
  let L : Tm [.nat, .arrow .nat .nat, .nat] .nat := .app tmPow2 (.var (.there (.there .here)))
  have hMid : ∀ {as'} {Δ' : Ctx [.nat, .arrow .nat .nat, .nat] as'},
      Deriv Δ' (.eq (.add (.add lo L) L) (.add lo (.app tmPow2 (.succ (.var (.there (.there .here))))))) :=
    fun {_ _} ↦ Deriv.transE (plusAssocT _ _ _) (Deriv.congAddR _ (Deriv.symmE (pow2SuccD _)))
  -- the half: `∃s. (s = 0 ∨ s = L) ∧ c (lo+s) ≠ c ((lo+s)+L)`
  refine Deriv.impE (Deriv.impI (x := .ex .nat (.and
      (.or (.eq (.var .here) .zero)
        (.eq (.var .here) (.app tmPow2 (.var (.there (.there (.there .here)))))))
      (Formula.eq (.app (.var (.there (.there .here))) (.add (.var (.there .here)) (.var .here)))
        (.app (.var (.there (.there .here)))
          (.add (.add (.var (.there .here)) (.var .here))
            (.app tmPow2 (.var (.there (.there (.there .here)))))))).neg)) ?_) ?_
  rotate_left
  · refine Deriv.orE (Deriv.eqDec (.app c lo) (.app c (.add lo L))) ?_ ?_
    · -- equal: the right half, `s = L`
      refine Deriv.exI L ?_
      deriv_norm
      refine Deriv.andI (Deriv.orI₂ (Deriv.eqRefl _)) ?_
      exact Deriv.impI (Deriv.impE (Deriv.wk (Deriv.wk Deriv.ax))
        (Deriv.transE (Deriv.wk Deriv.ax) (Deriv.transE Deriv.ax (Deriv.congArg _ hMid))))
    · -- unequal: the left half, `s = 0`
      refine Deriv.exI .zero ?_
      deriv_norm
      refine Deriv.andI (Deriv.orI₁ (Deriv.eqRefl _)) ?_
      exact Deriv.impI (Deriv.impE (Deriv.wk Deriv.ax)
        (Deriv.transE (Deriv.congArg _ (Deriv.symmE (Deriv.convAddZero _)))
          (Deriv.transE Deriv.ax (Deriv.congArg _
            (Deriv.congAddL _ (Deriv.convAddZero _))))))
  deriv_norm
  -- hypotheses `hM :: H :: IH`; open the half
  refine Deriv.exE Deriv.ax ?_
  deriv_norm
  -- variables `s :: lo :: c :: j`; one IH call, at `c`, `lo + s`
  refine Deriv.impE (Deriv.impI ?_) (Deriv.allE (.add (.var (.there .here)) (.var .here))
    (Deriv.allE (.var (.there (.there .here))) (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax)))))
  deriv_norm
  -- bind the recursive result to a hypothesis *before* opening it: `exE`
  -- extracts to `(λλ body) (snd p) (fst p)`, which would evaluate `p` — the
  -- recursive call — twice; an `impE`/`impI` redex evaluates it once
  refine Deriv.impE (Deriv.impI ?_) (Deriv.impE Deriv.ax (Deriv.andE₂ (Deriv.wk Deriv.ax)))
  refine Deriv.exE Deriv.ax ?_
  deriv_norm
  refine Deriv.exE (Deriv.andE₁ Deriv.ax) ?_
  deriv_norm
  -- variables `d :: i :: s :: lo :: c :: j`; the witness is `s + i`
  refine Deriv.exI (.add (.var (.there (.there .here))) (.var (.there .here))) ?_
  deriv_norm
  refine Deriv.andI ?_ ?_
  · -- the bound, by cases on the half (both branches pure arithmetic)
    refine Deriv.orE (Deriv.andE₁ (Deriv.wk (Deriv.wk (Deriv.wk (Deriv.wk Deriv.ax))))) ?_ ?_
    · -- `s = 0`: `(s+i)+1 + (d + L) = L + L`
      refine Deriv.exI (.add (.var .here)
        (.app tmPow2 (.var (.there (.there (.there (.there (.there .here)))))))) ?_
      deriv_norm
      refine Deriv.transE (Deriv.congAddL _ (Deriv.congSucc (Deriv.transE
        (Deriv.congAddL _ Deriv.ax) (zeroPlusT _)))) ?_
      exact Deriv.transE (Deriv.symmE (plusAssocT _ _ _))
        (Deriv.transE (Deriv.congAddL _ (Deriv.wk Deriv.ax)) (Deriv.symmE (pow2SuccD _)))
    · -- `s = L`: `(s+i)+1 + d = L + L`
      refine Deriv.exI (.var .here) ?_
      deriv_norm
      refine Deriv.transE (Deriv.congAddL _ (Deriv.congSucc (Deriv.congAddL _ Deriv.ax))) ?_
      exact Deriv.transE (Deriv.congAddL _ (Deriv.symmE (Deriv.convAddSucc _ _)))
        (Deriv.transE (plusAssocT _ _ _)
          (Deriv.transE (Deriv.congAddR _ (Deriv.wk Deriv.ax)) (Deriv.symmE (pow2SuccD _))))
  · -- the crossing: `lo + (s+i) = (lo+s) + i`
    exact Deriv.impI (Deriv.impE (Deriv.wk (Deriv.andE₂ (Deriv.wk Deriv.ax)))
      (Deriv.transE (Deriv.congArg _ (plusAssocT _ _ _))
        (Deriv.transE Deriv.ax (Deriv.congArg _ (Deriv.congSucc
          (Deriv.symmE (plusAssocT _ _ _)))))))

/-- **Bisection**: `∀j ∀c ∀lo. c lo ≠ c (lo + 2ʲ) → ∃i < 2ʲ. c (lo+i) ≠ c (lo+i+1)`. -/
def bisectD : Deriv (Ctx.nil (Γ := [])) (.all .nat bsPhi) := Deriv.ind bsBaseD bsStepD

/-- The same theorem by the slow step (the IH inside both branches). -/
def bisectSlowD : Deriv (Ctx.nil (Γ := [])) (.all .nat bsPhi) := Deriv.ind bsBaseD bsStepSlowD

/-! ## The operator -/

/-- **The extracted bisection operator.**  Depth `j`, coloring `c`, left end
`lo` ↦ the offset `i` of a crossing in `[lo, lo + 2ʲ]`.  Nobody wrote this
program: it is `extract bisectD`, read at its first component. -/
def bisect (j : Nat) (c : Nat → Nat) (lo : Nat) : Nat :=
  ((extractClosed bisectD).eval Env.nil j c lo (fun _ ↦ ())).1

/-- The program extracted from `bisectSlowD`: same theorem, same answers where
both run, but it evaluates both halves' recursive calls (`orE` extracts to
`recNat left right tag`, and the left branch is evaluated eagerly). -/
def bisectSlow (j : Nat) (c : Nat → Nat) (lo : Nat) : Nat :=
  ((extractClosed bisectSlowD).eval Env.nil j c lo (fun _ ↦ ())).1

/-- **Its certificate, from `soundness`**: whenever the ends of `[lo, lo + 2ʲ]`
disagree, `bisect` returns an offset inside the interval at which `c` changes. -/
theorem bisect_spec (j : Nat) (c : Nat → Nat) (lo : Nat) (h : c lo ≠ c (lo + 2 ^ j)) :
    bisect j c lo < 2 ^ j ∧ c (lo + bisect j c lo) ≠ c (lo + bisect j c lo + 1) := by
  have hs := soundness bisectD Env.nil Env.nil (fun _ v ↦ nomatch v) j c lo (fun _ ↦ ())
    (fun _ hz ↦ h (by
      change c lo = c (lo + (tmPow2 (Γ := [.nat, .arrow .nat .nat, .nat])).eval _ j) at hz
      rwa [tmPow2_eval] at hz))
  obtain ⟨h1, h2⟩ := hs
  constructor
  · change bisect j c lo + 1 + _ = (tmPow2 (Γ := [.nat, .nat, .nat, .arrow .nat .nat, .nat])).eval _ j at h1
    rw [tmPow2_eval] at h1
    omega
  · exact fun hc ↦ h2 () hc

/-! ## Running the operator

Pure Lean functions as colorings — no coding.  Every `#guard` below runs the
extracted program. -/

-- small intervals: a valid crossing (soundness), checked
#guard bisect 2 (fun k ↦ [0,0,1,1,1].getD k 0) 0 == 1
#guard bisect 2 (fun k ↦ [5,5,5,5,5,7,7].getD k 0) 3 == 1
-- an oscillating coloring: bisection finds the crossing its halving leads to,
-- not the first one (a linear scan would return 0)
#guard bisect 3 (fun k ↦ [0,1,0,1,0,1,0,1,1].getD k 0) 0 == 6
-- an interval of 2⁶⁰ points: 61 queries, milliseconds
#guard bisect 60 (fun k ↦ if k < 777777777777777778 then 0 else 1) 0 == 777777777777777777
-- `⌊√2 · 2⁴⁰⌋`, as the crossing of `k ↦ [k² ≥ 2·4⁴⁰]`
#guard bisect 41 (fun k ↦ if k * k < 2 * 4 ^ 40 then 0 else 1) 0 == 1554944255987
-- the slow proof's program agrees where it runs
#guard bisectSlow 8 (fun k ↦ if k < 200 then 0 else 1) 0 == bisect 8 (fun k ↦ if k < 200 then 0 else 1) 0

#print axioms bisectD
#print axioms bisect
#print axioms bisect_spec
#print axioms bisectSlowD

end HAomega
