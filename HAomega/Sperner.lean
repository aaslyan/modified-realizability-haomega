/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.Hercules

/-!
# Sperner's lemma in one dimension

    spernerD : ∀n ∀c^(ℕ→ℕ). c 0 = 0 → c n = 1 → ∃k. k < n ∧ c k ≠ c (k+1)

The discrete intermediate value theorem.  In the first-order development the
coloring had to be a ℕ-code accessed through the `look` symbol — the one
place its "no new symbols" discipline was genuinely forced.  Here **a
coloring is a function variable**: no symbol, no coding, and the theorem is
stated for arbitrary ℕ-valued colorings exactly as in the mathematics.

`k < n` is the defined order `∃d. (k+1) + d = n`; `≠` is the negated
equation.  The proof is the first-order S1 forward scan: induction on the
invariant `P(m) := c m = 0 ∨ ∃k < m. c k ≠ c (k+1)`.

**The extracted witness is the *last* crossing, not the first** — and that is
a finding, not a defect.  This proof's step decides `c (m+1) = 0` *before*
consulting the invariant, so a fresh zero re-enters the left disjunct and
discards any crossing already found; the first-order S1 proof consults the
invariant first and therefore extracts the *first*-crossing scan.  Same
theorem, different proof — measurably different program: the extraction map
is faithful to proof structure, which is the whole thesis.
-/

namespace HAomega

/-- The scan invariant, over `m :: c :: n :: Γ`. -/
abbrev spInv (Γ : List Ty) : Formula (.nat :: .arrow .nat .nat :: .nat :: Γ)
    (.prod .nat (.prod .unit
      (.prod .nat (.prod (.prod .nat .unit) (.arrow .unit .unit))))) :=
  .or (.eq (.app (.var (.there .here)) (.var .here)) .zero)
      (.ex .nat (.and
        (.ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here))
          (.var (.there (.there .here)))))
        ((Formula.eq (.app (.var (.there (.there .here))) (.var .here))
          (.app (.var (.there (.there .here))) (.succ (.var .here)))).neg)))

/-- **Sperner 1D.** -/
def spernerD {Γ as : List Ty} {Δ : Ctx Γ as} :
    Deriv Δ (.all .nat (.all (.arrow .nat .nat)
      (.imp (.eq (.app (.var .here) .zero) .zero)
      (.imp (.eq (.app (.var .here) (.var (.there .here))) (.succ .zero))
        (.ex .nat (.and
          (.ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here))
            (.var (.there (.there (.there .here))))))
          ((Formula.eq (.app (.var (.there .here)) (.var .here))
            (.app (.var (.there .here)) (.succ (.var .here)))).neg))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_)))
  -- ctx: c :: n ; hyps: h1 (c n = 1) :: h0 (c 0 = 0)
  -- prove the invariant for all m, then read it at n
  have hInv : Deriv (.cons (.eq (.app (.var .here) (.var (.there .here))) (.succ .zero))
      (.cons (.eq (.app (.var .here) .zero) .zero) ((Δ.wk).wk)))
      (.all .nat (spInv Γ)) := by
    refine Deriv.ind ?_ ?_
    · -- P(0): the left disjunct is exactly h0
      refine Deriv.orI₁ ?_
      deriv_norm
      deriv_assumption
    · refine Deriv.allI (Deriv.impI ?_)
      deriv_norm
      -- decide c (m+1) = 0
      refine Deriv.orE (Deriv.eqDec
        (.app (.var (.there .here)) (.succ (.var .here))) .zero) ?_ ?_
      · exact Deriv.orI₁ Deriv.ax
      · -- c (m+1) ≠ 0: case on the invariant at m
        refine Deriv.orE (Deriv.wk Deriv.ax) ?_ ?_
        · -- c m = 0 ⟹ crossing at m
          refine Deriv.orI₂ (Deriv.exI (.var .here) ?_)
          deriv_norm
          refine Deriv.andI (Deriv.exI .zero ?_) ?_
          · deriv_norm
            exact Deriv.transE (Deriv.convAddZero _) (Deriv.eqRefl _)
          · refine Deriv.impI ?_
            refine Deriv.impE (Deriv.wk (Deriv.wk (Deriv.ax
              (φ := (Formula.eq (.app (.var (.there .here)) (.succ (.var .here)))
                .zero).neg)))) ?_
            refine Deriv.transE (Deriv.symmE Deriv.ax) ?_
            exact Deriv.transE (Deriv.wk Deriv.ax) (Deriv.eqRefl _)
        · -- crossing below m carries up
          refine Deriv.exE
            (ψ := .or (.eq (.app (.var (.there .here)) (.succ (.var .here))) .zero)
              (.ex .nat (.and
                (.ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here))
                  (.succ (.var (.there (.there .here))))))
                ((Formula.eq (.app (.var (.there (.there .here))) (.var .here))
                  (.app (.var (.there (.there .here)))
                    (.succ (.var .here)))).neg))))
            Deriv.ax ?_
          deriv_norm
          refine Deriv.orI₂ (Deriv.exI (.var .here) ?_)
          deriv_norm
          refine Deriv.andI ?_ ?_
          · refine Deriv.exE
              (ψ := .ex .nat (.eq (.add (.succ (.var (.there .here))) (.var .here))
                (.succ (.var (.there (.there .here))))))
              (Deriv.andE₁ Deriv.ax) ?_
            deriv_norm
            refine Deriv.exI (.succ (.var .here)) ?_
            deriv_norm
            refine Deriv.transE (Deriv.convAddSucc _ _) ?_
            exact Deriv.transE (Deriv.congSucc Deriv.ax) (Deriv.eqRefl _)
          · exact Deriv.andE₂ Deriv.ax
  have hn := Deriv.allE (τ := .nat) (.var (.there .here)) hInv
  deriv_norm at hn
  refine Deriv.orE hn ?_ ?_
  · -- c n = 0 contradicts c n = 1
    refine Deriv.botE ?_
    refine Deriv.impE (Deriv.succNeZero .zero) ?_
    refine Deriv.transE (Deriv.symmE (Deriv.wk Deriv.ax)) ?_
    exact Deriv.transE Deriv.ax (Deriv.eqRefl _)
  · exact Deriv.ax

/-- **The extracted last-crossing search.** -/
def spernerX (n : Nat) (c : Nat → Nat) : Nat :=
  ((((((extractClosed (spernerD (Γ := []) (Δ := Ctx.nil))).eval Env.nil)
    n) c) ()) ()).1

-- Concrete colorings, as plain Lean functions — no coding, no `look`.
-- Valid crossings at every coloring (soundness), and specifically the *last*
-- 0→nonzero edge, per the proof-structure note above.
#guard [spernerX 3 (fun k ↦ [0,1,0,1].getD k 0),
        spernerX 2 (fun k ↦ [0,0,1].getD k 0),
        spernerX 4 (fun k ↦ [0,1,1,0,1].getD k 0),
        spernerX 3 (fun k ↦ [0,0,0,1].getD k 0),
        spernerX 5 (fun k ↦ [0,0,7,7,0,1].getD k 0)] == [2, 1, 3, 2, 4]
#guard (let c := fun k ↦ [0,1,0,1].getD k 0
        let k := spernerX 3 c
        c k != c (k+1) && k < 3)

#print axioms spernerD
#print axioms spernerX

end HAomega
