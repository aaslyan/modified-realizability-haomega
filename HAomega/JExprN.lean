/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.TrigPolyTerms

/-!
# Polynomial–integral expressions in `n` jet variables

`JExpr` (one variable) and `JExpr2` (two) generalized to any number of
variables. A state is a stream of jets `W : ℕ → JetTy` (`WTy`), variable `i`
being `W(i)`; `JExprN.var i` reads it. `JExprN.WF n F` says every variable
index in `F` is `< n`.

`JExprN.prefixT` is the prefix lemma, derived inside `Deriv` by structural
recursion: if `w, w'` agree, in every variable `v < n`, at every index `≤ N`,
then `F(w), F(w')` agree at every index `≤ N` — for every well-formed `F`.
It is what the n-variable general solver needs.
-/

namespace HAomega

/-- A state: variable index `↦` jet. -/
abbrev WTy : Ty := .arrow .nat JetTy

/-- Polynomial–integral expressions in jet variables `var 0, var 1, …`. -/
inductive JExprN : Type where
  | var : Nat → JExprN
  | const : Tm [] JetTy → JExprN
  | add : JExprN → JExprN → JExprN
  | sub : JExprN → JExprN → JExprN
  | mul : JExprN → JExprN → JExprN
  | integ : JExprN → JExprN

/-- Every variable index is `< n`. -/
def JExprN.WF (n : Nat) : JExprN → Prop
  | .var i => i < n
  | .const _ => True
  | .add a b => a.WF n ∧ b.WF n
  | .sub a b => a.WF n ∧ b.WF n
  | .mul a b => a.WF n ∧ b.WF n
  | .integ a => a.WF n

/-- The jet term `F(w)`. -/
def JExprN.toTm {Γ : List Ty} (w : Tm Γ WTy) : JExprN → Tm Γ JetTy
  | .var i => .app w (natTm i)
  | .const c => Tm.closedWk c
  | .add a b => .app (.app tmJetAdd (a.toTm w)) (b.toTm w)
  | .sub a b => .app (.app tmJetSub (a.toTm w)) (b.toTm w)
  | .mul a b => .app (.app tmJetMul (a.toTm w)) (b.toTm w)
  | .integ a => .app tmJetInteg (a.toTm w)

/-- `w, w'` agree in every variable `v < n` at every index `≤ N`:
    `∀v ∀e. v + succ e = n → prefixAgree (w v) (w' v) N`. -/
abbrev prefixAgreeN {Γ : List Ty} (n : Nat) (w w' : Tm Γ WTy) (N : Tm Γ .nat) :=
  (Formula.all .nat (.all .nat
    (.imp (.eq (.add (.var (.there .here)) (.succ (.var .here))) (natTm n))
      (prefixAgree (.app w.wk.wk (.var (.there .here))) (.app w'.wk.wk (.var (.there .here)))
        N.wk.wk))) :
    Formula Γ _)

/-- Substitution leaves `natTm m` unchanged. -/
@[derivNorm] theorem natTm_subst (m : Nat) {Γ Δ : List Ty} (s : Sub Γ Δ) :
    (natTm m (Γ := Γ)).subst s = natTm m (Γ := Δ) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg Tm.succ ih

/-- Numeral addition `natTm a + natTm b = natTm (a + b)` inside `Deriv`. -/
def natTm_addD (a : Nat) : ∀ (b : Nat) {Γ as : List Ty} {Δ : Ctx Γ as},
    Deriv Δ (.eq (.add (natTm a) (natTm b)) (natTm (a + b)))
  | 0, _, _, _ => Deriv.convAddZero (natTm a)
  | b + 1, _, _, _ =>
    Deriv.transE (Deriv.convAddSucc (natTm a) (natTm b))
      (Deriv.congSucc (natTm_addD a b))

/-- Numeral addition `natTm a + succ (natTm b) = natTm (a + b + 1)` inside `Deriv`. -/
def natTm_add_succD {Γ as : List Ty} {Δ : Ctx Γ as} (a b : Nat) :
    Deriv Δ (.eq (.add (natTm a) (.succ (natTm b))) (natTm (a + b + 1))) :=
  natTm_addD a (b + 1)

/-- **Prefix property of every well-formed `JExprN`, inside `Deriv`.** -/
def JExprN.prefixT (F : JExprN) (n : Nat) (hF : F.WF n) {Γ as : List Ty} {Δ : Ctx Γ as}
    (w w' : Tm Γ WTy) (N : Tm Γ .nat)
    (h : Deriv Δ (prefixAgreeN n w w' N)) :
    Deriv Δ (prefixAgree (F.toTm w) (F.toTm w') N) := by
  cases F with
  | var i =>
    have h1 := Deriv.allE (natTm i) h
    deriv_norm at h1
    have h2 := Deriv.allE (natTm (n - i - 1)) h1
    deriv_norm at h2
    have h_eq : Deriv Δ (.eq (.add (natTm i) (.succ (natTm (n - i - 1)))) (natTm n)) := by
      have heq : i + (n - i - 1) + 1 = n := by
        change i < n at hF
        omega
      have h_add := natTm_add_succD (Δ := Δ) i (n - i - 1)
      rwa [heq] at h_add
    exact Deriv.impE h2 h_eq
  | const _ => exact Deriv.allI (Deriv.allI (Deriv.impI (Deriv.eqRefl _)))
  | add a b =>
    exact prefixAgree_addT (a.toTm w) (a.toTm w') (b.toTm w) (b.toTm w') N
      (a.prefixT n hF.1 w w' N h) (b.prefixT n hF.2 w w' N h)
  | sub a b =>
    exact prefixAgree_subT (a.toTm w) (a.toTm w') (b.toTm w) (b.toTm w') N
      (a.prefixT n hF.1 w w' N h) (b.prefixT n hF.2 w w' N h)
  | mul a b =>
    exact prefixAgree_mulT (a.toTm w) (a.toTm w') (b.toTm w) (b.toTm w') N
      (a.prefixT n hF.1 w w' N h) (b.prefixT n hF.2 w w' N h)
  | integ a =>
    exact prefixAgree_integT (a.toTm w) (a.toTm w') N (a.prefixT n hF w w' N h)

#print axioms JExprN.prefixT

end HAomega
