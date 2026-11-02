/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.UniverseInvFun

/-!
# The local implicit function theorem in the universe

Given a flat system `sysX` in `x` (solution `X(x)`), a flat system `sysY` in `y`
(solution `Z(y)`), and a polynomial expression `E(X, Z)` in their variables with
constant coefficients (`E.WF (sysX.length + sysY.length)`, `E.ConstsConst`,
`E.NoInteg`), suppose that at `(x, y) = (0, 0)`:

    E(X(0), Z(0)) = 0,       E_y(X(0), Z(0)) ≠ 0.

Then the implicit equation `E(X(x), Z(y(x))) = 0` has a local formal power-series
solution `y ∈ InGPAC` with `y(0) = 0`.

**Construction (`impFunSys`).** Write `nX := sysX.length`, `nY := sysY.length`,
and let `Ex := impEx sysX E` and `Ey := impEy nX sysY E` be the partial symbolic
derivatives of `E` with respect to the `X`-variables (via `sysX`) and the
`Z`-variables (via `sysY`). Along `y(x)` with `W_w(x) := (Z_w ∘ y)(x)`,
`u(x) := 1 / Ey(X(x), W(x))`, and `y'(x) = -Ex(X(x), W(x)) · u(x)`:

    X_i = A_{X,i} + ∫ F_{X,i}(X)                        (0 ≤ i < nX),
    W_w = A_{Y,w} + ∫ F_{Y,w}(W) · (−Ex(X, W) · u)      (0 ≤ w < nY),
    y   = 0 + ∫ (−Ex(X, W) · u)                         (index nX + nY),
    u   = 1 / Ey(X(0), Z(0)) + ∫ (−u² · H(X, W, u))     (index nX + nY + 1),

where `H := Ey.derivSym impSysXY` is the symbolic derivative of `Ey(X, W)` along
the `(X, W)` equations. Then `(Ey · u)' = H · u · (1 − Ey · u)` with initial
value `1` forces `Ey(X, W) · u = 1` by uniqueness (`inv_zero_of_linear_rec`), so
`(E(X, W))' = Ex + Ey · (−Ex · u) = Ex · (1 − Ey · u) = 0` and `E(X, Z ∘ y) = 0`.
-/

namespace HAomega

/-- Partial symbolic derivative of `F : JExprN` with respect to the `x`-system
variables `0, …, sysX.length - 1` (treating variables `≥ sysX.length` as constant). -/
def impEx (sysX : List (Tm [] JetTy × JExprN)) : JExprN → JExprN
  | .var u =>
      if u < sysX.length then (sysX.getD u (tmZeroJet, .const tmZeroJet)).2
      else .const tmZeroJet
  | .const _ => .const tmZeroJet
  | .add a b => .add (impEx sysX a) (impEx sysX b)
  | .sub a b => .sub (impEx sysX a) (impEx sysX b)
  | .mul a b => .add (.mul (impEx sysX a) b) (.mul a (impEx sysX b))
  | .integ a => a

/-- Partial symbolic derivative of `F : JExprN` with respect to the `y`-system
variables `nX, …, nX + sysY.length - 1` (treating variables `< nX` as constant). -/
def impEy (nX : Nat) (sysY : List (Tm [] JetTy × JExprN)) : JExprN → JExprN
  | .var u =>
      if u < nX then .const tmZeroJet
      else ((sysY.getD (u - nX) (tmZeroJet, .const tmZeroJet)).2).shiftVars nX
  | .const _ => .const tmZeroJet
  | .add a b => .add (impEy nX sysY a) (impEy nX sysY b)
  | .sub a b => .sub (impEy nX sysY a) (impEy nX sysY b)
  | .mul a b => .add (.mul (impEy nX sysY a) b) (.mul a (impEy nX sysY b))
  | .integ a => a

/-- The right-hand side `−Ex(X, W) · u` for `y'`. -/
def impYrhs (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) : JExprN :=
  let u : JExprN := .var (sysX.length + sysY.length + 1)
  .sub (.const tmZeroJet) (.mul (impEx sysX E) u)

/-- The first `sysX.length + sysY.length` equations of `impFunSys`: `sysX` followed
by `sysY` shifted and scaled by `impYrhs`. -/
def impSysXY (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) :
    List (Tm [] JetTy × JExprN) :=
  let nX := sysX.length
  let yrhs := impYrhs sysX sysY E
  sysX ++ sysY.map (fun p ↦ (p.1, .mul (p.2.shiftVars nX) yrhs))

/-- The compiled polynomial ODE system for the implicit equation `E(X(x), Z(y(x))) = 0`:
variables `0 .. nX - 1` are `X`, variables `nX .. nX + nY - 1` are `W = Z ∘ y`,
variable `nX + nY` is `y`, and variable `nX + nY + 1` is `u = 1 / Ey(X, W)`. -/
def impFunSys (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) :
    List (Tm [] JetTy × JExprN) :=
  let xy := impSysXY sysX sysY E
  let Ey := impEy sysX.length sysY E
  let H := Ey.derivSym xy
  let u : JExprN := .var (sysX.length + sysY.length + 1)
  let yrhs := impYrhs sysX sysY E
  xy ++
    [(tmZeroJet, yrhs),
     (.app tmInv0 (Ey.toTm (initN xy)),
      .sub (.const tmZeroJet) (.mul (.mul u u) H))]

/-- The combined state `(solN sysX, (solN sysY) ∘ y)` on `0 .. nX + nY - 1`. -/
def impCombinedState (sysX sysY : List (Tm [] JetTy × JExprN)) (y : Nat → Q) :
    Nat → Nat → Q :=
  fun v n ↦
    if v < sysX.length then solN sysX v n
    else (Jet.compZero ⟨solN sysY (v - sysX.length)⟩ ⟨y⟩).coeff n

/-- Evaluating a bivariate expression `F` on `(solN sysX, (solN sysY) ∘ y)`. -/
def impEval (sysX sysY : List (Tm [] JetTy × JExprN)) (F : JExprN) (y : Nat → Q) :
    Nat → Q :=
  (F.toTm (.var .here)).eval (Env.cons (σ := WTy) (impCombinedState sysX sysY y) Env.nil)

/-! ## Structural properties of `impEx`, `impEy`, `impSysXY`, and `impFunSys` -/

theorem imp_impEx_wf (sysX : List (Tm [] JetTy × JExprN)) (nY : Nat)
    (hwfX : ∀ p ∈ sysX, p.2.WF sysX.length)
    (F : JExprN) (hF : F.WF (sysX.length + nY)) :
    (impEx sysX F).WF (sysX.length + nY) := by
  induction F with
  | var u =>
    dsimp only [impEx]
    split
    · rename_i hu
      rw [uDeriv_getD_eq_getElem sysX _ u hu]
      exact (hwfX sysX[u] (List.getElem_mem hu)).mono (by omega)
    · trivial
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | mul _ _ iha ihb => exact ⟨⟨iha hF.1, hF.2⟩, ⟨hF.1, ihb hF.2⟩⟩
  | integ _ _ => exact hF

theorem imp_impEx_constsConst (sysX : List (Tm [] JetTy × JExprN)) {nY : Nat}
    (hgpacX : GPACSys sysX) (F : JExprN) (hF_wf : F.WF (sysX.length + nY))
    (hF_cc : F.ConstsConst) :
    (impEx sysX F).ConstsConst := by
  induction F with
  | var u =>
    dsimp only [impEx]
    split
    · rename_i hu
      rw [uDeriv_getD_eq_getElem sysX _ u hu]
      exact (hgpacX sysX[u] (List.getElem_mem hu)).2.2
    · exact gpac_isConstJet_zero
  | const _ => exact gpac_isConstJet_zero
  | add _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | mul _ _ iha ihb =>
    exact ⟨⟨iha hF_wf.1 hF_cc.1, hF_cc.2⟩, ⟨hF_cc.1, ihb hF_wf.2 hF_cc.2⟩⟩
  | integ _ _ => exact hF_cc

theorem imp_impEy_wf (nX : Nat) (sysY : List (Tm [] JetTy × JExprN))
    (hwfY : ∀ p ∈ sysY, p.2.WF sysY.length)
    (F : JExprN) (hF : F.WF (nX + sysY.length)) :
    (impEy nX sysY F).WF (nX + sysY.length) := by
  induction F with
  | var u =>
    dsimp only [impEy]
    split
    · trivial
    · rename_i hu
      change u < nX + sysY.length at hF
      have hw : u - nX < sysY.length := by omega
      rw [uDeriv_getD_eq_getElem sysY _ (u - nX) hw]
      exact (sysY[u - nX].2).shiftVars_wf nX sysY.length (hwfY sysY[u - nX] (List.getElem_mem hw))
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | mul _ _ iha ihb => exact ⟨⟨iha hF.1, hF.2⟩, ⟨hF.1, ihb hF.2⟩⟩
  | integ _ _ => exact hF

theorem imp_impEy_constsConst (nX : Nat) (sysY : List (Tm [] JetTy × JExprN))
    (hgpacY : GPACSys sysY) (F : JExprN) (hF_wf : F.WF (nX + sysY.length))
    (hF_cc : F.ConstsConst) :
    (impEy nX sysY F).ConstsConst := by
  induction F with
  | var u =>
    dsimp only [impEy]
    split
    · exact gpac_isConstJet_zero
    · rename_i hu
      change u < nX + sysY.length at hF_wf
      have hw : u - nX < sysY.length := by omega
      rw [uDeriv_getD_eq_getElem sysY _ (u - nX) hw]
      exact gpac_shiftVars_constsConst sysY[u - nX].2 nX
        (hgpacY sysY[u - nX] (List.getElem_mem hw)).2.2
  | const _ => exact gpac_isConstJet_zero
  | add _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | mul _ _ iha ihb =>
    exact ⟨⟨iha hF_wf.1 hF_cc.1, hF_cc.2⟩, ⟨hF_cc.1, ihb hF_wf.2 hF_cc.2⟩⟩
  | integ _ _ => exact hF_cc

theorem imp_impSysXY_length (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) :
    (impSysXY sysX sysY E).length = sysX.length + sysY.length := by
  simp [impSysXY]

theorem imp_impFunSys_length (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) :
    (impFunSys sysX sysY E).length = sysX.length + sysY.length + 2 := by
  simp [impFunSys, imp_impSysXY_length]

theorem imp_impSysXY_getElem_lt_x (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN)
    (i : Nat) (hi : i < sysX.length) :
    (impSysXY sysX sysY E)[i]'(by rw [imp_impSysXY_length]; omega) = sysX[i] := by
  simp only [impSysXY]
  exact List.getElem_append_left hi

theorem imp_impSysXY_getElem_ge_x (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN)
    (v : Nat) (hvX : ¬ v < sysX.length) (hvY : v < sysX.length + sysY.length) :
    (impSysXY sysX sysY E)[v]'(by rw [imp_impSysXY_length]; exact hvY) =
      ((sysY[v - sysX.length]'(by omega)).1,
       .mul ((sysY[v - sysX.length]'(by omega)).2.shiftVars sysX.length) (impYrhs sysX sysY E)) := by
  simp only [impSysXY]
  rw [List.getElem_append_right (by omega), List.getElem_map]

theorem imp_impFunSys_getElem_xy (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN)
    (v : Nat) (hv : v < sysX.length + sysY.length) :
    (impFunSys sysX sysY E)[v]'(by rw [imp_impFunSys_length]; omega) =
      (impSysXY sysX sysY E)[v]'(by rw [imp_impSysXY_length]; exact hv) := by
  simp only [impFunSys]
  exact List.getElem_append_left (by rw [imp_impSysXY_length]; exact hv)

theorem imp_impFunSys_getElem_y_var (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) :
    (impFunSys sysX sysY E)[sysX.length + sysY.length]'(by rw [imp_impFunSys_length]; omega) =
      (tmZeroJet, impYrhs sysX sysY E) := by
  simp only [impFunSys]
  rw [List.getElem_append_right (by rw [imp_impSysXY_length])]
  simp [imp_impSysXY_length]

theorem imp_impFunSys_getElem_u_var (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) :
    let xy := impSysXY sysX sysY E
    let Ey := impEy sysX.length sysY E
    let H := Ey.derivSym xy
    let u : JExprN := .var (sysX.length + sysY.length + 1)
    (impFunSys sysX sysY E)[sysX.length + sysY.length + 1]'(by rw [imp_impFunSys_length]; omega) =
      (.app tmInv0 (Ey.toTm (initN xy)),
       .sub (.const tmZeroJet) (.mul (.mul u u) H)) := by
  dsimp only
  simp only [impFunSys]
  rw [List.getElem_append_right (by rw [imp_impSysXY_length]; omega)]
  simp [imp_impSysXY_length]

/-- If `F.WF xs.length`, then `F.derivSym (xs ++ ys) = F.derivSym xs`. -/
theorem imp_derivSym_append_left (xs ys : List (Tm [] JetTy × JExprN))
    (F : JExprN) (hF : F.WF xs.length) :
    F.derivSym (xs ++ ys) = F.derivSym xs := by
  induction F with
  | var u =>
    dsimp only [JExprN.derivSym]
    rw [sfst_getD_append_left xs ys _ u hF]
  | const _ => rfl
  | add _ _ iha ihb => exact congrArg₂ JExprN.add (iha hF.1) (ihb hF.2)
  | sub _ _ iha ihb => exact congrArg₂ JExprN.sub (iha hF.1) (ihb hF.2)
  | mul _ _ iha ihb =>
    exact congrArg₂ JExprN.add
      (congrArg (JExprN.mul · _) (iha hF.1))
      (congrArg (JExprN.mul _) (ihb hF.2))
  | integ _ _ => rfl

/-- Well-formedness of `F.derivSym sys` when `sys` has `WF M` right-hand sides and `F.WF sys.length` with `sys.length ≤ M`. -/
theorem imp_derivSym_wf_bound (sys : List (Tm [] JetTy × JExprN)) (M : Nat)
    (hwf : ∀ p ∈ sys, p.2.WF M) (F : JExprN) (hF : F.WF sys.length) (hM : sys.length ≤ M) :
    (F.derivSym sys).WF M := by
  induction F with
  | var u =>
    dsimp only [JExprN.derivSym]
    rw [uDeriv_getD_eq_getElem sys _ u hF]
    exact ⟨trivial, hwf sys[u] (List.getElem_mem hF)⟩
  | const _ => trivial
  | add _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF.1, ihb hF.2⟩
  | mul _ _ iha ihb =>
    exact ⟨⟨iha hF.1, hF.2.mono hM⟩, ⟨hF.1.mono hM, ihb hF.2⟩⟩
  | integ _ _ => exact hF.mono hM

/-- `ConstsConst` preservation for `F.derivSym sys` when every equation in `sys` has `IsConstJet p.1 ∧ p.2.ConstsConst`. -/
theorem imp_derivSym_constsConst (sys : List (Tm [] JetTy × JExprN))
    (hcc : ∀ p ∈ sys, IsConstJet p.1 ∧ p.2.ConstsConst)
    (F : JExprN) (hF_wf : F.WF sys.length) (hF_cc : F.ConstsConst) :
    (F.derivSym sys).ConstsConst := by
  induction F with
  | var u =>
    dsimp only [JExprN.derivSym]
    rw [uDeriv_getD_eq_getElem sys _ u hF_wf]
    have hp := hcc sys[u] (List.getElem_mem hF_wf)
    exact ⟨gpac_isConstJet_deriv hp.1, hp.2⟩
  | const c => exact gpac_isConstJet_deriv hF_cc
  | add _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | sub _ _ iha ihb => exact ⟨iha hF_wf.1 hF_cc.1, ihb hF_wf.2 hF_cc.2⟩
  | mul _ _ iha ihb =>
    exact ⟨⟨iha hF_wf.1 hF_cc.1, hF_cc.2⟩, ⟨hF_cc.1, ihb hF_wf.2 hF_cc.2⟩⟩
  | integ _ _ => exact hF_cc

/-- Well-formedness of `impFunSys sysX sysY E`. -/
theorem imp_impFunSys_wf (sysX sysY : List (Tm [] JetTy × JExprN))
    (hwfX : ∀ p ∈ sysX, p.2.WF sysX.length)
    (hwfY : ∀ p ∈ sysY, p.2.WF sysY.length)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) :
    ∀ p ∈ impFunSys sysX sysY E, p.2.WF (impFunSys sysX sysY E).length := by
  rw [imp_impFunSys_length]
  let nX := sysX.length
  let nY := sysY.length
  have hu_wf : (JExprN.var (nX + nY + 1)).WF (nX + nY + 2) := by
    show nX + nY + 1 < nX + nY + 2; omega
  have hEx_wf : (impEx sysX E).WF (nX + nY + 2) :=
    (imp_impEx_wf sysX nY hwfX E hE_wf).mono (by omega)
  have hyrhs_wf : (impYrhs sysX sysY E).WF (nX + nY + 2) :=
    ⟨trivial, hEx_wf, hu_wf⟩
  have hxy_wf : ∀ p ∈ impSysXY sysX sysY E, p.2.WF (nX + nY + 2) := by
    intro p hp
    simp only [impSysXY, List.mem_append, List.mem_map] at hp
    rcases hp with hpX | ⟨q, hq, rfl⟩
    · exact (hwfX p hpX).mono (by omega)
    · exact ⟨(q.2.shiftVars_wf nX nY (hwfY q hq)).mono (by omega), hyrhs_wf⟩
  have hEy_wf : (impEy nX sysY E).WF (impSysXY sysX sysY E).length := by
    rw [imp_impSysXY_length]
    exact imp_impEy_wf nX sysY hwfY E hE_wf
  have hH_wf : ((impEy nX sysY E).derivSym (impSysXY sysX sysY E)).WF (nX + nY + 2) :=
    imp_derivSym_wf_bound (impSysXY sysX sysY E) (nX + nY + 2) hxy_wf
      (impEy nX sysY E) hEy_wf (by rw [imp_impSysXY_length]; omega)
  intro p hp
  simp only [impFunSys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hpxy | rfl | rfl
  · exact hxy_wf p hpxy
  · exact hyrhs_wf
  · exact ⟨trivial, ⟨hu_wf, hu_wf⟩, hH_wf⟩

/-- `impFunSys sysX sysY E` is a `GPACSys`. -/
theorem imp_gpac_impFunSys (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) (hE_cc : E.ConstsConst) :
    GPACSys (impFunSys sysX sysY E) := by
  let nX := sysX.length
  let nY := sysY.length
  have hwfX := gpac_wf hX
  have hwfY := gpac_wf hY
  have hEx_cc : (impEx sysX E).ConstsConst := imp_impEx_constsConst sysX hX E hE_wf hE_cc
  have hyrhs_cc : (impYrhs sysX sysY E).ConstsConst :=
    ⟨gpac_isConstJet_zero, hEx_cc, trivial⟩
  have hxy_cc : ∀ p ∈ impSysXY sysX sysY E, IsConstJet p.1 ∧ p.2.ConstsConst := by
    intro p hp
    simp only [impSysXY, List.mem_append, List.mem_map] at hp
    rcases hp with hpX | ⟨q, hq, rfl⟩
    · exact (hX p hpX).2
    · have hqY := hY q hq
      exact ⟨hqY.2.1, gpac_shiftVars_constsConst q.2 nX hqY.2.2, hyrhs_cc⟩
  have hEy_wf : (impEy nX sysY E).WF (impSysXY sysX sysY E).length := by
    rw [imp_impSysXY_length]
    exact imp_impEy_wf nX sysY hwfY E hE_wf
  have hEy_cc : (impEy nX sysY E).ConstsConst :=
    imp_impEy_constsConst nX sysY hY E hE_wf hE_cc
  have hH_cc := imp_derivSym_constsConst (impSysXY sysX sysY E) hxy_cc
    (impEy nX sysY E) hEy_wf hEy_cc
  intro p hp
  refine ⟨imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf p hp, ?_⟩
  simp only [impFunSys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hpxy | rfl | rfl
  · exact hxy_cc p hpxy
  · exact ⟨gpac_isConstJet_zero, hyrhs_cc⟩
  · exact ⟨inv_isConstJet_inv0 _, gpac_isConstJet_zero, ⟨trivial, trivial⟩, hH_cc⟩

/-! ## Target state and fixed-point identification -/

/-- Target state for `impFunSys sysX sysY E`: `solN sysX` on `[0, nX)`,
`Jet.compZero ⟨solN sysY (v - nX)⟩ ⟨y⟩` on `[nX, nX + nY)`, and `solN S` at `≥ nX + nY`. -/
def impTargetState (sysX sysY : List (Tm [] JetTy × JExprN)) (E : JExprN) :
    Nat → Nat → Q :=
  let S := impFunSys sysX sysY E
  let nX := sysX.length
  let nY := sysY.length
  fun v n ↦
    if v < nX then solN sysX v n
    else if v < nX + nY then (Jet.compZero ⟨solN sysY (v - nX)⟩ ⟨solN S (nX + nY)⟩).coeff n
    else solN S v n

theorem imp_solN_y_zero_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hwfX : ∀ p ∈ sysX, p.2.WF sysX.length)
    (hwfY : ∀ p ∈ sysY, p.2.WF sysY.length)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) :
    (solN (impFunSys sysX sysY E) (sysX.length + sysY.length) 0).val = 0 := by
  let S := impFunSys sysX sysY E
  have hy : sysX.length + sysY.length < S.length := by rw [imp_impFunSys_length]; omega
  rw [uMul_solN_zero_val S (imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf) _ hy,
      imp_impFunSys_getElem_y_var sysX sysY E]
  exact Q.val_ofNat 0

theorem imp_solN_y_deriv_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hwfX : ∀ p ∈ sysX, p.2.WF sysX.length)
    (hwfY : ∀ p ∈ sysY, p.2.WF sysY.length)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) (j : Nat) :
    let S := impFunSys sysX sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    (((tmJetDeriv (Γ := [])).eval Env.nil) (solN S (sysX.length + sysY.length)) j).val =
      ((((impYrhs sysX sysY E).toTm (.var .here)).eval eS) j).val := by
  intro S eS
  have hy : sysX.length + sysY.length < S.length := by rw [imp_impFunSys_length]; omega
  have hderiv := uMul_solN_deriv_val S (imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf) _ hy j
  rw [imp_impFunSys_getElem_y_var sysX sysY E] at hderiv
  have h0 : (((tmJetDeriv (Γ := [])).eval Env.nil) (tmZeroJet.eval Env.nil) j).val = 0 :=
    gpac_deriv_const_val gpac_isConstJet_zero j
  dsimp only at hderiv
  rw [hderiv, h0, zero_add]

theorem imp_eqStepEval_lt_x_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (E : JExprN)
    (i : Nat) (hi : i < sysX.length) (n : Nat) :
    let S := impFunSys sysX sysY E
    let hiS : i < S.length := by rw [imp_impFunSys_length]; omega
    (eqStepEval S[i] (impTargetState sysX sysY E) n).val =
      (impTargetState sysX sysY E i n).val := by
  intro S hiS
  have hwfX := gpac_wf hX
  have hi_xy : i < sysX.length + sysY.length := by omega
  rw [imp_impFunSys_getElem_xy sysX sysY E i hi_xy,
      imp_impSysXY_getElem_lt_x sysX sysY E i hi]
  have h_eq : eqStepEval sysX[i] (impTargetState sysX sysY E) = eqStepEval sysX[i] (solN sysX) := by
    refine eqStepEval_of_eq_below sysX[i] sysX.length (hwfX sysX[i] (List.getElem_mem hi))
      (impTargetState sysX sysY E) (solN sysX) (fun u hu ↦ ?_)
    funext m
    unfold impTargetState
    exact if_pos hu
  rw [h_eq, ← genStepN_eval_getElem sysX (solN sysX) i hi, solN_fixed sysX hwfX i hi n]
  unfold impTargetState
  rw [if_pos hi]

theorem imp_eqStepEval_y_block_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY) (hnoY : ∀ p ∈ sysY, p.2.NoInteg)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length))
    (v : Nat) (hvX : ¬ v < sysX.length) (hvY : v < sysX.length + sysY.length) (n : Nat)
    (h_agree : ∀ u < sysX.length + sysY.length + 2, ∀ k < n,
      (solN (impFunSys sysX sysY E) u k).val = (impTargetState sysX sysY E u k).val) :
    let S := impFunSys sysX sysY E
    let hvS : v < S.length := by rw [imp_impFunSys_length]; omega
    (eqStepEval S[v] (impTargetState sysX sysY E) n).val =
      (impTargetState sysX sysY E v n).val := by
  intro S hvS
  have hwfX := gpac_wf hX
  have hwfY := gpac_wf hY
  let w := v - sysX.length
  have hw : w < sysY.length := by omega
  rw [imp_impFunSys_getElem_xy sysX sysY E v hvY,
      imp_impSysXY_getElem_ge_x sysX sysY E v hvX hvY]
  unfold impTargetState
  rw [if_neg hvX, if_pos hvY]
  let T := impTargetState sysX sysY E
  let eT : Env [WTy] := Env.cons (σ := WTy) T Env.nil
  let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
  let Y : Jet := ⟨solN S (sysX.length + sysY.length)⟩
  let Fw : Jet := ⟨solN sysY w⟩
  have hp_gpac := hY sysY[w] (List.getElem_mem hw)
  have hp_no := hnoY sysY[w] (List.getElem_mem hw)
  let W_comp : Nat → Nat → Q := fun u ↦ (Jet.compZero ⟨solN sysY u⟩ Y).coeff
  have hTW : ∀ u < sysY.length, T (sysX.length + u) = W_comp u := by
    intro u hu
    funext m
    unfold T impTargetState
    rw [if_neg (by omega), if_pos (by omega)]
    have : sysX.length + u - sysX.length = u := by omega
    rw [this]
  cases n with
  | zero =>
    unfold eqStepEval
    change (Q.add (sysY[w].1.eval Env.nil 0) (Q.ofNat 0)).val = ((Jet.compZero Fw Y).coeff 0).val
    have h0 : (Q.add (sysY[w].1.eval Env.nil 0) (Q.ofNat 0)).val = (sysY[w].1.eval Env.nil 0).val := by
      rw [Q.val_add, Q.val_ofNat]; ring
    rw [h0, ← uMul_solN_zero_val sysY hwfY w hw,
        compZero_coeff_val_eq_sum Fw Y 0 0 (le_refl 0),
        Finset.sum_range_one]
    dsimp [Fw, hPow]
    rw [Q.val_ofNat]
    ring
  | succ j =>
    have hF_eval : ∀ m < j + 1,
        ((((sysY[w].2.shiftVars sysX.length).toTm (.var .here)).eval eT) m).val =
          ((Jet.compZero Fw.deriv Y).coeff m).val := by
      intro m _
      have hsh := sysY[w].2.shiftVars_toTm_eval sysX.length sysY.length hp_gpac.1
        eT (Env.cons (σ := WTy) W_comp Env.nil) (.var .here) (.var .here) hTW
      rw [hsh, comp_toTm_compZero_val sysY Y sysY[w].2 hp_gpac.2.2 hp_no m]
      refine compZero_congr_val
        ⟨(sysY[w].2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sysY) Env.nil)⟩
        Fw.deriv Y (fun k ↦ ?_) m
      have hderiv_w := uMul_solN_deriv_val sysY hwfY w hw k
      have hA_zero := gpac_deriv_const_val hp_gpac.2.1 k
      change (((sysY[w].2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sysY) Env.nil)) k).val =
        (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sysY w) k).val
      linarith
    have hyrhs_wf : (impYrhs sysX sysY E).WF (sysX.length + sysY.length + 2) := by
      refine ⟨trivial, (imp_impEx_wf sysX sysY.length hwfX E hE_wf).mono (by omega), ?_⟩
      show sysX.length + sysY.length + 1 < sysX.length + sysY.length + 2
      omega
    have hyrhs_eval : ∀ m < j + 1,
        ((((impYrhs sysX sysY E).toTm (.var .here)).eval eT) m).val =
          (Y.deriv.coeff m).val := by
      intro m hm
      have hag := (impYrhs sysX sysY E).toTm_agreeV (sysX.length + sysY.length + 2) hyrhs_wf
        eT eS (.var .here) (.var .here) (j + 1)
        (fun u hu k hk ↦ (h_agree u hu k hk).symm) m hm
      exact hag.trans (imp_solN_y_deriv_val sysX sysY hwfX hwfY E hE_wf m).symm
    have hmul :
        ((((JExprN.mul (sysY[w].2.shiftVars sysX.length) (impYrhs sysX sysY E)).toTm (.var .here)).eval eT) j).val =
          (((Jet.compZero Fw Y).deriv).coeff j).val := by
      have hm := tmJetMul_agreeV Env.nil Env.nil (j + 1)
        (((sysY[w].2.shiftVars sysX.length).toTm (.var .here)).eval eT)
        (Jet.compZero Fw.deriv Y).coeff
        (((impYrhs sysX sysY E).toTm (.var .here)).eval eT)
        Y.deriv.coeff
        hF_eval hyrhs_eval j (Nat.lt_succ_self j)
      rw [ivf_toTm_mul_eval, hm, inv_jetMul_comm_val, tmJetMul_eval, ← compZero_deriv_val Fw Y j]
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    have hne_rat : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
    unfold eqStepEval
    change (Q.add (sysY[w].1.eval Env.nil (j + 1))
      (Q.div ((((JExprN.mul (sysY[w].2.shiftVars sysX.length) (impYrhs sysX sysY E)).toTm (.var .here)).eval eT) j)
        (Q.ofNat (j + 1)))).val = ((Jet.compZero Fw Y).coeff (j + 1)).val
    rw [Q.val_add, hp_gpac.2.1 j, zero_add, Q.val_div _ _ hne, Q.val_ofNat, hmul]
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
    field_simp

/-- `solN (impFunSys sysX sysY E)` agrees in value with `impTargetState sysX sysY E` at all variables and degrees. -/
theorem imp_solN_eq_target_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY) (hnoY : ∀ p ∈ sysY, p.2.NoInteg)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) (m : Nat) :
    ∀ v, (solN (impFunSys sysX sysY E) v m).val = (impTargetState sysX sysY E v m).val := by
  let S := impFunSys sysX sysY E
  have hwfS := imp_impFunSys_wf sysX sysY (gpac_wf hX) (gpac_wf hY) E hE_wf
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro v
    by_cases hvX : v < sysX.length
    · have hvS : v < S.length := by rw [imp_impFunSys_length]; omega
      have hag := genStepN_agreeV_succ S hwfS m (solN S) (impTargetState sysX sysY E)
        (fun u _ k hk ↦ ih k hk u) v m (Nat.lt_succ_self m)
      rw [← solN_fixed S hwfS v hvS m, hag, genStepN_eval_getElem S _ v hvS]
      exact imp_eqStepEval_lt_x_val sysX sysY hX E v hvX m
    · by_cases hvY : v < sysX.length + sysY.length
      · have hvS : v < S.length := by rw [imp_impFunSys_length]; omega
        have hag := genStepN_agreeV_succ S hwfS m (solN S) (impTargetState sysX sysY E)
          (fun u _ k hk ↦ ih k hk u) v m (Nat.lt_succ_self m)
        rw [← solN_fixed S hwfS v hvS m, hag, genStepN_eval_getElem S _ v hvS]
        exact imp_eqStepEval_y_block_val sysX sysY hX hY hnoY E hE_wf v hvX hvY m
          (fun u _ k hk ↦ ih k hk u)
      · unfold impTargetState
        rw [if_neg hvX, if_neg hvY]

/-- Evaluating any `F` (`F.WF (nX + nY)`) on `solN (impFunSys sysX sysY E)` agrees in value with `impEval sysX sysY F y`. -/
theorem imp_toTm_solN_eq_impEval_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY) (hnoY : ∀ p ∈ sysY, p.2.NoInteg)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length))
    (F : JExprN) (hF_wf : F.WF (sysX.length + sysY.length)) (m : Nat) :
    let S := impFunSys sysX sysY E
    let y := solN S (sysX.length + sysY.length)
    (((F.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN S) Env.nil)) m).val =
      (impEval sysX sysY F y m).val := by
  intro S y
  refine F.toTm_agreeV (sysX.length + sysY.length) hF_wf
    (Env.cons (σ := WTy) (solN S) Env.nil)
    (Env.cons (σ := WTy) (impCombinedState sysX sysY y) Env.nil)
    (.var .here) (.var .here) (m + 1) (fun v hv k _ ↦ ?_) m (Nat.lt_succ_self m)
  change (solN S v k).val = (impCombinedState sysX sysY y v k).val
  rw [imp_solN_eq_target_val sysX sysY hX hY hnoY E hE_wf k v]
  unfold impTargetState impCombinedState
  by_cases hvX : v < sysX.length
  · rw [if_pos hvX, if_pos hvX]
  · rw [if_neg hvX, if_neg hvX, if_pos hv]

/-! ## Directional derivative decomposition and `Ey · u = 1` -/

/-- Bilinear Cauchy-product decomposition for the Leibniz rule of `impEx` and `impEy`. -/
theorem imp_mul_decomp_val (a b a' b' ax ay bx by_ u : Nat → Q) (n : Nat)
    (ha : ∀ m ≤ n,
      (Q.add (ax m) (((tmJetMul (Γ := [])).eval Env.nil) ay u m)).val = (a' m).val)
    (hb : ∀ m ≤ n,
      (Q.add (bx m) (((tmJetMul (Γ := [])).eval Env.nil) by_ u m)).val = (b' m).val) :
    let mul := (tmJetMul (Γ := [])).eval Env.nil
    (Q.add (mul a' b n) (mul a b' n)).val =
      (Q.add (Q.add (mul ax b n) (mul a bx n))
        (mul (fun k ↦ Q.add (mul ay b k) (mul a by_ k)) u n)).val := by
  intro mul
  have h1 : (mul a' b n).val = (mul ax b n).val + (mul (mul ay u) b n).val := by
    rw [inv_jetMul_val, inv_jetMul_val, inv_jetMul_val, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hai := ha i hi_le
    rw [Q.val_add] at hai
    rw [← hai]
    ring
  have h2 : (mul a b' n).val = (mul a bx n).val + (mul a (mul by_ u) n).val := by
    rw [inv_jetMul_val, inv_jetMul_val, inv_jetMul_val, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hni_le : n - i ≤ n := Nat.sub_le n i
    have hbi := hb (n - i) hni_le
    rw [Q.val_add] at hbi
    rw [← hbi]
    ring
  have h3 : (mul (mul ay u) b n).val = (mul (mul ay b) u n).val := by
    rw [inv_jetMul_comm_val (mul ay u) b n,
        ← inv_jetMul_assoc_val b ay u n]
    refine tmJetMul_agreeV Env.nil Env.nil (n + 1)
      (mul b ay) (mul ay b) u u
      (fun m _ ↦ inv_jetMul_comm_val b ay m) (fun _ _ ↦ rfl)
      n (Nat.lt_succ_self n)
  have h4 : (mul a (mul by_ u) n).val = (mul (mul a by_) u n).val :=
    (inv_jetMul_assoc_val a by_ u n).symm
  have h5 : (mul (fun k ↦ Q.add (mul ay b k) (mul a by_ k)) u n).val =
      (mul (mul ay b) u n).val + (mul (mul a by_) u n).val := by
    rw [inv_jetMul_val, inv_jetMul_val, inv_jetMul_val, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Q.val_add]
    ring
  simp only [Q.val_add]
  linarith

/-- For any `F` (`F.WF (nX + nY)`, `F.ConstsConst`, `F.NoInteg`), `F.derivSym (impSysXY sysX sysY E)`
decomposes in value into `impEx sysX F + impEy nX sysY F · impYrhs sysX sysY E`. -/
theorem imp_derivSym_decomp_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY) (E : JExprN)
    (F : JExprN) (hF_wf : F.WF (sysX.length + sysY.length))
    (hF_cc : F.ConstsConst) (hF_no : F.NoInteg)
    (W : Nat → Nat → Q) (n : Nat) :
    let eW : Env [WTy] := Env.cons (σ := WTy) W Env.nil
    let mul := (tmJetMul (Γ := [])).eval Env.nil
    let dF := ((F.derivSym (impSysXY sysX sysY E)).toTm (.var .here)).eval eW
    let Fx := ((impEx sysX F).toTm (.var .here)).eval eW
    let Fy := ((impEy sysX.length sysY F).toTm (.var .here)).eval eW
    let yrhs := ((impYrhs sysX sysY E).toTm (.var .here)).eval eW
    (dF n).val = (Q.add (Fx n) (mul Fy yrhs n)).val := by
  intro eW mul
  induction F generalizing n with
  | var u =>
    dsimp only [JExprN.derivSym, impEx, impEy]
    have hu_xy : u < (impSysXY sysX sysY E).length := by
      rw [imp_impSysXY_length]; exact hF_wf
    rw [uDeriv_getD_eq_getElem (impSysXY sysX sysY E) _ u hu_xy]
    by_cases huX : u < sysX.length
    · rw [if_pos huX, if_pos huX,
          imp_impSysXY_getElem_lt_x sysX sysY E u huX,
          uDeriv_getD_eq_getElem sysX _ u huX]
      have hpX := hX sysX[u] (List.getElem_mem huX)
      have hA0 : (((JExprN.const (.app tmJetDeriv sysX[u].1)).toTm (.var .here)).eval eW n).val = 0 := by
        dsimp only [JExprN.toTm]
        rw [closedWk_eval (.app tmJetDeriv sysX[u].1) eW]
        exact gpac_deriv_const_val hpX.2.1 n
      have h0_mul : (mul (((JExprN.const tmZeroJet).toTm (.var .here)).eval eW)
          (((impYrhs sysX sysY E).toTm (.var .here)).eval eW) n).val = 0 := by
        rw [inv_jetMul_val]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        dsimp only [JExprN.toTm]
        rw [closedWk_eval tmZeroJet eW]
        have hz : (tmZeroJet.eval Env.nil i).val = 0 := Q.val_ofNat 0
        rw [hz, zero_mul]
      change (Q.add (((JExprN.const (.app tmJetDeriv sysX[u].1)).toTm (.var .here)).eval eW n)
          (((sysX[u].2).toTm (.var .here)).eval eW n)).val =
        (Q.add (((sysX[u].2).toTm (.var .here)).eval eW n)
          (mul (((JExprN.const tmZeroJet).toTm (.var .here)).eval eW)
            (((impYrhs sysX sysY E).toTm (.var .here)).eval eW) n)).val
      rw [Q.val_add, Q.val_add, hA0, h0_mul, zero_add, add_zero]
    · rw [if_neg huX, if_neg huX]
      change u < sysX.length + sysY.length at hF_wf
      have hw : u - sysX.length < sysY.length := by omega
      rw [imp_impSysXY_getElem_ge_x sysX sysY E u huX hF_wf,
          uDeriv_getD_eq_getElem sysY _ (u - sysX.length) hw]
      have hpY := hY sysY[u - sysX.length] (List.getElem_mem hw)
      have hA0 : (((JExprN.const (.app tmJetDeriv sysY[u - sysX.length].1)).toTm (.var .here)).eval eW n).val = 0 := by
        dsimp only [JExprN.toTm]
        rw [closedWk_eval (.app tmJetDeriv sysY[u - sysX.length].1) eW]
        exact gpac_deriv_const_val hpY.2.1 n
      have hz0 : (((JExprN.const tmZeroJet).toTm (.var .here)).eval eW n).val = 0 := by
        dsimp only [JExprN.toTm]
        rw [closedWk_eval tmZeroJet eW]
        exact Q.val_ofNat 0
      change (Q.add (((JExprN.const (.app tmJetDeriv sysY[u - sysX.length].1)).toTm (.var .here)).eval eW n)
          ((((JExprN.mul (sysY[u - sysX.length].2.shiftVars sysX.length) (impYrhs sysX sysY E)).toTm (.var .here)).eval eW) n)).val =
        (Q.add (((JExprN.const tmZeroJet).toTm (.var .here)).eval eW n)
          (mul (((sysY[u - sysX.length].2.shiftVars sysX.length).toTm (.var .here)).eval eW)
            (((impYrhs sysX sysY E).toTm (.var .here)).eval eW) n)).val
      rw [Q.val_add, Q.val_add, hA0, hz0, ivf_toTm_mul_eval]
  | const c =>
    dsimp only [JExprN.derivSym, impEx, impEy, JExprN.toTm]
    rw [closedWk_eval (.app tmJetDeriv c) eW, closedWk_eval tmZeroJet eW, Q.val_add]
    have hc0 : (((Tm.app tmJetDeriv c).eval Env.nil) n).val = 0 := gpac_deriv_const_val hF_cc n
    have hz0 : (tmZeroJet.eval Env.nil n).val = 0 := Q.val_ofNat 0
    have hmul0 : (mul (tmZeroJet.eval Env.nil)
        (((impYrhs sysX sysY E).toTm (.var .here)).eval eW) n).val = 0 := by
      rw [inv_jetMul_val]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have hzi : (tmZeroJet.eval Env.nil i).val = 0 := Q.val_ofNat 0
      rw [hzi, zero_mul]
    rw [hc0, hz0, hmul0, add_zero]
  | add a b iha ihb =>
    have ha := iha hF_wf.1 hF_cc.1 hF_no.1 n
    have hb := ihb hF_wf.2 hF_cc.2 hF_no.2 n
    let ay := ((impEy sysX.length sysY a).toTm (.var .here)).eval eW
    let by_ := ((impEy sysX.length sysY b).toTm (.var .here)).eval eW
    let yrhs := ((impYrhs sysX sysY E).toTm (.var .here)).eval eW
    have hmul_add : (mul (((JExprN.add (impEy sysX.length sysY a) (impEy sysX.length sysY b)).toTm (.var .here)).eval eW) yrhs n).val =
        (mul ay yrhs n).val + (mul by_ yrhs n).val := by
      rw [inv_jetMul_val, inv_jetMul_val, inv_jetMul_val, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change (Q.add (ay i) (by_ i)).val * (yrhs (n - i)).val = _
      rw [Q.val_add]
      ring
    change (Q.add (((a.derivSym (impSysXY sysX sysY E)).toTm (.var .here)).eval eW n)
        (((b.derivSym (impSysXY sysX sysY E)).toTm (.var .here)).eval eW n)).val =
      (Q.add (Q.add (((impEx sysX a).toTm (.var .here)).eval eW n)
          (((impEx sysX b).toTm (.var .here)).eval eW n))
        (mul (((JExprN.add (impEy sysX.length sysY a) (impEy sysX.length sysY b)).toTm (.var .here)).eval eW) yrhs n)).val
    rw [Q.val_add, ha, hb, Q.val_add, Q.val_add, Q.val_add, Q.val_add, hmul_add]
    ring
  | sub a b iha ihb =>
    have ha := iha hF_wf.1 hF_cc.1 hF_no.1 n
    have hb := ihb hF_wf.2 hF_cc.2 hF_no.2 n
    let ay := ((impEy sysX.length sysY a).toTm (.var .here)).eval eW
    let by_ := ((impEy sysX.length sysY b).toTm (.var .here)).eval eW
    let yrhs := ((impYrhs sysX sysY E).toTm (.var .here)).eval eW
    have hmul_sub : (mul (((JExprN.sub (impEy sysX.length sysY a) (impEy sysX.length sysY b)).toTm (.var .here)).eval eW) yrhs n).val =
        (mul ay yrhs n).val - (mul by_ yrhs n).val := by
      rw [inv_jetMul_val, inv_jetMul_val, inv_jetMul_val, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change (Q.sub (ay i) (by_ i)).val * (yrhs (n - i)).val = _
      rw [Q.val_sub]
      ring
    change (Q.sub (((a.derivSym (impSysXY sysX sysY E)).toTm (.var .here)).eval eW n)
        (((b.derivSym (impSysXY sysX sysY E)).toTm (.var .here)).eval eW n)).val =
      (Q.add (Q.sub (((impEx sysX a).toTm (.var .here)).eval eW n)
          (((impEx sysX b).toTm (.var .here)).eval eW n))
        (mul (((JExprN.sub (impEy sysX.length sysY a) (impEy sysX.length sysY b)).toTm (.var .here)).eval eW) yrhs n)).val
    rw [Q.val_sub, ha, hb, Q.val_add, Q.val_add, Q.val_add, Q.val_sub, hmul_sub]
    ring
  | mul a b iha ihb =>
    let ea := (a.toTm (.var .here)).eval eW
    let eb := (b.toTm (.var .here)).eval eW
    let da := ((a.derivSym (impSysXY sysX sysY E)).toTm (.var .here)).eval eW
    let db := ((b.derivSym (impSysXY sysX sysY E)).toTm (.var .here)).eval eW
    let ax := ((impEx sysX a).toTm (.var .here)).eval eW
    let ay := ((impEy sysX.length sysY a).toTm (.var .here)).eval eW
    let bx := ((impEx sysX b).toTm (.var .here)).eval eW
    let by_ := ((impEy sysX.length sysY b).toTm (.var .here)).eval eW
    let yrhs := ((impYrhs sysX sysY E).toTm (.var .here)).eval eW
    have hmul_eq := imp_mul_decomp_val ea eb da db ax ay bx by_ yrhs n
      (fun m _ ↦ (iha hF_wf.1 hF_cc.1 hF_no.1 m).symm)
      (fun m _ ↦ (ihb hF_wf.2 hF_cc.2 hF_no.2 m).symm)
    dsimp only [JExprN.derivSym, impEx, impEy]
    change (Q.add (((JExprN.mul (a.derivSym (impSysXY sysX sysY E)) b).toTm (.var .here)).eval eW n)
        (((JExprN.mul a (b.derivSym (impSysXY sysX sysY E))).toTm (.var .here)).eval eW n)).val =
      (Q.add (Q.add (((JExprN.mul (impEx sysX a) b).toTm (.var .here)).eval eW n)
          (((JExprN.mul a (impEx sysX b)).toTm (.var .here)).eval eW n))
        (mul (((JExprN.add (.mul (impEy sysX.length sysY a) b)
          (.mul a (impEy sysX.length sysY b))).toTm (.var .here)).eval eW) yrhs n)).val
    rw [ivf_toTm_mul_eval, ivf_toTm_mul_eval, ivf_toTm_mul_eval, ivf_toTm_mul_eval]
    have h_ey : (((JExprN.add (.mul (impEy sysX.length sysY a) b)
        (.mul a (impEy sysX.length sysY b))).toTm (.var .here)).eval eW) =
        fun k ↦ Q.add (mul ay eb k) (mul ea by_ k) := by
      funext k
      change Q.add (((JExprN.mul (impEy sysX.length sysY a) b).toTm (.var .here)).eval eW k)
          (((JExprN.mul a (impEy sysX.length sysY b)).toTm (.var .here)).eval eW k) = _
      rw [ivf_toTm_mul_eval, ivf_toTm_mul_eval]
    rw [h_ey]
    exact hmul_eq
  | integ _ _ => exact False.elim hF_no

/-- At degree `0`, any `F` (`F.WF (nX + nY)`) evaluated on `solN S` equals `impEval sysX sysY F tmZeroJet 0`. -/
theorem imp_eval_zero_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length))
    (F : JExprN) (hF_wf : F.WF (sysX.length + sysY.length)) :
    let S := impFunSys sysX sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    (((F.toTm (.var .here)).eval eS) 0).val =
      (impEval sysX sysY F (tmZeroJet.eval Env.nil) 0).val := by
  intro S eS
  have hwfX := gpac_wf hX
  have hwfY := gpac_wf hY
  have hwfS := imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf
  refine F.toTm_agreeV (sysX.length + sysY.length) hF_wf
    eS (Env.cons (σ := WTy) (impCombinedState sysX sysY (tmZeroJet.eval Env.nil)) Env.nil)
    (.var .here) (.var .here) 1 (fun v hv k hk ↦ ?_) 0 (Nat.succ_pos 0)
  have hk0 : k = 0 := by omega
  subst hk0
  have hvS : v < S.length := by rw [imp_impFunSys_length]; omega
  change (solN S v 0).val = (impCombinedState sysX sysY (tmZeroJet.eval Env.nil) v 0).val
  rw [uMul_solN_zero_val S hwfS v hvS, imp_impFunSys_getElem_xy sysX sysY E v hv]
  unfold impCombinedState
  by_cases hvX : v < sysX.length
  · rw [if_pos hvX, imp_impSysXY_getElem_lt_x sysX sysY E v hvX,
        uMul_solN_zero_val sysX hwfX v hvX]
  · rw [if_neg hvX, imp_impSysXY_getElem_ge_x sysX sysY E v hvX hv]
    have hw : v - sysX.length < sysY.length := by omega
    dsimp only
    rw [← uMul_solN_zero_val sysY hwfY (v - sysX.length) hw,
        compZero_coeff_val_eq_sum ⟨solN sysY (v - sysX.length)⟩ ⟨tmZeroJet.eval Env.nil⟩ 0 0 (le_refl 0),
        Finset.sum_range_one]
    dsimp [hPow]
    rw [Q.val_ofNat]
    ring

/-- At degree `0`, `Ey` evaluated on `solN (impFunSys sysX sysY E)` equals `impEval sysX sysY Ey tmZeroJet 0`. -/
theorem imp_ey_zero_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) :
    let S := impFunSys sysX sysY E
    let Ey := impEy sysX.length sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    (((Ey.toTm (.var .here)).eval eS) 0).val =
      (impEval sysX sysY Ey (tmZeroJet.eval Env.nil) 0).val :=
  imp_eval_zero_val sysX sysY hX hY E hE_wf (impEy sysX.length sysY E)
    (imp_impEy_wf sysX.length sysY (gpac_wf hY) E hE_wf)

/-- At degree `0`, `Ey.toTm (initN (impSysXY sysX sysY E))` has the same rational value as `Ey` on `solN S`. -/
theorem imp_ey_init_zero_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) :
    let S := impFunSys sysX sysY E
    let xy := impSysXY sysX sysY E
    let Ey := impEy sysX.length sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    (((Ey.toTm (initN xy (Γ := []))).eval Env.nil) 0).val =
      (((Ey.toTm (.var .here)).eval eS) 0).val := by
  intro S xy Ey eS
  have hwfX := gpac_wf hX
  have hwfY := gpac_wf hY
  have hwfS := imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf
  have hEy_wf : Ey.WF (sysX.length + sysY.length) := imp_impEy_wf sysX.length sysY hwfY E hE_wf
  let eInit : Env [WTy] := Env.cons (σ := WTy) ((initN xy (Γ := [])).eval Env.nil) Env.nil
  rw [Ey.toTm_eval_eq Env.nil eInit (initN xy) (.var .here) rfl]
  refine Ey.toTm_agreeV (sysX.length + sysY.length) hEy_wf
    eInit eS (.var .here) (.var .here) 1 (fun v hv k hk ↦ ?_) 0 (Nat.succ_pos 0)
  have hk0 : k = 0 := by omega
  subst hk0
  have hv_xy : v < xy.length := by rw [imp_impSysXY_length]; exact hv
  have hvS : v < S.length := by rw [imp_impFunSys_length]; omega
  change ((((initN xy (Γ := [])).eval Env.nil) v) 0).val = (solN S v 0).val
  rw [uDeriv_initN_eval_getElem xy v hv_xy,
      uMul_solN_zero_val S hwfS v hvS,
      imp_impFunSys_getElem_xy sysX sysY E v hv]

/-- At degree `0`, component `nX + nY + 1` (`u`) of `solN S` has value `1 / (Ey(solN S) 0).val`. -/
theorem imp_solN_u_zero_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length))
    (h1 : (impEval sysX sysY (impEy sysX.length sysY E) (tmZeroJet.eval Env.nil) 0).val ≠ 0) :
    let S := impFunSys sysX sysY E
    let Ey := impEy sysX.length sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    (solN S (sysX.length + sysY.length + 1) 0).val =
      1 / (((Ey.toTm (.var .here)).eval eS) 0).val := by
  intro S Ey eS
  have hwfX := gpac_wf hX
  have hwfY := gpac_wf hY
  have hwfS := imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf
  have hu : sysX.length + sysY.length + 1 < S.length := by rw [imp_impFunSys_length]; omega
  rw [uMul_solN_zero_val S hwfS (sysX.length + sysY.length + 1) hu,
      imp_impFunSys_getElem_u_var sysX sysY E]
  let xy := impSysXY sysX sysY E
  let Ah : Tm [] JetTy := Ey.toTm (initN xy)
  have hAh0 : (Ah.eval Env.nil 0).val = (((Ey.toTm (.var .here)).eval eS) 0).val :=
    imp_ey_init_zero_val sysX sysY hX hY E hE_wf
  have hEy_ne : (((Ey.toTm (.var .here)).eval eS) 0).val ≠ 0 := by
    rw [imp_ey_zero_val sysX sysY hX hY E hE_wf]
    exact h1
  have hne : (Ah.eval Env.nil 0).num ≠ 0 := by
    apply inv_num_ne_zero
    rw [hAh0]
    exact hEy_ne
  change (Q.div (Q.ofNat 1) (Ah.eval Env.nil 0)).val = _
  rw [Q.val_div _ _ hne, Q.val_ofNat, hAh0]
  rfl

/-- Derivative of component `nX + nY + 1` (`u`) of `solN S` equals `-((u · u) · (deriv G1))`. -/
theorem imp_solN_u_deriv_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length)) (j : Nat) :
    let S := impFunSys sysX sysY E
    let Ey := impEy sysX.length sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let G1 := (Ey.toTm (.var .here)).eval eS
    let u := solN S (sysX.length + sysY.length + 1)
    let mul := (tmJetMul (Γ := [])).eval Env.nil
    let deriv := (tmJetDeriv (Γ := [])).eval Env.nil
    (deriv u j).val = - (mul (mul u u) (deriv G1) j).val := by
  intro S Ey eS G1 u mul deriv
  have hwfX := gpac_wf hX
  have hwfY := gpac_wf hY
  have hwfS := imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf
  have hu : sysX.length + sysY.length + 1 < S.length := by rw [imp_impFunSys_length]; omega
  have hderiv := uMul_solN_deriv_val S hwfS (sysX.length + sysY.length + 1) hu j
  rw [imp_impFunSys_getElem_u_var sysX sysY E] at hderiv
  let xy := impSysXY sysX sysY E
  let H := Ey.derivSym xy
  let H_eval := (H.toTm (.var .here)).eval eS
  let u_var : JExprN := .var (sysX.length + sysY.length + 1)
  have hA_deriv : (deriv ((Tm.app tmInv0 (Ey.toTm (initN xy))).eval Env.nil) j).val = 0 :=
    gpac_deriv_const_val (inv_isConstJet_inv0 _) j
  have hvar : (u_var.toTm (.var .here)).eval eS = u := by
    change solN S ((natTm (sysX.length + sysY.length + 1)).eval eS) = u
    rw [natTm_eval]
  have hmul : ((((JExprN.mul (.mul u_var u_var) H).toTm (.var .here)).eval eS) j) =
      mul (mul u u) H_eval j := by
    rw [ivf_toTm_mul_eval, ivf_toTm_mul_eval, hvar]
  have hFlast : ((((JExprN.sub (.const tmZeroJet) (.mul (.mul u_var u_var) H)).toTm (.var .here)).eval eS) j).val =
      - (mul (mul u u) H_eval j).val := by
    change (Q.sub ((Tm.closedWk tmZeroJet).eval eS j)
      ((((JExprN.mul (.mul u_var u_var) H).toTm (.var .here)).eval eS) j)).val = _
    rw [closedWk_eval tmZeroJet eS, Q.val_sub, hmul]
    have hz : (tmZeroJet.eval Env.nil j).val = 0 := Q.val_ofNat 0
    rw [hz, zero_sub]
  dsimp only at hderiv
  rw [hderiv, hA_deriv, hFlast, zero_add]
  refine congrArg Neg.neg ?_
  have hEy_wf_xy : Ey.WF xy.length := by
    rw [imp_impSysXY_length]
    exact imp_impEy_wf sysX.length sysY hwfY E hE_wf
  have hH_eq : H = Ey.derivSym S :=
    (imp_derivSym_append_left xy _ Ey hEy_wf_xy).symm
  have hEy_wf_S : Ey.WF S.length := by
    rw [imp_impFunSys_length]
    exact (imp_impEy_wf sysX.length sysY hwfY E hE_wf).mono (by omega)
  exact tmJetMul_agreeV Env.nil Env.nil (j + 1) (mul u u) (mul u u) H_eval (deriv G1)
    (fun _ _ ↦ rfl)
    (fun m _ ↦ by
      dsimp [H_eval]
      rw [hH_eq]
      exact uDeriv_derivSym_val S hwfS Ey hEy_wf_S m)
    j (Nat.lt_succ_self j)

/-- In `impFunSys sysX sysY E`, the product `Ey(solN S) · u` equals the constant jet `1` in value. -/
theorem imp_mul_ey_u_eq_one_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length))
    (h1 : (impEval sysX sysY (impEy sysX.length sysY E) (tmZeroJet.eval Env.nil) 0).val ≠ 0)
    (n : Nat) :
    let S := impFunSys sysX sysY E
    let Ey := impEy sysX.length sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    let G1 := (Ey.toTm (.var .here)).eval eS
    let u := solN S (sysX.length + sysY.length + 1)
    (((tmJetMul (Γ := [])).eval Env.nil) G1 u n).val =
      ((Jet.const (Q.ofNat 1)).coeff n).val := by
  intro S Ey eS G1 u
  let mul := (tmJetMul (Γ := [])).eval Env.nil
  let deriv := (tmJetDeriv (Γ := [])).eval Env.nil
  let p := mul G1 u
  let K := mul (deriv G1) u
  let q : Nat → Rat := fun m ↦ ((Jet.const (Q.ofNat 1)).coeff m).val - (p m).val
  have hEy0_ne : (G1 0).val ≠ 0 := by
    rw [imp_ey_zero_val sysX sysY hX hY E hE_wf]
    exact h1
  have hq0 : q 0 = 0 := by
    dsimp [q, p, mul]
    rw [uMul_zero_val, imp_solN_u_zero_val sysX sysY hX hY E hE_wf h1]
    change (Q.ofNat 1).val - (G1 0).val * (1 / (G1 0).val) = 0
    rw [Q.val_ofNat]
    field_simp
    ring
  have hdu : ∀ j, (deriv u j).val = - (mul K u j).val := by
    intro j
    rw [imp_solN_u_deriv_val sysX sysY hX hY E hE_wf j]
    refine congrArg Neg.neg ?_
    rw [inv_jetMul_comm_val (mul u u) (deriv G1) j,
        ← inv_jetMul_assoc_val (deriv G1) u u j]
  have hrec : ∀ m, ((m + 1 : Nat) : Rat) * q (m + 1) =
      - ∑ i ∈ Finset.range (m + 1), (K i).val * q (m - i) := by
    intro m
    have h_G1_du : (mul G1 (deriv u) m).val = - (mul G1 (mul K u) m).val := by
      rw [inv_jetMul_val, inv_jetMul_val, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hdu (m - i)]
      ring
    have h_reassoc : (mul G1 (mul K u) m).val = (mul K p m).val := by
      rw [← inv_jetMul_assoc_val G1 K u m,
          tmJetMul_agreeV Env.nil Env.nil (m + 1) (mul G1 K) (mul K G1) u u
            (fun i _ ↦ inv_jetMul_comm_val G1 K i) (fun _ _ ↦ rfl) m (Nat.lt_succ_self m),
          inv_jetMul_assoc_val K G1 u m]
    have h_dp : ((m + 1 : Nat) : Rat) * (p (m + 1)).val = (K m).val - (mul K p m).val := by
      have hleib := jetMul_leibniz_val G1 u m
      change (Q.mul (Q.ofNat (m + 1)) (p (m + 1))).val =
        (K m).val + (mul G1 (deriv u) m).val at hleib
      rw [Q.val_mul, Q.val_ofNat, h_G1_du, h_reassoc] at hleib
      linarith
    have h_rhs : (K m).val - (mul K p m).val =
        ∑ i ∈ Finset.range (m + 1), (K i).val * q (m - i) := by
      dsimp [q]
      rw [← inv_mul_one_val K m, inv_jetMul_val K p m, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    dsimp [q]
    change ((m + 1 : Nat) : Rat) * (Q.zero.val - (p (m + 1)).val) = _
    rw [Q.val_zero, zero_sub, mul_neg, h_dp, h_rhs]
  have hqn := inv_zero_of_linear_rec (fun i ↦ (K i).val) q hq0 hrec n
  dsimp [q] at hqn
  linarith

/-- In `impFunSys sysX sysY E`, the expression `E` evaluated on `solN S` vanishes at every degree `n`. -/
theorem imp_eval_E_eq_zero_val (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length))
    (hE_cc : E.ConstsConst) (hE_no : E.NoInteg)
    (h0 : (impEval sysX sysY E (tmZeroJet.eval Env.nil) 0).val = 0)
    (h1 : (impEval sysX sysY (impEy sysX.length sysY E) (tmZeroJet.eval Env.nil) 0).val ≠ 0)
    (n : Nat) :
    let S := impFunSys sysX sysY E
    let eS : Env [WTy] := Env.cons (σ := WTy) (solN S) Env.nil
    (((E.toTm (.var .here)).eval eS) n).val = 0 := by
  intro S eS
  have hwfX := gpac_wf hX
  have hwfY := gpac_wf hY
  have hwfS := imp_impFunSys_wf sysX sysY hwfX hwfY E hE_wf
  cases n with
  | zero =>
    rw [imp_eval_zero_val sysX sysY hX hY E hE_wf E hE_wf, h0]
  | succ j =>
    let mul := (tmJetMul (Γ := [])).eval Env.nil
    let deriv := (tmJetDeriv (Γ := [])).eval Env.nil
    let xy := impSysXY sysX sysY E
    let Ex_eval := ((impEx sysX E).toTm (.var .here)).eval eS
    let Ey_eval := ((impEy sysX.length sysY E).toTm (.var .here)).eval eS
    let u := solN S (sysX.length + sysY.length + 1)
    let yrhs_eval := ((impYrhs sysX sysY E).toTm (.var .here)).eval eS
    have hE_wf_xy : E.WF xy.length := by rw [imp_impSysXY_length]; exact hE_wf
    have hE_wf_S : E.WF S.length := by rw [imp_impFunSys_length]; exact hE_wf.mono (by omega)
    have hE_sym : E.derivSym S = E.derivSym xy :=
      imp_derivSym_append_left xy _ E hE_wf_xy
    have h_deriv : (deriv ((E.toTm (.var .here)).eval eS) j).val =
        (Q.add (Ex_eval j) (mul Ey_eval yrhs_eval j)).val := by
      rw [← uDeriv_derivSym_val S hwfS E hE_wf_S j, hE_sym]
      exact imp_derivSym_decomp_val sysX sysY hX hY E E hE_wf hE_cc hE_no (solN S) j
    have hyrhs_val : ∀ m, (yrhs_eval m).val = - (mul Ex_eval u m).val := by
      intro m
      have hvar : ((JExprN.var (sysX.length + sysY.length + 1)).toTm (.var .here)).eval eS = u := by
        change solN S ((natTm (sysX.length + sysY.length + 1)).eval eS) = u
        rw [natTm_eval]
      change (Q.sub ((Tm.closedWk tmZeroJet).eval eS m)
        ((((JExprN.mul (impEx sysX E) (.var (sysX.length + sysY.length + 1))).toTm (.var .here)).eval eS) m)).val = _
      rw [closedWk_eval tmZeroJet eS, Q.val_sub, ivf_toTm_mul_eval, hvar]
      have hz : (tmZeroJet.eval Env.nil m).val = 0 := Q.val_ofNat 0
      rw [hz, zero_sub]
    have h_ey_yrhs : (mul Ey_eval yrhs_eval j).val = - (mul Ey_eval (mul Ex_eval u) j).val := by
      rw [inv_jetMul_val, inv_jetMul_val, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hyrhs_val (j - i)]
      ring
    have h_reassoc : (mul Ey_eval (mul Ex_eval u) j).val = (Ex_eval j).val := by
      rw [← inv_jetMul_assoc_val Ey_eval Ex_eval u j,
          tmJetMul_agreeV Env.nil Env.nil (j + 1) (mul Ey_eval Ex_eval) (mul Ex_eval Ey_eval) u u
            (fun i _ ↦ inv_jetMul_comm_val Ey_eval Ex_eval i) (fun _ _ ↦ rfl) j (Nat.lt_succ_self j),
          inv_jetMul_assoc_val Ex_eval Ey_eval u j]
      have h_one := tmJetMul_agreeV Env.nil Env.nil (j + 1)
        Ex_eval Ex_eval (mul Ey_eval u) (Jet.const (Q.ofNat 1)).coeff
        (fun _ _ ↦ rfl)
        (fun i _ ↦ imp_mul_ey_u_eq_one_val sysX sysY hX hY E hE_wf h1 i)
        j (Nat.lt_succ_self j)
      rw [h_one, inv_jetMul_val, inv_mul_one_val Ex_eval j]
    have h_d0 : (deriv ((E.toTm (.var .here)).eval eS) j).val = 0 := by
      rw [h_deriv, Q.val_add, h_ey_yrhs, h_reassoc, add_neg_cancel]
    change (Q.mul (Q.ofNat (j + 1)) (((E.toTm (.var .here)).eval eS) (j + 1))).val = 0 at h_d0
    rw [Q.val_mul, Q.val_ofNat] at h_d0
    have hne : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h_d0).resolve_left hne

/-- **Local implicit function theorem in the universe.**
If `sysX` and `sysY` are flat `GPACSys` systems and `E(X, Z)` is an `∫`-free
polynomial expression in their components with `E(X(0), Z(0)) = 0` and
`E_y(X(0), Z(0)) ≠ 0`, there is a universe member `y ∈ InGPAC` with `y(0) = 0`
satisfying `E(X(x), Z(y(x))) = 0` coefficientwise at every degree `n`. -/
theorem InGPAC_impFun (sysX sysY : List (Tm [] JetTy × JExprN))
    (hX : GPACSys sysX) (hY : GPACSys sysY) (hnoY : ∀ p ∈ sysY, p.2.NoInteg)
    (E : JExprN) (hE_wf : E.WF (sysX.length + sysY.length))
    (hE_cc : E.ConstsConst) (hE_no : E.NoInteg)
    (h0 : (impEval sysX sysY E (tmZeroJet.eval Env.nil) 0).val = 0)
    (h1 : (impEval sysX sysY (impEy sysX.length sysY E) (tmZeroJet.eval Env.nil) 0).val ≠ 0) :
    ∃ y : Nat → Q, InGPAC y ∧ (y 0).val = 0 ∧
      ∀ n, (impEval sysX sysY E y n).val = 0 := by
  let S := impFunSys sysX sysY E
  let y := solN S (sysX.length + sysY.length)
  have hgpacS := imp_gpac_impFunSys sysX sysY hX hY E hE_wf hE_cc
  have hy_idx : sysX.length + sysY.length < S.length := by rw [imp_impFunSys_length]; omega
  have hy_gpac : InGPAC y := ⟨S, hgpacS, sysX.length + sysY.length, hy_idx, fun _ ↦ rfl⟩
  have hy0 : (y 0).val = 0 := imp_solN_y_zero_val sysX sysY (gpac_wf hX) (gpac_wf hY) E hE_wf
  refine ⟨y, hy_gpac, hy0, fun n ↦ ?_⟩
  rw [← imp_toTm_solN_eq_impEval_val sysX sysY hX hY hnoY E hE_wf E hE_wf n]
  exact imp_eval_E_eq_zero_val sysX sysY hX hY E hE_wf hE_cc hE_no h0 h1 n

/-! ## Check: `sin(y) + x · y − x = 0`

Here `x` and `y` are coupled by `x · y` while `y` also appears inside `sin(y)`.
- `impTestSysX`: 1 variable `X_0(x) = x` (`0 + ∫ 1`).
- `impTestSysY`: 3 variables `Z_0(y) = sin(y)`, `Z_1(y) = cos(y)`, `Z_2(y) = y`.
- `impTestE`: `Z_0 + X_0 · Z_2 − X_0 = sin(y) + x · y − x`.
Expanding `sin(y) + x · y = x` gives:
`y(x) = x − x² + (7/6)x³ − (5/3)x⁴ + (329/120)x⁵ − (73/15)x⁶ + ⋯`. -/

/-- `x`-system with one variable `X_0(x) = x`. -/
def impTestSysX : List (Tm [] JetTy × JExprN) :=
  [(tmZeroJet, .const tmConstOneJet)]

/-- `y`-system with `(sin y, cos y, y)`. -/
def impTestSysY : List (Tm [] JetTy × JExprN) :=
  memSinCosSys ++ [(tmZeroJet, .const tmConstOneJet)]

/-- The implicit equation `sin(y) + x · y − x = 0` (`X_0` at `0`, `sin y` at `1`, `y` at `3`). -/
def impTestE : JExprN :=
  .sub (.add (.var 1) (.mul (.var 0) (.var 3))) (.var 0)

#guard (List.range 7).map
    (fun n ↦ Q.norm (solFast (impFunSys impTestSysX impTestSysY impTestE) 4 n))
  == [Q.zero, Q.ofNat 1, ⟨-1, 0⟩, ⟨7, 5⟩, ⟨-5, 2⟩, ⟨329, 119⟩, ⟨-73, 14⟩].map Q.norm

#print axioms impFunSys
#print axioms InGPAC_impFun

end HAomega
