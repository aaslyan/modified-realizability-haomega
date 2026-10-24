/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ChainRule

/-!
# The GPAC universe is closed under composition

`Jet.compZero F G = F(G − G(0))`. Two steps.

1. **`∫`-free normal form** (`InGPAC_noInteg`). Composing with `g` commutes with
   `+ − ×` and fixes constants (`ChainRule.lean`) but not with `∫`, so right-hand
   sides are first made `∫`-free: each subterm `∫a` becomes a new variable
   `z = 0 + ∫a`. Every member of the universe is a component of a system with
   constant data and `∫`-free right-hand sides.
2. **The composed system** (`compSys`). With `g = A_g + ∫F_g` and `f`'s system
   `∫`-free: `g`'s system, then each variable `u` of `f`'s system, renumbered,
   with equation `Y_u = A_u + ∫(g' · F_u(Y))`, `g' = D A_g + F_g`. By the chain
   rule `Y_u = f_u ∘ (g − g(0))` is a fixed point, and `genSolveN_unique_val`
   identifies it with the proof-computed solution.

Value-level metatheory theorems (`Classical.choice` through `Q.val`).
-/

namespace HAomega

/-- No `∫` in the expression. -/
def JExprN.NoInteg : JExprN → Prop
  | .var _ => True
  | .const _ => True
  | .add a b => a.NoInteg ∧ b.NoInteg
  | .sub a b => a.NoInteg ∧ b.NoInteg
  | .mul a b => a.NoInteg ∧ b.NoInteg
  | .integ _ => False

/-- Total number of `.integ` nodes in a `JExprN`. -/
def flatCount : JExprN → Nat
  | .var _ => 0
  | .const _ => 0
  | .add a b => flatCount a + flatCount b
  | .sub a b => flatCount a + flatCount b
  | .mul a b => flatCount a + flatCount b
  | .integ a => flatCount a + 1

/-- Replace the leftmost `.integ a` in `F` by `.var idx` and return `some a`, or `(F, none)` if `F` is `∫`-free. -/
def flatOne (idx : Nat) : JExprN → JExprN × Option JExprN
  | .var u => (.var u, none)
  | .const c => (.const c, none)
  | .add a b =>
      match flatOne idx a with
      | (a', some e) => (.add a' b, some e)
      | (_, none) =>
          match flatOne idx b with
          | (b', some e) => (.add a b', some e)
          | (_, none) => (.add a b, none)
  | .sub a b =>
      match flatOne idx a with
      | (a', some e) => (.sub a' b, some e)
      | (_, none) =>
          match flatOne idx b with
          | (b', some e) => (.sub a b', some e)
          | (_, none) => (.sub a b, none)
  | .mul a b =>
      match flatOne idx a with
      | (a', some e) => (.mul a' b, some e)
      | (_, none) =>
          match flatOne idx b with
          | (b', some e) => (.mul a b', some e)
          | (_, none) => (.mul a b, none)
  | .integ a => (.var idx, some a)

/-- If `flatOne idx F` returns `none`, then `F.NoInteg`. -/
theorem flat_noInteg_of_flatOne_none (idx : Nat) (F : JExprN)
    (h : (flatOne idx F).2 = none) : F.NoInteg := by
  induction F with
  | var _ => trivial
  | const _ => trivial
  | add a b iha ihb =>
    dsimp [flatOne] at h
    split at h
    · contradiction
    · rename_i ha
      split at h
      · contradiction
      · rename_i hb
        exact ⟨iha (congrArg Prod.snd ha), ihb (congrArg Prod.snd hb)⟩
  | sub a b iha ihb =>
    dsimp [flatOne] at h
    split at h
    · contradiction
    · rename_i ha
      split at h
      · contradiction
      · rename_i hb
        exact ⟨iha (congrArg Prod.snd ha), ihb (congrArg Prod.snd hb)⟩
  | mul a b iha ihb =>
    dsimp [flatOne] at h
    split at h
    · contradiction
    · rename_i ha
      split at h
      · contradiction
      · rename_i hb
        exact ⟨iha (congrArg Prod.snd ha), ihb (congrArg Prod.snd hb)⟩
  | integ _ => contradiction

/-- `tmJetInteg` evaluates identically in any environment. -/
theorem flat_tmJetInteg_eval {Γ : List Ty} (e : Env Γ) (c : Nat → Q) :
    ((tmJetInteg (Γ := Γ)).eval e) c = ((tmJetInteg (Γ := [])).eval Env.nil) c := rfl

/-- Properties of `flatOne n F = (F', some e)`: count decrease, well-formedness, constant leaves, and evaluation. -/
theorem flat_flatOne_some_props (n : Nat) (F F' e : JExprN)
    (h : flatOne n F = (F', some e)) (hF_wf : F.WF n) (hF_cc : F.ConstsConst) :
    flatCount F = flatCount F' + flatCount e + 1 ∧
    (F'.WF (n + 1) ∧ e.WF n) ∧
    (F'.ConstsConst ∧ e.ConstsConst) ∧
    ∀ (W : Nat → Nat → Q),
      W n = ((tmJetInteg (Γ := [])).eval Env.nil)
        ((e.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil)) →
      (F'.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil) =
        (F.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil) := by
  induction F generalizing F' e with
  | var _ => exact Option.noConfusion (congrArg Prod.snd h)
  | const _ => exact Option.noConfusion (congrArg Prod.snd h)
  | integ a _ =>
    have h1 : F' = .var n := (congrArg Prod.fst h).symm
    have h2 : e = a := (Option.some.inj (congrArg Prod.snd h)).symm
    subst h1; subst h2
    refine ⟨by simp [flatCount], ⟨Nat.lt_succ_self n, hF_wf⟩, ⟨trivial, hF_cc⟩, fun W hW ↦ ?_⟩
    exact (congrArg W (natTm_eval (Env.cons (σ := WTy) W Env.nil) n)).trans
      (hW.trans (flat_tmJetInteg_eval (Env.cons (σ := WTy) W Env.nil) _).symm)
  | add a b iha ihb =>
    dsimp [flatOne] at h
    split at h
    · rename_i a' e₁ ha
      obtain ⟨hc, ⟨hwf₁, hwf₂⟩, ⟨hcc₁, hcc₂⟩, heval⟩ := iha a' e₁ ha hF_wf.1 hF_cc.1
      have h1 : F' = .add a' b := (congrArg Prod.fst h).symm
      have h2 : e = e₁ := (Option.some.inj (congrArg Prod.snd h)).symm
      subst h1; subst h2
      refine ⟨by dsimp [flatCount]; omega,
        ⟨⟨hwf₁, hF_wf.2.mono (Nat.le_succ n)⟩, hwf₂⟩,
        ⟨⟨hcc₁, hF_cc.2⟩, hcc₂⟩, fun W hW ↦ ?_⟩
      exact congrFun (congrArg ((tmJetAdd (Γ := [WTy])).eval (Env.cons (σ := WTy) W Env.nil))
        (heval W hW)) ((b.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil))
    · split at h
      · rename_i b' e₂ hb
        obtain ⟨hc, ⟨hwf₁, hwf₂⟩, ⟨hcc₁, hcc₂⟩, heval⟩ := ihb b' e₂ hb hF_wf.2 hF_cc.2
        have h1 : F' = .add a b' := (congrArg Prod.fst h).symm
        have h2 : e = e₂ := (Option.some.inj (congrArg Prod.snd h)).symm
        subst h1; subst h2
        refine ⟨by dsimp [flatCount]; omega,
          ⟨⟨hF_wf.1.mono (Nat.le_succ n), hwf₁⟩, hwf₂⟩,
          ⟨⟨hF_cc.1, hcc₁⟩, hcc₂⟩, fun W hW ↦ ?_⟩
        exact congrArg (((tmJetAdd (Γ := [WTy])).eval (Env.cons (σ := WTy) W Env.nil))
          ((a.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil))) (heval W hW)
      · exact Option.noConfusion (congrArg Prod.snd h)
  | sub a b iha ihb =>
    dsimp [flatOne] at h
    split at h
    · rename_i a' e₁ ha
      obtain ⟨hc, ⟨hwf₁, hwf₂⟩, ⟨hcc₁, hcc₂⟩, heval⟩ := iha a' e₁ ha hF_wf.1 hF_cc.1
      have h1 : F' = .sub a' b := (congrArg Prod.fst h).symm
      have h2 : e = e₁ := (Option.some.inj (congrArg Prod.snd h)).symm
      subst h1; subst h2
      refine ⟨by dsimp [flatCount]; omega,
        ⟨⟨hwf₁, hF_wf.2.mono (Nat.le_succ n)⟩, hwf₂⟩,
        ⟨⟨hcc₁, hF_cc.2⟩, hcc₂⟩, fun W hW ↦ ?_⟩
      exact congrFun (congrArg ((tmJetSub (Γ := [WTy])).eval (Env.cons (σ := WTy) W Env.nil))
        (heval W hW)) ((b.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil))
    · split at h
      · rename_i b' e₂ hb
        obtain ⟨hc, ⟨hwf₁, hwf₂⟩, ⟨hcc₁, hcc₂⟩, heval⟩ := ihb b' e₂ hb hF_wf.2 hF_cc.2
        have h1 : F' = .sub a b' := (congrArg Prod.fst h).symm
        have h2 : e = e₂ := (Option.some.inj (congrArg Prod.snd h)).symm
        subst h1; subst h2
        refine ⟨by dsimp [flatCount]; omega,
          ⟨⟨hF_wf.1.mono (Nat.le_succ n), hwf₁⟩, hwf₂⟩,
          ⟨⟨hF_cc.1, hcc₁⟩, hcc₂⟩, fun W hW ↦ ?_⟩
        exact congrArg (((tmJetSub (Γ := [WTy])).eval (Env.cons (σ := WTy) W Env.nil))
          ((a.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil))) (heval W hW)
      · exact Option.noConfusion (congrArg Prod.snd h)
  | mul a b iha ihb =>
    dsimp [flatOne] at h
    split at h
    · rename_i a' e₁ ha
      obtain ⟨hc, ⟨hwf₁, hwf₂⟩, ⟨hcc₁, hcc₂⟩, heval⟩ := iha a' e₁ ha hF_wf.1 hF_cc.1
      have h1 : F' = .mul a' b := (congrArg Prod.fst h).symm
      have h2 : e = e₁ := (Option.some.inj (congrArg Prod.snd h)).symm
      subst h1; subst h2
      refine ⟨by dsimp [flatCount]; omega,
        ⟨⟨hwf₁, hF_wf.2.mono (Nat.le_succ n)⟩, hwf₂⟩,
        ⟨⟨hcc₁, hF_cc.2⟩, hcc₂⟩, fun W hW ↦ ?_⟩
      exact congrFun (congrArg ((tmJetMul (Γ := [WTy])).eval (Env.cons (σ := WTy) W Env.nil))
        (heval W hW)) ((b.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil))
    · split at h
      · rename_i b' e₂ hb
        obtain ⟨hc, ⟨hwf₁, hwf₂⟩, ⟨hcc₁, hcc₂⟩, heval⟩ := ihb b' e₂ hb hF_wf.2 hF_cc.2
        have h1 : F' = .mul a b' := (congrArg Prod.fst h).symm
        have h2 : e = e₂ := (Option.some.inj (congrArg Prod.snd h)).symm
        subst h1; subst h2
        refine ⟨by dsimp [flatCount]; omega,
          ⟨⟨hF_wf.1.mono (Nat.le_succ n), hwf₁⟩, hwf₂⟩,
          ⟨⟨hF_cc.1, hcc₁⟩, hcc₂⟩, fun W hW ↦ ?_⟩
        exact congrArg (((tmJetMul (Γ := [WTy])).eval (Env.cons (σ := WTy) W Env.nil))
          ((a.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil))) (heval W hW)
      · exact Option.noConfusion (congrArg Prod.snd h)

/-- Replace the first `.integ` in a list of equations by `.var idx`, returning the updated list and the extracted integrand. -/
def flatSysOne (idx : Nat) :
    List (Tm [] JetTy × JExprN) → List (Tm [] JetTy × JExprN) × Option JExprN
  | [] => ([], none)
  | (A, F) :: rest =>
      match flatOne idx F with
      | (F', some e) => ((A, F') :: rest, some e)
      | (_, none) =>
          match flatSysOne idx rest with
          | (rest', some e) => ((A, F) :: rest', some e)
          | (_, none) => ((A, F) :: rest, none)

/-- If `flatSysOne idx tail` returns `none`, every equation in `tail` is `∫`-free. -/
theorem flat_noInteg_of_flatSysOne_none (idx : Nat) (tail : List (Tm [] JetTy × JExprN))
    (h : (flatSysOne idx tail).2 = none) : ∀ p ∈ tail, p.2.NoInteg := by
  induction tail with
  | nil => intro _ hp; contradiction
  | cons hd rest ih =>
    rcases hd with ⟨A, F⟩
    dsimp [flatSysOne] at h
    split at h
    · contradiction
    · rename_i hF
      split at h
      · contradiction
      · rename_i hrest
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact flat_noInteg_of_flatOne_none idx F (congrArg Prod.snd hF)
        · exact ih (congrArg Prod.snd hrest) p hp

/-- Properties of `flatSysOne n tail = (tail', some e)`. -/
theorem flat_flatSysOne_some_props (n : Nat) (tail tail' : List (Tm [] JetTy × JExprN)) (e : JExprN)
    (h : flatSysOne n tail = (tail', some e))
    (htail : ∀ p ∈ tail, p.2.WF n ∧ IsConstJet p.1 ∧ p.2.ConstsConst) :
    tail'.length = tail.length ∧
    (tail'.map (fun p ↦ flatCount p.2)).sum + flatCount e + 1 =
      (tail.map (fun p ↦ flatCount p.2)).sum ∧
    ((∀ p ∈ tail', p.2.WF (n + 1) ∧ IsConstJet p.1 ∧ p.2.ConstsConst) ∧ e.WF n ∧ e.ConstsConst) ∧
    ∀ (W : Nat → Nat → Q),
      W n = ((tmJetInteg (Γ := [])).eval Env.nil)
        ((e.toTm (.var .here)).eval (Env.cons (σ := WTy) W Env.nil)) →
      ∀ (w : Nat) (hw : w < tail.length) (hw' : w < tail'.length),
        eqStepEval tail'[w] W = eqStepEval tail[w] W := by
  induction tail generalizing tail' e with
  | nil => exact Option.noConfusion (congrArg Prod.snd h)
  | cons hd rest ih =>
    rcases hd with ⟨A, F⟩
    have hhd := htail (A, F) List.mem_cons_self
    have hrest_all : ∀ p ∈ rest, p.2.WF n ∧ IsConstJet p.1 ∧ p.2.ConstsConst :=
      fun p hp ↦ htail p (List.mem_cons_of_mem _ hp)
    dsimp [flatSysOne] at h
    split at h
    · rename_i F' e₁ hF
      obtain ⟨hc, ⟨hwf₁, hwf₂⟩, ⟨hcc₁, hcc₂⟩, heval⟩ :=
        flat_flatOne_some_props n F F' e₁ hF hhd.1 hhd.2.2
      have h1 : tail' = (A, F') :: rest := (congrArg Prod.fst h).symm
      have h2 : e = e₁ := (Option.some.inj (congrArg Prod.snd h)).symm
      subst h1; subst h2
      refine ⟨rfl, by simp only [List.map_cons, List.sum_cons]; omega,
        ⟨?_, hwf₂, hcc₂⟩, fun W hW w hw hw' ↦ ?_⟩
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hwf₁, hhd.2.1, hcc₁⟩
        · have hp_rest := hrest_all p hp
          exact ⟨hp_rest.1.mono (Nat.le_succ n), hp_rest.2⟩
      · cases w with
        | zero =>
          dsimp only [List.getElem_cons_zero]
          exact congrArg (((tmJetAdd (Γ := [])).eval Env.nil) (A.eval Env.nil))
            (congrArg ((tmJetInteg (Γ := [])).eval Env.nil) (heval W hW))
        | succ u =>
          dsimp only [List.getElem_cons_succ]
    · split at h
      · rename_i rest' e₂ hrest
        obtain ⟨hlen, hsum, ⟨hrest'_gpac, he_wf, he_cc⟩, heval⟩ :=
          ih rest' e₂ hrest hrest_all
        have h1 : tail' = (A, F) :: rest' := (congrArg Prod.fst h).symm
        have h2 : e = e₂ := (Option.some.inj (congrArg Prod.snd h)).symm
        subst h1; subst h2
        refine ⟨congrArg Nat.succ hlen,
          by simp only [List.map_cons, List.sum_cons]; omega,
          ⟨?_, he_wf, he_cc⟩, fun W hW w hw hw' ↦ ?_⟩
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨hhd.1.mono (Nat.le_succ n), hhd.2⟩
          · exact hrest'_gpac p hp
        · cases w with
          | zero =>
            dsimp only [List.getElem_cons_zero]
          | succ u =>
            dsimp only [List.getElem_cons_succ]
            exact heval W hW u (Nat.lt_of_succ_lt_succ hw) (Nat.lt_of_succ_lt_succ hw')
      · exact Option.noConfusion (congrArg Prod.snd h)

/-- One flattening step on a system `sys` preserves `GPACSys`, decreases the total `flatCount` by `1`, and preserves `solN` values on `< sys.length`. -/
theorem flat_step_solN_val (sys sys' : List (Tm [] JetTy × JExprN)) (e : JExprN)
    (hgpac : GPACSys sys) (h : flatSysOne sys.length sys = (sys', some e)) :
    let S := sys' ++ [(tmZeroJet, e)]
    S.length = sys.length + 1 ∧
    GPACSys S ∧
    (S.map (fun p ↦ flatCount p.2)).sum + 1 = (sys.map (fun p ↦ flatCount p.2)).sum ∧
    ∀ v < sys.length, ∀ n, (solN sys v n).val = (solN S v n).val := by
  intro S
  have hwf : ∀ p ∈ sys, p.2.WF sys.length := gpac_wf hgpac
  obtain ⟨hlen, hsum, ⟨hsys'_gpac, he_wf, he_cc⟩, heval⟩ :=
    flat_flatSysOne_some_props sys.length sys sys' e h hgpac
  have hS_len : S.length = sys.length + 1 := by
    simp [S, hlen]
  have hS_gpac : GPACSys S := by
    intro p hp
    rw [hS_len]
    simp only [S, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp₁ | rfl
    · exact hsys'_gpac p hp₁
    · exact ⟨he_wf.mono (Nat.le_succ _), gpac_isConstJet_zero, he_cc⟩
  have hS_sum : (S.map (fun p ↦ flatCount p.2)).sum + 1 = (sys.map (fun p ↦ flatCount p.2)).sum := by
    simp only [S, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    omega
  refine ⟨hS_len, hS_gpac, hS_sum, fun v hv n ↦ ?_⟩
  let Z : Nat → Nat → Q := fun w m ↦
    if w < sys.length then solN sys w m
    else (((tmJetInteg (Γ := [])).eval Env.nil)
      ((e.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil))) m
  have hZ_below : ∀ u < sys.length, Z u = solN sys u := by
    intro u hu; funext m; exact if_pos hu
  have he_eval : (e.toTm (.var .here)).eval (Env.cons (σ := WTy) Z Env.nil) =
      (e.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sys) Env.nil) :=
    e.toTm_eval_of_eq_below sys.length he_wf
      (Env.cons (σ := WTy) Z Env.nil) (Env.cons (σ := WTy) (solN sys) Env.nil)
      (.var .here) (.var .here) hZ_below
  have hZ_last : Z sys.length = ((tmJetInteg (Γ := [])).eval Env.nil)
      ((e.toTm (.var .here)).eval (Env.cons (σ := WTy) Z Env.nil)) := by
    rw [he_eval]
    funext m
    exact if_neg (Nat.lt_irrefl _)
  have hZ_fixed : ∀ w < S.length, ∀ m,
      ((((genStepN S (Γ := [])).eval Env.nil) Z) w m).val = (Z w m).val := by
    intro w hw m
    rw [genStepN_eval_getElem S Z w hw]
    by_cases hw₁ : w < sys.length
    · have hw' : w < sys'.length := by omega
      have hget : S[w] = sys'[w] := List.getElem_append_left hw'
      rw [hget, heval Z hZ_last w hw₁ hw',
          eqStepEval_of_eq_below sys[w] sys.length (hwf sys[w] (List.getElem_mem hw₁)) Z (solN sys) hZ_below,
          ← genStepN_eval_getElem sys (solN sys) w hw₁]
      dsimp [Z]
      rw [if_pos hw₁]
      exact solN_fixed sys hwf w hw₁ m
    · have hw_eq : w = sys.length := by omega
      have hget : S[w] = (tmZeroJet, e) := by
        simp only [S]
        rw [List.getElem_append_right (by omega)]
        simp [hw_eq, hlen]
      rw [hget]
      unfold eqStepEval
      rw [← hZ_last]
      change (Q.add (Q.ofNat 0) (Z sys.length m)).val = (Z w m).val
      rw [Q.val_add, Q.val_ofNat, hw_eq]
      ring
  have huniq := genSolveN_unique_val S (gpac_wf hS_gpac) Z hZ_fixed
    (n + 1) v n (by omega) (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change (solN sys v n).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil)) v n).val
  rw [huniq]
  dsimp [Z]
  rw [if_pos hv]

/-- By induction on the total `flatCount`, every `GPACSys` can be flattened to an `∫`-free `GPACSys` preserving `solN` on existing variables. -/
theorem flat_ind_noInteg (k : Nat) :
    ∀ (sys : List (Tm [] JetTy × JExprN)),
      GPACSys sys →
      (sys.map (fun p ↦ flatCount p.2)).sum ≤ k →
      ∀ v < sys.length,
        ∃ (sysF : List (Tm [] JetTy × JExprN)) (_ : GPACSys sysF) (_ : ∀ p ∈ sysF, p.2.NoInteg)
          (v' : Nat), v' < sysF.length ∧ ∀ n, (solN sys v n).val = (solN sysF v' n).val := by
  induction k with
  | zero =>
    intro sys hgpac hsum v hv
    cases h : flatSysOne sys.length sys with
    | mk sys' opt =>
      cases opt with
      | none =>
        exact ⟨sys, hgpac, flat_noInteg_of_flatSysOne_none sys.length sys (congrArg Prod.snd h),
          v, hv, fun _ ↦ rfl⟩
      | some e =>
        have hstep := flat_step_solN_val sys sys' e hgpac h
        omega
  | succ k ih =>
    intro sys hgpac hsum v hv
    cases h : flatSysOne sys.length sys with
    | mk sys' opt =>
      cases opt with
      | none =>
        exact ⟨sys, hgpac, flat_noInteg_of_flatSysOne_none sys.length sys (congrArg Prod.snd h),
          v, hv, fun _ ↦ rfl⟩
      | some e =>
        obtain ⟨hS_len, hS_gpac, hS_sum, hS_val⟩ := flat_step_solN_val sys sys' e hgpac h
        obtain ⟨sysF, hgpacF, hnoF, v', hv', hv'_val⟩ :=
          ih (sys' ++ [(tmZeroJet, e)]) hS_gpac (by omega) v (by omega)
        exact ⟨sysF, hgpacF, hnoF, v', hv', fun n ↦ (hS_val v hv n).trans (hv'_val n)⟩

/-- **`∫`-free normal form.** -/
theorem InGPAC_noInteg (f : Nat → Q) (hf : InGPAC f) :
    ∃ (sys : List (Tm [] JetTy × JExprN)) (_ : GPACSys sys) (_ : ∀ p ∈ sys, p.2.NoInteg)
      (v : Nat), v < sys.length ∧ ∀ n, (f n).val = (solN sys v n).val := by
  rcases hf with ⟨sys₀, hgpac₀, v₀, hv₀, hf_val⟩
  obtain ⟨sys, hgpac, hno, v, hv, hsol⟩ :=
    flat_ind_noInteg (sys₀.map (fun p ↦ flatCount p.2)).sum sys₀ hgpac₀ (le_refl _) v₀ hv₀
  exact ⟨sys, hgpac, hno, v, hv, fun n ↦ (hf_val n).trans (hsol n)⟩

/-- The composed system: `sysG`, then `sysF` renumbered after it with
    `Y_u = A_u + ∫(g' · F_u(Y))`, `g' = D A_g + F_g`. -/
def compSys (sysF sysG : List (Tm [] JetTy × JExprN)) (w : Nat) (hw : w < sysG.length) :
    List (Tm [] JetTy × JExprN) :=
  let Dg : JExprN := .add (.const (.app tmJetDeriv sysG[w].1)) sysG[w].2
  sysG ++ sysF.map (fun p ↦ (p.1, .mul Dg (p.2.shiftVars sysG.length)))

/-- `hPow G r` respects value equality in `G`. -/
theorem comp_hPow_congr_val (G G' : Jet) (hG : ∀ m, (G.coeff m).val = (G'.coeff m).val) :
    ∀ (r n : Nat), ((hPow G r).coeff n).val = ((hPow G' r).coeff n).val
  | 0, _ => rfl
  | r + 1, 0 => rfl
  | r + 1, k + 1 => by
    dsimp [hPow, mulShift]
    rw [TrigPoly.cauchyConvAux_val, TrigPoly.cauchyConvAux_val]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp [Jet.shift]
    rw [hG (j + 1), comp_hPow_congr_val G G' hG r (k - j)]

/-- Composition respects value equality in its second argument. -/
theorem comp_compZero_congr_right_val (F G G' : Jet)
    (hG : ∀ m, (G.coeff m).val = (G'.coeff m).val) (n : Nat) :
    ((Jet.compZero F G).coeff n).val = ((Jet.compZero F G').coeff n).val := by
  rw [compZero_coeff_val_eq_sum F G n n (le_refl _),
      compZero_coeff_val_eq_sum F G' n n (le_refl _)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [comp_hPow_congr_val G G' hG r n]

/-- Length of `compSys sysF sysG w hw`. -/
theorem comp_compSys_length (sysF sysG : List (Tm [] JetTy × JExprN)) (w : Nat) (hw : w < sysG.length) :
    (compSys sysF sysG w hw).length = sysG.length + sysF.length := by
  simp [compSys]

/-- Well-formedness of `compSys sysF sysG w hw`. -/
theorem comp_compSys_wf (sysF sysG : List (Tm [] JetTy × JExprN))
    (hwfF : ∀ p ∈ sysF, p.2.WF sysF.length) (hwfG : ∀ p ∈ sysG, p.2.WF sysG.length)
    (w : Nat) (hw : w < sysG.length) :
    ∀ p ∈ compSys sysF sysG w hw, p.2.WF (compSys sysF sysG w hw).length := by
  rw [comp_compSys_length]
  intro p hp
  simp only [compSys, List.mem_append, List.mem_map] at hp
  rcases hp with hpG | ⟨q, hq, rfl⟩
  · exact (hwfG p hpG).mono (by omega)
  · refine ⟨⟨trivial, (hwfG sysG[w] (List.getElem_mem hw)).mono (by omega)⟩, ?_⟩
    exact q.2.shiftVars_wf sysG.length sysF.length (hwfF q hq)

/-- `compSys` preserves `GPACSys`. -/
theorem comp_gpac_compSys (sysF sysG : List (Tm [] JetTy × JExprN))
    (hF : GPACSys sysF) (hG : GPACSys sysG) (w : Nat) (hw : w < sysG.length) :
    GPACSys (compSys sysF sysG w hw) := by
  intro p hp
  refine ⟨comp_compSys_wf sysF sysG (gpac_wf hF) (gpac_wf hG) w hw p hp, ?_⟩
  simp only [compSys, List.mem_append, List.mem_map] at hp
  rcases hp with hpG | ⟨q, hq, rfl⟩
  · exact (hG p hpG).2
  · have hgw := hG sysG[w] (List.getElem_mem hw)
    have hqf := hF q hq
    exact ⟨hqf.2.1, ⟨gpac_isConstJet_deriv hgw.2.1, hgw.2.2⟩,
      gpac_shiftVars_constsConst q.2 sysG.length hqf.2.2⟩

/-- Target solution state for `compSys`: `solN sysG` on `[0, sysG.length)` and `Jet.compZero ⟨solN sysF u⟩ ⟨solN sysG w⟩` at `sysG.length + u`. -/
def compTargetState (sysF sysG : List (Tm [] JetTy × JExprN)) (w : Nat) : Nat → Nat → Q :=
  fun u n ↦
    if u < sysG.length then solN sysG u n
    else (Jet.compZero ⟨solN sysF (u - sysG.length)⟩ ⟨solN sysG w⟩).coeff n

/-- Evaluating an `∫`-free `F` with constant leaves on composed jets equals composing `F` evaluated on `solN sysF` with `solN sysG w`. -/
theorem comp_toTm_compZero_val (sysF : List (Tm [] JetTy × JExprN)) (G : Jet)
    (F : JExprN) (hcc : F.ConstsConst) (hno : F.NoInteg) (n : Nat) :
    let W_comp : Nat → Nat → Q := fun u ↦ (Jet.compZero ⟨solN sysF u⟩ G).coeff
    (((F.toTm (.var .here)).eval (Env.cons (σ := WTy) W_comp Env.nil)) n).val =
      ((Jet.compZero ⟨(F.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sysF) Env.nil)⟩ G).coeff n).val := by
  intro W_comp
  let eC : Env [WTy] := Env.cons (σ := WTy) W_comp Env.nil
  let eF : Env [WTy] := Env.cons (σ := WTy) (solN sysF) Env.nil
  induction F generalizing n with
  | var u =>
    change ((Jet.compZero ⟨solN sysF ((natTm u).eval eC)⟩ G).coeff n).val =
      ((Jet.compZero ⟨solN sysF ((natTm u).eval eF)⟩ G).coeff n).val
    rw [natTm_eval, natTm_eval]
  | const c =>
    dsimp only [JExprN.toTm]
    rw [closedWk_eval c eC, closedWk_eval c eF]
    exact (compZero_const_val ⟨c.eval Env.nil⟩ G hcc n).symm
  | add a b iha ihb =>
    let Ja : Jet := ⟨(a.toTm (.var .here)).eval eF⟩
    let Jb : Jet := ⟨(b.toTm (.var .here)).eval eF⟩
    change (Q.add (((a.toTm (.var .here)).eval eC) n) (((b.toTm (.var .here)).eval eC) n)).val =
      ((Jet.compZero (Ja.add Jb) G).coeff n).val
    rw [Q.val_add, iha hcc.1 hno.1 n, ihb hcc.2 hno.2 n, compZero_add_val Ja Jb G n]
    dsimp [Jet.add]
    rw [Q.val_add]
  | sub a b iha ihb =>
    let Ja : Jet := ⟨(a.toTm (.var .here)).eval eF⟩
    let Jb : Jet := ⟨(b.toTm (.var .here)).eval eF⟩
    change (Q.sub (((a.toTm (.var .here)).eval eC) n) (((b.toTm (.var .here)).eval eC) n)).val =
      ((Jet.compZero (Ja.sub Jb) G).coeff n).val
    rw [Q.val_sub, iha hcc.1 hno.1 n, ihb hcc.2 hno.2 n, compZero_sub_val Ja Jb G n]
    dsimp [Jet.sub]
    rw [Q.val_sub]
  | mul a b iha ihb =>
    let Ja : Jet := ⟨(a.toTm (.var .here)).eval eF⟩
    let Jb : Jet := ⟨(b.toTm (.var .here)).eval eF⟩
    have hm : ((((JExprN.mul a b).toTm (.var .here)).eval eC) n).val =
        (((tmJetMul (Γ := [])).eval Env.nil)
          (Jet.compZero Ja G).coeff (Jet.compZero Jb G).coeff n).val :=
      tmJetMul_agreeV Env.nil Env.nil (n + 1)
        ((a.toTm (.var .here)).eval eC) (Jet.compZero Ja G).coeff
        ((b.toTm (.var .here)).eval eC) (Jet.compZero Jb G).coeff
        (fun i _ ↦ iha hcc.1 hno.1 i) (fun i _ ↦ ihb hcc.2 hno.2 i) n (Nat.lt_succ_self n)
    rw [hm, tmJetMul_eval]
    have hmul_eq : (⟨((JExprN.mul a b).toTm (.var .here)).eval eF⟩ : Jet) = Ja.mul Jb := by
      congr 1
      funext m
      exact tmJetMul_eval eF ((a.toTm (.var .here)).eval eF) ((b.toTm (.var .here)).eval eF) m
    rw [hmul_eq, compZero_mul_val Ja Jb G n]
  | integ _ _ => exact False.elim hno

/-- Evaluating the composed equation at `sysG.length + u` on `compTargetState` yields `Jet.compZero ⟨solN sysF u⟩ ⟨solN sysG w⟩`. -/
theorem comp_eqStepEval_shifted_val (sysF sysG : List (Tm [] JetTy × JExprN))
    (hF : GPACSys sysF) (hnoF : ∀ p ∈ sysF, p.2.NoInteg)
    (hwfG : ∀ p ∈ sysG, p.2.WF sysG.length)
    (w : Nat) (hw : w < sysG.length) (u : Nat) (hu : u < sysF.length) (n : Nat) :
    let Dg : JExprN := .add (.const (.app tmJetDeriv sysG[w].1)) sysG[w].2
    let p := sysF[u]
    (eqStepEval (p.1, .mul Dg (p.2.shiftVars sysG.length)) (compTargetState sysF sysG w) n).val =
      ((Jet.compZero ⟨solN sysF u⟩ ⟨solN sysG w⟩).coeff n).val := by
  intro Dg p
  let Z := compTargetState sysF sysG w
  let eZ : Env [WTy] := Env.cons (σ := WTy) Z Env.nil
  let G : Jet := ⟨solN sysG w⟩
  let Fu : Jet := ⟨solN sysF u⟩
  have hwfF : ∀ q ∈ sysF, q.2.WF sysF.length := gpac_wf hF
  have hp_mem : p ∈ sysF := List.getElem_mem hu
  have hp_gpac := hF p hp_mem
  have hp_no := hnoF p hp_mem
  have hZG : ∀ i < sysG.length, Z i = solN sysG i := by
    intro i hi; funext m; exact if_pos hi
  have hZF : ∀ i < sysF.length, Z (sysG.length + i) = (Jet.compZero ⟨solN sysF i⟩ G).coeff := by
    intro i _
    funext m
    unfold Z compTargetState
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
  cases n with
  | zero =>
    unfold eqStepEval
    change (Q.add (p.1.eval Env.nil 0) (Q.ofNat 0)).val = ((Jet.compZero Fu G).coeff 0).val
    have h0 : (Q.add (p.1.eval Env.nil 0) (Q.ofNat 0)).val = (p.1.eval Env.nil 0).val := by
      rw [Q.val_add, Q.val_ofNat]; ring
    rw [h0, ← uMul_solN_zero_val sysF hwfF u hu,
        compZero_coeff_val_eq_sum Fu G 0 0 (le_refl 0),
        Finset.sum_range_one]
    dsimp [Fu, hPow]
    rw [Q.val_ofNat]
    ring
  | succ j =>
    have hDg : ∀ m < j + 1, (((Dg.toTm (.var .here)).eval eZ) m).val = (G.deriv.coeff m).val := by
      intro m _
      have hFg := sysG[w].2.toTm_eval_of_eq_below sysG.length
        (hwfG sysG[w] (List.getElem_mem hw)) eZ (Env.cons (σ := WTy) (solN sysG) Env.nil)
        (.var .here) (.var .here) hZG
      change (Q.add ((Tm.closedWk (.app tmJetDeriv sysG[w].1)).eval eZ m)
        (((sysG[w].2.toTm (.var .here)).eval eZ) m)).val = (G.deriv.coeff m).val
      rw [closedWk_eval (.app tmJetDeriv sysG[w].1) eZ, hFg, Q.val_add]
      exact (uMul_solN_deriv_val sysG hwfG w hw m).symm
    have hF_shift : ∀ m < j + 1,
        ((((p.2.shiftVars sysG.length).toTm (.var .here)).eval eZ) m).val =
          ((Jet.compZero Fu.deriv G).coeff m).val := by
      intro m _
      let W_comp : Nat → Nat → Q := fun i ↦ (Jet.compZero ⟨solN sysF i⟩ G).coeff
      have hsh := p.2.shiftVars_toTm_eval sysG.length sysF.length hp_gpac.1
        eZ (Env.cons (σ := WTy) W_comp Env.nil) (.var .here) (.var .here) hZF
      rw [hsh, comp_toTm_compZero_val sysF G p.2 hp_gpac.2.2 hp_no m]
      refine compZero_congr_val ⟨(p.2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sysF) Env.nil)⟩
        Fu.deriv G (fun k ↦ ?_) m
      have hderiv_u := uMul_solN_deriv_val sysF hwfF u hu k
      have hA_zero := gpac_deriv_const_val hp_gpac.2.1 k
      dsimp [p] at hA_zero ⊢
      change (((p.2.toTm (.var .here)).eval (Env.cons (σ := WTy) (solN sysF) Env.nil)) k).val =
        (((tmJetDeriv (Γ := [])).eval Env.nil) (solN sysF u) k).val
      linarith
    have hmul :
        ((((JExprN.mul Dg (p.2.shiftVars sysG.length)).toTm (.var .here)).eval eZ) j).val =
          (((Jet.compZero Fu G).deriv).coeff j).val := by
      have hm := tmJetMul_agreeV Env.nil Env.nil (j + 1)
        ((Dg.toTm (.var .here)).eval eZ) G.deriv.coeff
        (((p.2.shiftVars sysG.length).toTm (.var .here)).eval eZ) (Jet.compZero Fu.deriv G).coeff
        hDg hF_shift j (Nat.lt_succ_self j)
      exact hm.trans (by rw [tmJetMul_eval, ← compZero_deriv_val Fu G j])
    have hne : (Q.ofNat (j + 1)).num ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    have hne_rat : ((j + 1 : Nat) : Rat) ≠ 0 := by positivity
    unfold eqStepEval
    change (Q.add (p.1.eval Env.nil (j + 1))
      (Q.div ((((JExprN.mul Dg (p.2.shiftVars sysG.length)).toTm (.var .here)).eval eZ) j)
        (Q.ofNat (j + 1)))).val = ((Jet.compZero Fu G).coeff (j + 1)).val
    rw [Q.val_add, hp_gpac.2.1 j, zero_add, Q.val_div _ _ hne, Q.val_ofNat, hmul]
    dsimp [Jet.deriv]
    rw [Q.val_mul, Q.val_ofNat]
    field_simp

/-- `compTargetState` is a value-level fixed point of `genStepN (compSys sysF sysG w hw)`. -/
theorem compTargetState_fixed (sysF sysG : List (Tm [] JetTy × JExprN))
    (hF : GPACSys sysF) (hnoF : ∀ p ∈ sysF, p.2.NoInteg)
    (hwfG : ∀ p ∈ sysG, p.2.WF sysG.length)
    (w : Nat) (hw : w < sysG.length) :
    ∀ u < (compSys sysF sysG w hw).length, ∀ n,
      ((((genStepN (compSys sysF sysG w hw) (Γ := [])).eval Env.nil)
        (compTargetState sysF sysG w)) u n).val =
        (compTargetState sysF sysG w u n).val := by
  intro u hu n
  rw [genStepN_eval_getElem _ _ u hu]
  have hu_len : u < sysG.length + sysF.length := by rwa [comp_compSys_length] at hu
  have hZG : ∀ i < sysG.length, compTargetState sysF sysG w i = solN sysG i := by
    intro i hi; funext m; exact if_pos hi
  by_cases hu₁ : u < sysG.length
  · have hget : (compSys sysF sysG w hw)[u] = sysG[u] := by
      simp only [compSys]
      exact List.getElem_append_left hu₁
    rw [hget, eqStepEval_of_eq_below sysG[u] sysG.length (hwfG sysG[u] (List.getElem_mem hu₁)) _ _ hZG,
        ← genStepN_eval_getElem sysG (solN sysG) u hu₁]
    unfold compTargetState
    rw [if_pos hu₁]
    exact solN_fixed sysG hwfG u hu₁ n
  · have hidx : u - sysG.length < sysF.length := by omega
    have hget : (compSys sysF sysG w hw)[u] =
        (sysF[u - sysG.length].1,
         .mul (.add (.const (.app tmJetDeriv sysG[w].1)) sysG[w].2)
           (sysF[u - sysG.length].2.shiftVars sysG.length)) := by
      simp only [compSys]
      rw [List.getElem_append_right (Nat.not_lt.mp hu₁), List.getElem_map]
    rw [hget, comp_eqStepEval_shifted_val sysF sysG hF hnoF hwfG w hw (u - sysG.length) hidx n]
    unfold compTargetState
    rw [if_neg hu₁]

/-- **Closure under composition.** -/
theorem InGPAC_comp (f g : Nat → Q) (hf : InGPAC f) (hg : InGPAC g) :
    InGPAC (Jet.compZero ⟨f⟩ ⟨g⟩).coeff := by
  obtain ⟨sysF, hgpacF, hnoF, v, hv, hf_val⟩ := InGPAC_noInteg f hf
  rcases hg with ⟨sysG, hgpacG, w, hw, hg_val⟩
  let S := compSys sysF sysG w hw
  have hgpacS := comp_gpac_compSys sysF sysG hgpacF hgpacG w hw
  have hwfS := gpac_wf hgpacS
  have hvS : sysG.length + v < S.length := by
    rw [comp_compSys_length]
    omega
  refine ⟨S, hgpacS, sysG.length + v, hvS, fun n ↦ ?_⟩
  have huniq := genSolveN_unique_val S hwfS (compTargetState sysF sysG w)
    (compTargetState_fixed sysF sysG hgpacF hnoF (gpac_wf hgpacG) w hw)
    (n + 1) (sysG.length + v) n hvS (Nat.lt_succ_self n)
  rw [extractClosed_genSolveND_fst] at huniq
  change ((Jet.compZero ⟨f⟩ ⟨g⟩).coeff n).val =
    ((((genStepN S (Γ := [])).eval Env.nil)^[n + 1] ((initN S (Γ := [])).eval Env.nil))
      (sysG.length + v) n).val
  rw [huniq]
  unfold compTargetState
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  exact (compZero_congr_val ⟨f⟩ ⟨solN sysF v⟩ ⟨g⟩ hf_val n).trans
    (comp_compZero_congr_right_val ⟨solN sysF v⟩ ⟨g⟩ ⟨solN sysG w⟩ hg_val n)

#print axioms InGPAC_noInteg
#print axioms InGPAC_comp

end HAomega
