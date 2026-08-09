/-
# Composition: an explicit associate for `α ↦ F (G α)`

Stretch goal.  Given

* an associate `a` for `F : (ℕ → ℕ) → ℕ`, and
* for each output coordinate `k`, an associate `g k` for the component
  functional `α ↦ G α k` of a map `G : (ℕ → ℕ) → (ℕ → ℕ)`,

this file *constructs* — not merely proves to exist — an associate
`compAssociate a g` for the composite `α ↦ F (G α)`
(`isAssociate_compAssociate`).  This is the type-2 kernel of the fact that
the countable functionals compose: Kleene's application `f | g` of
associates (Longley, *Notions of computability at higher types I*, §3.3.1;
Longley–Normann 2015, Ch. 8) computed with finite lookahead.

The construction, on (the code of) a finite sequence `σ`:

1. run each coordinate associate `g k` along the prefix chain of `σ`
   (`coordVal`); by the first-fire principle, whenever `σ` is a genuine
   initial segment of some `α`, a nonzero answer is the *correct* value
   `G α k + 1` — tentative values are never wrong, only absent;
2. collect the longest determined initial segment of the output
   (`readyLen`, `tentativeOut`), capping its length by `σ.length` so the
   search is bounded;
3. run `a` along the prefix chain of that determined output segment
   (`chainVal`).

Every search is bounded, so `compAssociate` is a computable function of
`a` and `g` — no classical choice enters the definition, only the proofs.

The corollary `continuous2_comp` restates the theorem for continuity alone:
if `F` is continuous and each `α ↦ G α k` is continuous, so is
`α ↦ F (G α)`.  (The brief types the second map as `G : ℕ → (ℕ → ℕ)`,
whose composite with `F` would be a type-1 function with no continuity
content; the intended reading formalized here is `G : (ℕ → ℕ) → (ℕ → ℕ)`,
continuous componentwise.  See docs/first-order/STATUS.md.)
-/
import ContinuousFunctionals.MainTheorem

namespace ContinuousFunctionals

/-! ## Running an associate along a prefix chain with bounded lookahead -/

/-- `firstAlong a σ m` is the first nonzero value among
`a (code (σ.take 0)), a (code (σ.take 1)), …, a (code (σ.take m))`,
or `0` if all of them are zero: the result of running the neighborhood
function `a` along the prefix chain of `σ`, looking no further than `m`.
This is Kleene's application `a | -` restricted to the finite information
`σ` (Longley, *Notions of computability at higher types I*, §3.3.1). -/
def firstAlong (a : ℕ → ℕ) (σ : List ℕ) : ℕ → ℕ
  | 0 => a (code (σ.take 0))
  | m + 1 =>
    if firstAlong a σ m ≠ 0 then firstAlong a σ m
    else a (code (σ.take (m + 1)))

@[simp] theorem firstAlong_zero (a : ℕ → ℕ) (σ : List ℕ) :
    firstAlong a σ 0 = a (code (σ.take 0)) := rfl

theorem firstAlong_succ (a : ℕ → ℕ) (σ : List ℕ) (m : ℕ) :
    firstAlong a σ (m + 1) =
      if firstAlong a σ m ≠ 0 then firstAlong a σ m
      else a (code (σ.take (m + 1))) := rfl

/-- While every prefix up to length `m` reads zero, so does `firstAlong`. -/
theorem firstAlong_eq_zero {a : ℕ → ℕ} {σ : List ℕ} :
    ∀ m : ℕ, (∀ j ≤ m, a (code (σ.take j)) = 0) → firstAlong a σ m = 0 := by
  intro m
  induction m with
  | zero => exact fun h => h 0 le_rfl
  | succ q ih =>
    intro h
    have h0 : firstAlong a σ q = 0 :=
      ih (fun j hj => h j (le_trans hj (Nat.le_succ q)))
    rw [firstAlong_succ, h0, if_neg (fun hc : (0 : ℕ) ≠ 0 => hc rfl)]
    exact h (q + 1) le_rfl

/-- Once the chain first fires — zeros strictly below `i`, nonzero at `i` —
`firstAlong` returns that first value for every lookahead `m ≥ i`. -/
theorem firstAlong_eq_of_fire {a : ℕ → ℕ} {σ : List ℕ} {i : ℕ}
    (hz : ∀ j < i, a (code (σ.take j)) = 0)
    (hi : a (code (σ.take i)) ≠ 0) :
    ∀ m, i ≤ m → firstAlong a σ m = a (code (σ.take i)) := by
  intro m
  induction m with
  | zero =>
    intro h0
    rw [Nat.le_zero.mp h0] at hi ⊢
    rfl
  | succ q ih =>
    intro hq
    rcases Nat.eq_or_lt_of_le hq with heq | hlt
    · have hzq : firstAlong a σ q = 0 :=
        firstAlong_eq_zero q (fun j hj => hz j (by omega))
      rw [firstAlong_succ, hzq, if_neg (fun hc : (0 : ℕ) ≠ 0 => hc rfl), heq]
    · have h1 := ih (Nat.lt_succ_iff.mp hlt)
      rw [firstAlong_succ, h1, if_pos hi]

/-- A nonzero `firstAlong` value is witnessed by a first fire: a stage
`i ≤ m` with zeros strictly below it, whose value `firstAlong` returns. -/
theorem exists_fire_of_firstAlong_ne_zero {a : ℕ → ℕ} {σ : List ℕ} {m : ℕ}
    (h : firstAlong a σ m ≠ 0) :
    ∃ i, i ≤ m ∧ a (code (σ.take i)) ≠ 0 ∧
      (∀ j < i, a (code (σ.take j)) = 0) ∧
      firstAlong a σ m = a (code (σ.take i)) := by
  have hex0 : ∃ j, j ≤ m ∧ a (code (σ.take j)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h (firstAlong_eq_zero m hcon)
  have hex : ∃ j, a (code (σ.take j)) ≠ 0 :=
    ⟨hex0.choose, hex0.choose_spec.2⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_, ?_⟩
  · obtain ⟨j₀, hj₀m, hj₀⟩ := hex0
    exact le_trans (Nat.find_min' hex hj₀) hj₀m
  · intro j hj
    by_contra hne
    exact Nat.find_min hex hj hne
  · obtain ⟨j₀, hj₀m, hj₀⟩ := hex0
    exact firstAlong_eq_of_fire
      (fun j hj => by by_contra hne; exact Nat.find_min hex hj hne)
      (Nat.find_spec hex) m (le_trans (Nat.find_min' hex hj₀) hj₀m)

/-- `chainVal a σ`: run the associate `a` along the whole prefix chain of
the finite sequence `σ` — the committed value (in the `+ 1` convention) of
`a` on the information `σ`, or `0` if `σ` does not yet suffice. -/
def chainVal (a : ℕ → ℕ) (σ : List ℕ) : ℕ :=
  firstAlong a σ σ.length

/-- On a genuine initial segment of `α` extending the firing stage of an
associate-style witness, `chainVal` returns the committed value.  (Stated
for a raw witness pair rather than `IsAssociate` so it applies to the
witness of a single point `α`.) -/
theorem chainVal_initSeg_of_le {a : ℕ → ℕ} {v : ℕ} {α : ℕ → ℕ} {n₀ : ℕ}
    (hv : a (code (initSeg α n₀)) = v + 1)
    (hz : ∀ m < n₀, a (code (initSeg α m)) = 0)
    {n : ℕ} (hn : n₀ ≤ n) :
    chainVal a (initSeg α n) = v + 1 := by
  have hz' : ∀ j < n₀, a (code ((initSeg α n).take j)) = 0 := by
    intro j hj
    rw [initSeg_take α (le_trans (le_of_lt hj) hn)]
    exact hz j hj
  have hi' : a (code ((initSeg α n).take n₀)) ≠ 0 := by
    rw [initSeg_take α hn, hv]
    exact Nat.succ_ne_zero _
  have h := firstAlong_eq_of_fire hz' hi' n hn
  rw [initSeg_take α hn, hv] at h
  simpa [chainVal] using h

/-- The first-fire principle transported to `chainVal`, in fire-data
form: one known first-fire of `a` along `γ` forces every nonzero
`chainVal` on a genuine initial segment of `γ` to carry the same value —
tentative values are never wrong, only absent. -/
theorem chainVal_initSeg_eq_of_fire {a γ : ℕ → ℕ} {v p : ℕ}
    (hv : a (code (initSeg γ p)) = v + 1)
    (hz : ∀ m < p, a (code (initSeg γ m)) = 0)
    {n : ℕ} (h : chainVal a (initSeg γ n) ≠ 0) :
    chainVal a (initSeg γ n) = v + 1 := by
  have h' : firstAlong a (initSeg γ n) n ≠ 0 := by
    simpa [chainVal] using h
  obtain ⟨i, him, hi, hzi, heq⟩ := exists_fire_of_firstAlong_ne_zero h'
  rw [initSeg_take γ him] at hi heq
  have hz' : ∀ j < i, a (code (initSeg γ j)) = 0 := by
    intro j hj
    have h0 := hzi j hj
    rwa [initSeg_take γ (le_trans (le_of_lt hj) him)] at h0
  have hval := firstFire_eq_of_fire hv hz hi hz'
  have hcv : chainVal a (initSeg γ n) = firstAlong a (initSeg γ n) n := by
    simp [chainVal]
  rw [hcv, heq, hval]

/-- The associate-hypothesis form of `chainVal_initSeg_eq_of_fire`. -/
theorem IsAssociate.chainVal_initSeg_of_ne_zero {a : ℕ → ℕ}
    {F : (ℕ → ℕ) → ℕ} (ha : IsAssociate a F) {α : ℕ → ℕ} {n : ℕ}
    (h : chainVal a (initSeg α n) ≠ 0) :
    chainVal a (initSeg α n) = F α + 1 := by
  obtain ⟨p, hv, hz⟩ := ha α
  exact chainVal_initSeg_eq_of_fire hv hz h

/-! ## Reconstructing the output segment from the input segment -/

/-- `coordVal g k σ`: the tentative value (in the `+ 1` convention) of the
`k`-th output coordinate, as computed from the finite information `σ` by
the coordinate associate `g k`. -/
def coordVal (g : ℕ → ℕ → ℕ) (k : ℕ) (σ : List ℕ) : ℕ :=
  chainVal (g k) σ

/-- `readyLen g σ j`: how many consecutive output coordinates `0, 1, 2, …`
(capped at `j`) have already been determined by the information `σ`. -/
def readyLen (g : ℕ → ℕ → ℕ) (σ : List ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    if readyLen g σ j = j ∧ coordVal g j σ ≠ 0 then j + 1
    else readyLen g σ j

@[simp] theorem readyLen_zero (g : ℕ → ℕ → ℕ) (σ : List ℕ) :
    readyLen g σ 0 = 0 := rfl

theorem readyLen_succ (g : ℕ → ℕ → ℕ) (σ : List ℕ) (j : ℕ) :
    readyLen g σ (j + 1) =
      if readyLen g σ j = j ∧ coordVal g j σ ≠ 0 then j + 1
      else readyLen g σ j := rfl

theorem readyLen_le (g : ℕ → ℕ → ℕ) (σ : List ℕ) :
    ∀ j, readyLen g σ j ≤ j := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ q ih =>
    rw [readyLen_succ]
    split
    · exact le_rfl
    · exact le_trans ih (Nat.le_succ q)

theorem readyLen_le_succ (g : ℕ → ℕ → ℕ) (σ : List ℕ) (j : ℕ) :
    readyLen g σ j ≤ readyLen g σ (j + 1) := by
  rw [readyLen_succ]
  split
  · exact le_trans (readyLen_le g σ j) (Nat.le_succ j)
  · exact le_rfl

theorem readyLen_mono (g : ℕ → ℕ → ℕ) (σ : List ℕ) :
    ∀ j' j, j ≤ j' → readyLen g σ j ≤ readyLen g σ j' := by
  intro j'
  induction j' with
  | zero =>
    intro j h
    rw [Nat.le_zero.mp h]
  | succ q ih =>
    intro j h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · exact le_trans (ih j (Nat.lt_succ_iff.mp hlt)) (readyLen_le_succ g σ q)

/-- Every coordinate below `readyLen` has a (tentative) value. -/
theorem coordVal_ne_zero_of_lt_readyLen (g : ℕ → ℕ → ℕ) (σ : List ℕ) :
    ∀ j k, k < readyLen g σ j → coordVal g k σ ≠ 0 := by
  intro j
  induction j with
  | zero => exact fun k hk => absurd hk (Nat.not_lt_zero k)
  | succ q ih =>
    intro k hk
    rw [readyLen_succ] at hk
    by_cases hc : readyLen g σ q = q ∧ coordVal g q σ ≠ 0
    · rw [if_pos hc] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · exact ih k (by rw [hc.1]; exact hlt)
      · rw [heq]
        exact hc.2
    · rw [if_neg hc] at hk
      exact ih k hk

/-- If all coordinates below `j` have values, `readyLen` reaches `j`. -/
theorem readyLen_eq_self (g : ℕ → ℕ → ℕ) (σ : List ℕ) :
    ∀ j, (∀ k < j, coordVal g k σ ≠ 0) → readyLen g σ j = j := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ q ih =>
    intro h
    have h1 : readyLen g σ q = q := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    rw [readyLen_succ, if_pos ⟨h1, h q (Nat.lt_succ_self q)⟩]

/-- The determined initial segment of the output: the values (shifted back
from the `+ 1` convention) of the first `readyLen` output coordinates. -/
def tentativeOut (g : ℕ → ℕ → ℕ) (σ : List ℕ) : List ℕ :=
  (List.range (readyLen g σ σ.length)).map (fun k => coordVal g k σ - 1)

/-- On a genuine initial segment of `α`, the reconstructed output segment
is a genuine initial segment of the output sequence `γ` — stated in
fire-data form: all that is needed is that each coordinate function
`g k` first-fires along `α` with value `γ k`.  This is where the
first-fire principle pays off: the tentative coordinate values are the
true ones. -/
theorem tentativeOut_initSeg_of_fires {g : ℕ → ℕ → ℕ} {γ α : ℕ → ℕ}
    (hcoord : ∀ k, ∃ p, g k (code (initSeg α p)) = γ k + 1 ∧
      ∀ m < p, g k (code (initSeg α m)) = 0) (n : ℕ) :
    tentativeOut g (initSeg α n)
      = initSeg γ (readyLen g (initSeg α n) n) := by
  apply List.ext_getElem
  · simp [tentativeOut, initSeg]
  · intro i h1 h2
    have hi : i < readyLen g (initSeg α n) n := by
      simpa [tentativeOut] using h1
    have hne : coordVal g i (initSeg α n) ≠ 0 :=
      coordVal_ne_zero_of_lt_readyLen g (initSeg α n) n i hi
    obtain ⟨p, hv, hz⟩ := hcoord i
    have hval : coordVal g i (initSeg α n) = γ i + 1 :=
      chainVal_initSeg_eq_of_fire hv hz hne
    have hL : (tentativeOut g (initSeg α n))[i] = coordVal g i (initSeg α n) - 1 := by
      simp [tentativeOut]
    have hR : (initSeg γ (readyLen g (initSeg α n) n))[i] = γ i := by
      simp [initSeg]
    rw [hL, hR, hval]
    omega

/-- The associate-hypothesis form of `tentativeOut_initSeg_of_fires`. -/
theorem tentativeOut_initSeg {g : ℕ → ℕ → ℕ} {G : (ℕ → ℕ) → ℕ → ℕ}
    (hg : ∀ k, IsAssociate (g k) (fun α => G α k)) (α : ℕ → ℕ) (n : ℕ) :
    tentativeOut g (initSeg α n)
      = initSeg (G α) (readyLen g (initSeg α n) n) :=
  tentativeOut_initSeg_of_fires (fun k => hg k α) n

/-! ## The composite associate -/

/-- **The composite associate.**  On (the code of) a finite sequence `σ`:
reconstruct the determined initial segment of the output (`tentativeOut`),
then run the outer associate `a` along its prefix chain (`chainVal`).
An explicit — indeed computable — function of `a` and `g`. -/
def compAssociate (a : ℕ → ℕ) (g : ℕ → ℕ → ℕ) : ℕ → ℕ := fun k =>
  chainVal a (tentativeOut g (decodeList k))

theorem compAssociate_code (a : ℕ → ℕ) (g : ℕ → ℕ → ℕ) (σ : List ℕ) :
    compAssociate a g (code σ) = chainVal a (tentativeOut g σ) := by
  unfold compAssociate
  rw [decodeList_code]

/-- Finitely many naturals admit a common bound. -/
theorem exists_bound (m : ℕ → ℕ) : ∀ p : ℕ, ∃ N, ∀ k < p, m k ≤ N := by
  intro p
  induction p with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ q ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨max N (m q), fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact le_trans (hN k h) (le_max_left _ _)
    · rw [h]
      exact le_max_right _ _

/-- **Level-free core of the composition theorem.**  If each coordinate
function `g k` first-fires along `α` with value `γ k` (so the tentative
output reconstructed from prefixes of `α` is a genuine initial segment of
the sequence `γ`), and the outer function `b` first-fires along `γ` with
value `v`, then `compAssociate b g` first-fires along `α` with value `v`.
No associate hypothesis appears: the argument runs entirely on fire data,
which is what lets the hierarchy instantiate it at every level
(`assoc_comp` in `Hierarchy.lean`). -/
theorem compAssociate_fire_of_fires {b : ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    {γ α : ℕ → ℕ} {v : ℕ}
    (hcoord : ∀ k, ∃ p, g k (code (initSeg α p)) = γ k + 1 ∧
      ∀ m < p, g k (code (initSeg α m)) = 0)
    (hb : ∃ p, b (code (initSeg γ p)) = v + 1 ∧
      ∀ m < p, b (code (initSeg γ m)) = 0) :
    ∃ n, compAssociate b g (code (initSeg α n)) = v + 1 ∧
      ∀ m < n, compAssociate b g (code (initSeg α m)) = 0 := by
  classical
  obtain ⟨p, hpv, hpz⟩ := hb
  -- Firing stages (on `α`) of the coordinate functions.
  choose m hmv hmz using hcoord
  have hcoord : ∀ k, ∃ p, g k (code (initSeg α p)) = γ k + 1 ∧
      ∀ m' < p, g k (code (initSeg α m')) = 0 :=
    fun k => ⟨m k, hmv k, hmz k⟩
  -- A stage of `α` past `p` and past the first `p` coordinate firings.
  obtain ⟨M, hM⟩ := exists_bound m p
  have hcoordN : ∀ k < p, coordVal g k (initSeg α (max p M)) = γ k + 1 := by
    intro k hk
    exact chainVal_initSeg_of_le (hmv k) (hmz k)
      (le_trans (hM k hk) (le_max_right p M))
  have hready : p ≤ readyLen g (initSeg α (max p M)) (max p M) := by
    have h1 : readyLen g (initSeg α (max p M)) p = p :=
      readyLen_eq_self _ _ p (fun k hk => by
        rw [hcoordN k hk]; exact Nat.succ_ne_zero _)
    calc p = readyLen g (initSeg α (max p M)) p := h1.symm
      _ ≤ readyLen g (initSeg α (max p M)) (max p M) :=
        readyLen_mono _ _ (max p M) p (le_max_left p M)
  -- The composite fires at stage `max p M` …
  have hfire : compAssociate b g (code (initSeg α (max p M))) ≠ 0 := by
    rw [compAssociate_code, tentativeOut_initSeg_of_fires hcoord,
      chainVal_initSeg_of_le hpv hpz hready]
    exact Nat.succ_ne_zero _
  have hex : ∃ n, compAssociate b g (code (initSeg α n)) ≠ 0 := ⟨_, hfire⟩
  -- … so it has a least firing stage, where the value is forced.
  refine ⟨Nat.find hex, ?_, fun m' hm' => ?_⟩
  · have h0 := Nat.find_spec hex
    rw [compAssociate_code, tentativeOut_initSeg_of_fires hcoord] at h0 ⊢
    exact chainVal_initSeg_eq_of_fire hpv hpz h0
  · by_contra hne
    exact Nat.find_min hex hm' hne

/-- **Composition theorem** (stretch goal).  If `a` is an associate for
`F` and, for each output coordinate `k`, `g k` is an associate for
`α ↦ G α k`, then `compAssociate a g` — explicitly constructed above — is
an associate for the composite `α ↦ F (G α)`.

Existence of a firing stage: take a stage past the firing stages (on `α`)
of the first `p` coordinate associates and past `p` itself, where `p` is
the outer associate's witness stage on `G α`; then the reconstructed
output segment extends `initSeg (G α) p` and the outer chain fires.
Correctness at the *least* firing stage is automatic: the reconstructed
segment is always a genuine initial segment of `G α`
(`tentativeOut_initSeg`), so a nonzero outer chain value is forced to be
`F (G α) + 1` by the first-fire principle — no monotonicity analysis of
`readyLen` in the stage is needed.  All of this happens in the level-free
core `compAssociate_fire_of_fires`; this statement is its instance at the
fire data supplied by the two associate hypotheses. -/
theorem isAssociate_compAssociate {a : ℕ → ℕ} {g : ℕ → ℕ → ℕ}
    {F : (ℕ → ℕ) → ℕ} {G : (ℕ → ℕ) → ℕ → ℕ}
    (ha : IsAssociate a F) (hg : ∀ k, IsAssociate (g k) (fun α => G α k)) :
    IsAssociate (compAssociate a g) (fun α => F (G α)) := fun α =>
  compAssociate_fire_of_fires (fun k => hg k α) (ha (G α))

/-- Continuity is closed under composition with a componentwise continuous
map of Baire space: the purely topological corollary of the explicit
construction above, through the main theorem. -/
theorem continuous2_comp {F : (ℕ → ℕ) → ℕ} {G : (ℕ → ℕ) → ℕ → ℕ}
    (hF : Continuous2 F) (hG : ∀ k, Continuous2 (fun α => G α k)) :
    Continuous2 (fun α => F (G α)) := by
  obtain ⟨a, ha⟩ := hasAssociate_of_continuous hF
  choose g hg using fun k => hasAssociate_of_continuous (hG k)
  exact continuous_of_hasAssociate (isAssociate_compAssociate ha hg)

end ContinuousFunctionals
