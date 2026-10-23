/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ComposeSolve
import HAomega.ConstructiveFFT

/-!
# The Fourier layer, value level: trigonometric polynomials and the Taylor bridge

Closed-universe pillar 6, first half. A trigonometric polynomial is
`Σ_{|k| ≤ N} c_k e^{ikx}` with Gaussian-rational coefficients `c_k : CQ`.
They are closed, exactly, under `+`, `×` (convolution), `d/dx`
(`c_k ↦ ik·c_k`) and the mean-zero primitive `∫` (`c_k ↦ c_k/(ik)`, `k ≠ 0`).
Infinite Fourier series are not: a product coefficient of two infinite series
is an infinite sum. They belong to a bounds tier, like analytic jets.

`toJet` is the Taylor bridge: coefficient `n` is `Re(Σ c_k (ik)^n) / n!`.
The theorems relate the two layers, as rational values (`Q.val`):
`toJet` commutes with `d/dx` always and with `×` for real polynomials
(`c_{−k} = conj c_k`), `d/dx ∘ ∫` is the identity on mean-zero polynomials,
and the modes `cos(kx)`, `sin(kx)` map to the existing `cosFreq k`, `sinFreq k`.

Value level only (metatheory); the System T terms and in-logic statements are
the second half.
-/

namespace HAomega

/-- The rational `1/k` for a nonzero integer `k` (`num = sign k`, `den = |k|`). -/
def Q.invInt (k : Int) : Q := ⟨if k < 0 then -1 else 1, k.natAbs - 1⟩

/-- `z^n` in `CQ`. -/
def CQ.pow (z : CQ) : Nat → CQ
  | 0 => CQ.one
  | n + 1 => CQ.mul (CQ.pow z n) z

/-- A trigonometric polynomial `Σ_{|k| ≤ deg} c_k e^{ikx}`. -/
structure TrigPoly where
  deg : Nat
  c : Int → CQ

namespace TrigPoly

/-- The coefficient of `e^{ikx}`, zero outside `|k| ≤ deg`. -/
def coeff (p : TrigPoly) (k : Int) : CQ :=
  if k.natAbs ≤ p.deg then p.c k else CQ.zero

/-- The indices `−deg, …, deg`. -/
def range (N : Nat) : List Int :=
  (List.range (2 * N + 1)).map fun i ↦ (i : Int) - N

def add (p q : TrigPoly) : TrigPoly :=
  ⟨max p.deg q.deg, fun k ↦ CQ.add (p.coeff k) (q.coeff k)⟩

/-- `d/dx`: `c_k ↦ ik·c_k`. -/
def deriv (p : TrigPoly) : TrigPoly :=
  ⟨p.deg, fun k ↦ CQ.mul ⟨Q.zero, ⟨k, 0⟩⟩ (p.coeff k)⟩

/-- The mean-zero primitive: `c_k ↦ c_k/(ik) = −i·c_k/k` for `k ≠ 0`, `c_0 ↦ 0`. -/
def integ (p : TrigPoly) : TrigPoly :=
  ⟨p.deg, fun k ↦ if k = 0 then CQ.zero
    else CQ.mul ⟨Q.zero, Q.sub Q.zero (Q.invInt k)⟩ (p.coeff k)⟩

/-- `×`: convolution `(pq)_n = Σ_{|j| ≤ deg p} p_j q_{n−j}`. -/
def mul (p q : TrigPoly) : TrigPoly :=
  ⟨p.deg + q.deg, fun n ↦
    (range p.deg).foldl (fun acc j ↦ CQ.add acc (CQ.mul (p.coeff j) (q.coeff (n - j)))) CQ.zero⟩

/-- Real trigonometric polynomials: `c_{−k} = conj c_k` (as values). -/
def IsReal (p : TrigPoly) : Prop :=
  ∀ k : Int, ((p.coeff (-k)).re.val = (p.coeff k).re.val) ∧
    ((p.coeff (-k)).im.val = -(p.coeff k).im.val)

/-- The Taylor bridge: coefficient `n` is `Re(Σ_k c_k (ik)^n) / n!`. -/
def toJet (p : TrigPoly) : Jet :=
  ⟨fun n ↦ Q.div
    ((range p.deg).foldl
      (fun acc k ↦ CQ.add acc (CQ.mul (p.coeff k) (CQ.pow ⟨Q.zero, ⟨k, 0⟩⟩ n))) CQ.zero).re
    (Q.ofNat (fact n))⟩

/-- `cos(kx) = (e^{ikx} + e^{−ikx})/2`. -/
def cosMode (k : Nat) : TrigPoly :=
  ⟨k, fun j ↦ if j = k ∨ j = -(k : Int) then ⟨⟨1, 1⟩, Q.zero⟩ else CQ.zero⟩

/-- `sin(kx) = (e^{ikx} − e^{−ikx})/(2i)`: `c_k = −i/2`, `c_{−k} = i/2`. -/
def sinMode (k : Nat) : TrigPoly :=
  ⟨k, fun j ↦ if j = k then ⟨Q.zero, ⟨-1, 1⟩⟩ else if j = -(k : Int) then ⟨Q.zero, ⟨1, 1⟩⟩
    else CQ.zero⟩

/-- Proof-side Gaussian rationals `Rat × Rat` equipped with `CommRing`. -/
@[ext] structure CRat where
  re : Rat
  im : Rat

/-- Commutative ring structure on `CRat`. -/
instance : CommRing CRat where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  add a b := ⟨a.re + b.re, a.im + b.im⟩
  neg a := ⟨-a.re, -a.im⟩
  sub a b := ⟨a.re - b.re, a.im - b.im⟩
  mul a b := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
  nsmul n a := ⟨n * a.re, n * a.im⟩
  zsmul n a := ⟨n * a.re, n * a.im⟩
  natCast n := ⟨n, 0⟩
  intCast n := ⟨n, 0⟩
  add_assoc a b c := by
    ext
    · change (a.re + b.re) + c.re = a.re + (b.re + c.re); ring
    · change (a.im + b.im) + c.im = a.im + (b.im + c.im); ring
  zero_add a := by
    ext
    · change 0 + a.re = a.re; ring
    · change 0 + a.im = a.im; ring
  add_zero a := by
    ext
    · change a.re + 0 = a.re; ring
    · change a.im + 0 = a.im; ring
  add_comm a b := by
    ext
    · change a.re + b.re = b.re + a.re; ring
    · change a.im + b.im = b.im + a.im; ring
  left_distrib a b c := by
    ext
    · change a.re * (b.re + c.re) - a.im * (b.im + c.im) =
        (a.re * b.re - a.im * b.im) + (a.re * c.re - a.im * c.im); ring
    · change a.re * (b.im + c.im) + a.im * (b.re + c.re) =
        (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re); ring
  right_distrib a b c := by
    ext
    · change (a.re + b.re) * c.re - (a.im + b.im) * c.im =
        (a.re * c.re - a.im * c.im) + (b.re * c.re - b.im * c.im); ring
    · change (a.re + b.re) * c.im + (a.im + b.im) * c.re =
        (a.re * c.im + a.im * c.re) + (b.re * c.im + b.im * c.re); ring
  zero_mul a := by
    ext
    · change 0 * a.re - 0 * a.im = 0; ring
    · change 0 * a.im + 0 * a.re = 0; ring
  mul_zero a := by
    ext
    · change a.re * 0 - a.im * 0 = 0; ring
    · change a.re * 0 + a.im * 0 = 0; ring
  mul_assoc a b c := by
    ext
    · change (a.re * b.re - a.im * b.im) * c.re - (a.re * b.im + a.im * b.re) * c.im =
        a.re * (b.re * c.re - b.im * c.im) - a.im * (b.re * c.im + b.im * c.re); ring
    · change (a.re * b.re - a.im * b.im) * c.im + (a.re * b.im + a.im * b.re) * c.re =
        a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re - b.im * c.im); ring
  one_mul a := by
    ext
    · change 1 * a.re - 0 * a.im = a.re; ring
    · change 1 * a.im + 0 * a.re = a.im; ring
  mul_one a := by
    ext
    · change a.re * 1 - a.im * 0 = a.re; ring
    · change a.re * 0 + a.im * 1 = a.im; ring
  mul_comm a b := by
    ext
    · change a.re * b.re - a.im * b.im = b.re * a.re - b.im * a.im; ring
    · change a.re * b.im + a.im * b.re = b.re * a.im + b.im * a.re; ring
  sub_eq_add_neg a b := by
    ext
    · change a.re - b.re = a.re + -b.re; ring
    · change a.im - b.im = a.im + -b.im; ring
  nsmul_zero a := by
    ext
    · change ((0 : Nat) : Rat) * a.re = 0; simp
    · change ((0 : Nat) : Rat) * a.im = 0; simp
  nsmul_succ n a := by
    ext
    · change ((n + 1 : Nat) : Rat) * a.re = (n : Rat) * a.re + a.re; push_cast; ring
    · change ((n + 1 : Nat) : Rat) * a.im = (n : Rat) * a.im + a.im; push_cast; ring
  zsmul_zero' a := by
    ext
    · change ((0 : Int) : Rat) * a.re = 0; simp
    · change ((0 : Int) : Rat) * a.im = 0; simp
  zsmul_succ' n a := by
    ext
    · change ((Int.ofNat n.succ : Int) : Rat) * a.re = ((Int.ofNat n : Int) : Rat) * a.re + a.re
      simp only [Int.ofNat_eq_natCast, Nat.succ_eq_add_one]; push_cast; ring
    · change ((Int.ofNat n.succ : Int) : Rat) * a.im = ((Int.ofNat n : Int) : Rat) * a.im + a.im
      simp only [Int.ofNat_eq_natCast, Nat.succ_eq_add_one]; push_cast; ring
  zsmul_neg' n a := by
    ext
    · change ((Int.negSucc n : Int) : Rat) * a.re = -(((Int.ofNat n.succ : Int) : Rat) * a.re)
      simp only [Int.ofNat_eq_natCast, Nat.succ_eq_add_one]; push_cast; ring
    · change ((Int.negSucc n : Int) : Rat) * a.im = -(((Int.ofNat n.succ : Int) : Rat) * a.im)
      simp only [Int.ofNat_eq_natCast, Nat.succ_eq_add_one]; push_cast; ring
  neg_add_cancel a := by
    ext
    · change -a.re + a.re = 0; ring
    · change -a.im + a.im = 0; ring
  natCast_zero := by
    ext
    · change ((0 : Nat) : Rat) = 0; simp
    · rfl
  natCast_succ n := by
    ext
    · change ((n + 1 : Nat) : Rat) = (n : Rat) + 1; push_cast; rfl
    · change (0 : Rat) = 0 + 0; ring
  intCast_ofNat n := by
    ext
    · change (((n : Nat) : Int) : Rat) = (n : Rat); simp
    · rfl
  intCast_negSucc n := by
    ext
    · change ((Int.negSucc n : Int) : Rat) = -((n + 1 : Nat) : Rat); push_cast; ring
    · change (0 : Rat) = -0; ring

/-- Simp lemma for `.re` of `0 : CRat`. -/
@[simp] theorem CRat.zero_re : (0 : CRat).re = 0 := rfl

/-- Simp lemma for `.im` of `0 : CRat`. -/
@[simp] theorem CRat.zero_im : (0 : CRat).im = 0 := rfl

/-- Simp lemma for `.re` of `1 : CRat`. -/
@[simp] theorem CRat.one_re : (1 : CRat).re = 1 := rfl

/-- Simp lemma for `.im` of `1 : CRat`. -/
@[simp] theorem CRat.one_im : (1 : CRat).im = 0 := rfl

/-- Simp lemma for `.re` of addition in `CRat`. -/
@[simp] theorem CRat.add_re (a b : CRat) : (a + b).re = a.re + b.re := rfl

/-- Simp lemma for `.im` of addition in `CRat`. -/
@[simp] theorem CRat.add_im (a b : CRat) : (a + b).im = a.im + b.im := rfl

/-- Simp lemma for `.re` of negation in `CRat`. -/
@[simp] theorem CRat.neg_re (a : CRat) : (-a).re = -a.re := rfl

/-- Simp lemma for `.im` of negation in `CRat`. -/
@[simp] theorem CRat.neg_im (a : CRat) : (-a).im = -a.im := rfl

/-- Simp lemma for `.re` of subtraction in `CRat`. -/
@[simp] theorem CRat.sub_re (a b : CRat) : (a - b).re = a.re - b.re := rfl

/-- Simp lemma for `.im` of subtraction in `CRat`. -/
@[simp] theorem CRat.sub_im (a b : CRat) : (a - b).im = a.im - b.im := rfl

/-- Simp lemma for `.re` of multiplication in `CRat`. -/
@[simp] theorem CRat.mul_re (a b : CRat) : (a * b).re = a.re * b.re - a.im * b.im := rfl

/-- Simp lemma for `.im` of multiplication in `CRat`. -/
@[simp] theorem CRat.mul_im (a b : CRat) : (a * b).im = a.re * b.im + a.im * b.re := rfl

/-- Simp lemma for `.re` of `Nat.cast` in `CRat`. -/
@[simp] theorem CRat.natCast_re (n : Nat) : (n : CRat).re = n := rfl

/-- Simp lemma for `.im` of `Nat.cast` in `CRat`. -/
@[simp] theorem CRat.natCast_im (n : Nat) : (n : CRat).im = 0 := rfl

/-- Real-part additive homomorphism from `CRat` to `Rat`. -/
def CRat.reHom : CRat →+ Rat where
  toFun := CRat.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Imaginary-part additive homomorphism from `CRat` to `Rat`. -/
def CRat.imHom : CRat →+ Rat where
  toFun := CRat.im
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Real part of a `Finset.sum` in `CRat`. -/
theorem CRat.re_sum {α : Type} (s : Finset α) (f : α → CRat) :
    (∑ x ∈ s, f x).re = ∑ x ∈ s, (f x).re :=
  map_sum CRat.reHom f s

/-- Imaginary part of a `Finset.sum` in `CRat`. -/
theorem CRat.im_sum {α : Type} (s : Finset α) (f : α → CRat) :
    (∑ x ∈ s, f x).im = ∑ x ∈ s, (f x).im :=
  map_sum CRat.imHom f s

/-- Complex conjugation on `CRat`. -/
def CRat.conj (z : CRat) : CRat := ⟨z.re, -z.im⟩

/-- Conjugation commutes with multiplication in `CRat`. -/
theorem CRat.conj_mul (a b : CRat) :
    CRat.conj (a * b) = CRat.conj a * CRat.conj b := by
  ext <;> dsimp [CRat.conj] <;> ring

/-- Conjugation commutes with powers in `CRat`. -/
theorem CRat.conj_pow (z : CRat) : ∀ n : Nat,
    CRat.conj (z ^ n) = (CRat.conj z) ^ n
  | 0 => by ext <;> rfl
  | n + 1 => by rw [pow_succ, pow_succ, CRat.conj_mul, CRat.conj_pow z n]

/-- Map a `CQ` to its `CRat` value. -/
def toCRat (z : CQ) : CRat := ⟨z.re.val, z.im.val⟩

/-- `toCRat` maps `CQ.zero` to `0`. -/
theorem toCRat_zero : toCRat CQ.zero = 0 := by
  ext <;> exact Q.val_zero

/-- `toCRat` maps `CQ.one` to `1`. -/
theorem toCRat_one : toCRat CQ.one = 1 := by
  ext
  · exact Q.val_ofNat 1
  · exact Q.val_zero

/-- `toCRat` commutes with `CQ.add`. -/
theorem toCRat_add (a b : CQ) : toCRat (CQ.add a b) = toCRat a + toCRat b := by
  ext <;> exact Q.val_add _ _

/-- `toCRat` commutes with `CQ.mul`. -/
theorem toCRat_mul (a b : CQ) : toCRat (CQ.mul a b) = toCRat a * toCRat b := by
  ext
  · show (Q.sub (Q.mul a.re b.re) (Q.mul a.im b.im)).val =
      a.re.val * b.re.val - a.im.val * b.im.val
    rw [Q.val_sub, Q.val_mul, Q.val_mul]
  · show (Q.add (Q.mul a.re b.im) (Q.mul a.im b.re)).val =
      a.re.val * b.im.val + a.im.val * b.re.val
    rw [Q.val_add, Q.val_mul, Q.val_mul]

/-- `toCRat` commutes with `CQ.pow`. -/
theorem toCRat_pow (z : CQ) : ∀ n : Nat, toCRat (CQ.pow z n) = (toCRat z) ^ n
  | 0 => toCRat_one
  | n + 1 => by
    dsimp [CQ.pow]
    rw [toCRat_mul, toCRat_pow z n, pow_succ]

/-- Purely imaginary frequency `i · k` in `CRat`. -/
def ikCRat (k : Int) : CRat := ⟨0, (k : Rat)⟩

/-- `toCRat ⟨Q.zero, ⟨k, 0⟩⟩` equals `ikCRat k`. -/
theorem toCRat_ik (k : Int) : toCRat ⟨Q.zero, ⟨k, 0⟩⟩ = ikCRat k := by
  ext
  · exact Q.val_zero
  · exact Q.val_ofInt k

/-- `ikCRat (-k)` is the conjugate of `ikCRat k`. -/
theorem ikCRat_neg (k : Int) : ikCRat (-k) = CRat.conj (ikCRat k) := by
  ext <;> rfl

/-- `ikCRat (j + l)` splits additively into `ikCRat j + ikCRat l`. -/
theorem ikCRat_add (j l : Int) : ikCRat (j + l) = ikCRat j + ikCRat l := by
  ext
  · show (0 : Rat) = 0 + 0
    ring
  · show ((j + l : Int) : Rat) = (j : Rat) + (l : Rat)
    push_cast
    rfl

/-- `toCRat` turns a `CQ.add` fold over a list into `toCRat init` plus the list sum. -/
theorem toCRat_foldl_add {α : Type} (l : List α) (f : α → CQ) (init : CQ) :
    toCRat (l.foldl (fun acc x ↦ CQ.add acc (f x)) init) =
      toCRat init + (l.map (fun x ↦ toCRat (f x))).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, toCRat_add]
    ring

/-- The list coercion `(l : List Int)` for `l : List Nat` equals `l.map Int.ofNat`. -/
theorem coe_list_nat_int (l : List Nat) :
    (l : List Int) = l.map (fun i : Nat ↦ (i : Int)) := by
  induction l with
  | nil => rfl
  | cons a tl ih => exact congrArg (List.cons (a : Int)) ih

/-- Summing `g` over `range N` equals summing over `Finset.Icc (-N) N`. -/
theorem sum_range_eq_sum_Icc {β : Type} [AddCommMonoid β] (N : Nat) (g : Int → β) :
    ((range N).map g).sum = ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int), g k := by
  unfold range
  rw [coe_list_nat_int, List.map_map, List.map_map]
  change (∑ i ∈ Finset.range (2 * N + 1), g ((i : Int) - N)) = _
  refine Finset.sum_bij (fun (i : Nat) _ ↦ (i : Int) - N) ?_ ?_ ?_ ?_
  · intro i hi
    dsimp
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    omega
  · intro i₁ _ i₂ _ h
    dsimp at h
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    refine ⟨(k + N).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · dsimp
      omega
  · intro _ _
    rfl

/-- Evaluating a `CQ.add` fold over `range N` in `CRat` yields a `Finset.Icc (-N) N` sum. -/
theorem toCRat_foldl_range (N : Nat) (f : Int → CQ) :
    toCRat ((range N).foldl (fun acc k ↦ CQ.add acc (f k)) CQ.zero) =
      ∑ k ∈ Finset.Icc (-(N : Int)) (N : Int), toCRat (f k) := by
  rw [toCRat_foldl_add, toCRat_zero, zero_add, sum_range_eq_sum_Icc]

/-- The `n`-th complex spectral moment `Σ_{|k| ≤ deg p} c_k (ik)^n` in `CRat`. -/
def moment (p : TrigPoly) (n : Nat) : CRat :=
  ∑ k ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
    toCRat (p.coeff k) * (ikCRat k) ^ n

/-- Value of `(toJet p).coeff n` in terms of `moment p n` and `fact n`. -/
theorem toJet_coeff_val (p : TrigPoly) (n : Nat) :
    ((toJet p).coeff n).val = (moment p n).re / (fact n : Rat) := by
  have hfn_pos : 0 < fact n := fact_pos n
  have hfn_num : (Q.ofNat (fact n)).num ≠ 0 :=
    Int.ofNat_ne_zero.mpr (ne_of_gt hfn_pos)
  dsimp [toJet]
  rw [Q.val_div _ _ hfn_num, Q.val_ofNat]
  congr 1
  change (toCRat ((range p.deg).foldl
    (fun acc k ↦ CQ.add acc (CQ.mul (p.coeff k) (CQ.pow ⟨Q.zero, ⟨k, 0⟩⟩ n))) CQ.zero)).re = _
  rw [toCRat_foldl_range]
  unfold moment
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [toCRat_mul, toCRat_pow, toCRat_ik]

/-- Coefficient of `deriv p` in `CRat` equals `ikCRat k * toCRat (p.coeff k)`. -/
theorem toCRat_deriv_coeff (p : TrigPoly) (k : Int) :
    toCRat ((deriv p).coeff k) = ikCRat k * toCRat (p.coeff k) := by
  by_cases h : k.natAbs ≤ p.deg
  · have h1 : (deriv p).coeff k = CQ.mul ⟨Q.zero, ⟨k, 0⟩⟩ (p.coeff k) := if_pos h
    rw [h1, toCRat_mul, toCRat_ik]
  · have h1 : (deriv p).coeff k = CQ.zero := if_neg h
    have h2 : p.coeff k = CQ.zero := if_neg h
    rw [h1, h2, toCRat_zero, mul_zero]

/-- `moment (deriv p) n` equals `moment p (n + 1)`. -/
theorem moment_deriv (p : TrigPoly) (n : Nat) :
    moment (deriv p) n = moment p (n + 1) := by
  unfold moment
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [toCRat_deriv_coeff, pow_succ]
  ring

/-- `toJet` commutes with `d/dx`. -/
theorem toJet_deriv (p : TrigPoly) (n : Nat) :
    ((toJet (deriv p)).coeff n).val = ((Jet.deriv (toJet p)).coeff n).val := by
  rw [toJet_coeff_val, moment_deriv]
  dsimp [Jet.deriv]
  rw [Q.val_mul, Q.val_ofNat, toJet_coeff_val]
  have hn_rat : ((n + 1 : Nat) : Rat) ≠ 0 := by positivity
  have hfact : (fact (n + 1) : Rat) = ((n + 1 : Nat) : Rat) * (fact n : Rat) := by
    dsimp [fact]
    push_cast
    ring
  rw [hfact]
  field_simp

/-- For a real trigonometric polynomial `p`, `toCRat (p.coeff (-k))` is the conjugate of `toCRat (p.coeff k)`. -/
theorem IsReal.toCRat_neg {p : TrigPoly} (hp : IsReal p) (k : Int) :
    toCRat (p.coeff (-k)) = CRat.conj (toCRat (p.coeff k)) := by
  ext
  · exact (hp k).1
  · exact (hp k).2

/-- For a real trigonometric polynomial `p`, the imaginary part of `moment p n` is `0`. -/
theorem IsReal.moment_im_eq_zero {p : TrigPoly} (hp : IsReal p) (n : Nat) :
    (moment p n).im = 0 := by
  unfold moment
  rw [CRat.im_sum]
  let f : Int → Rat := fun k ↦ (toCRat (p.coeff k) * (ikCRat k) ^ n).im
  change ∑ k ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int), f k = 0
  have hneg : ∀ k : Int, f (-k) = -f k := by
    intro k
    have hterm : toCRat (p.coeff (-k)) * (ikCRat (-k)) ^ n =
        CRat.conj (toCRat (p.coeff k) * (ikCRat k) ^ n) := by
      rw [hp.toCRat_neg k, ikCRat_neg k, ← CRat.conj_pow, ← CRat.conj_mul]
    exact congrArg CRat.im hterm
  have hbij : ∑ k ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int), f k =
      ∑ k ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int), f (-k) := by
    refine Finset.sum_bij (fun k _ ↦ -k) ?_ ?_ ?_ ?_
    · intro k hk
      dsimp
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k₁ _ k₂ _ h
      dsimp at h
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      refine ⟨-k, ?_, by dsimp; omega⟩
      rw [Finset.mem_Icc]
      omega
    · intro k _
      dsimp
      rw [neg_neg]
  have hsum : ∑ k ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int), f (-k) =
      -(∑ k ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int), f k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ hneg k
  linarith

/-- For fixed `j` with `|j| ≤ p.deg`, summing `(p.coeff j) * (q.coeff (m - j)) * (ikCRat m)^n` over `|m| ≤ p.deg + q.deg` reindexes to `l = m - j` over `|l| ≤ q.deg`. -/
theorem sum_mul_shift_eq (p q : TrigPoly) (n : Nat) (j : Int)
    (hj : j ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int)) :
    (∑ m ∈ Finset.Icc (-((p.deg + q.deg : Nat) : Int)) ((p.deg + q.deg : Nat) : Int),
      toCRat (p.coeff j) * toCRat (q.coeff (m - j)) * (ikCRat m) ^ n) =
    ∑ l ∈ Finset.Icc (-(q.deg : Int)) (q.deg : Int),
      toCRat (p.coeff j) * toCRat (q.coeff l) * (ikCRat (j + l)) ^ n := by
  let Sl := Finset.Icc (-(q.deg : Int)) (q.deg : Int)
  let Sm := Finset.Icc (-((p.deg + q.deg : Nat) : Int)) ((p.deg + q.deg : Nat) : Int)
  let g : Int → CRat := fun m ↦ toCRat (p.coeff j) * toCRat (q.coeff (m - j)) * (ikCRat m) ^ n
  have hsub : Finset.image (fun l ↦ j + l) Sl ⊆ Sm := by
    intro m hm
    rw [Finset.mem_image] at hm
    rcases hm with ⟨l, hl, rfl⟩
    rw [Finset.mem_Icc] at hj hl ⊢
    omega
  have hzero : ∀ m ∈ Sm, m ∉ Finset.image (fun l ↦ j + l) Sl → g m = 0 := by
    intro m _ hnot
    have hmj : ¬ ((m - j).natAbs ≤ q.deg) := by
      intro hle
      apply hnot
      rw [Finset.mem_image]
      refine ⟨m - j, ?_, by omega⟩
      rw [Finset.mem_Icc]
      omega
    have hq0 : q.coeff (m - j) = CQ.zero := by
      unfold coeff
      exact if_neg hmj
    dsimp [g]
    rw [hq0, toCRat_zero, mul_zero, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  have hinj : Set.InjOn (fun l : Int ↦ j + l) Sl := fun _ _ _ _ h ↦ by dsimp at h; omega
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  dsimp [g]
  have hsub_add : j + l - j = l := by omega
  rw [hsub_add]

/-- Binomial convolution identity for `moment (mul p q) n`. -/
theorem moment_mul (p q : TrigPoly) (n : Nat) :
    moment (mul p q) n =
      ∑ a ∈ Finset.range (n + 1),
        (n.choose a : CRat) * moment p a * moment q (n - a) := by
  unfold moment
  have hstep1 :
      (∑ m ∈ Finset.Icc (-((mul p q).deg : Int)) ((mul p q).deg : Int),
        toCRat ((mul p q).coeff m) * (ikCRat m) ^ n) =
      ∑ j ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
        ∑ m ∈ Finset.Icc (-((p.deg + q.deg : Nat) : Int)) ((p.deg + q.deg : Nat) : Int),
          toCRat (p.coeff j) * toCRat (q.coeff (m - j)) * (ikCRat m) ^ n := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm_abs : m.natAbs ≤ (mul p q).deg := by
      rw [Finset.mem_Icc] at hm
      change m.natAbs ≤ p.deg + q.deg
      omega
    have hcoeff : (mul p q).coeff m = (mul p q).c m := if_pos hm_abs
    rw [hcoeff]
    dsimp [mul]
    rw [toCRat_foldl_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [toCRat_mul]
  rw [hstep1]
  have hstep2 :
      (∑ j ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
        ∑ m ∈ Finset.Icc (-((p.deg + q.deg : Nat) : Int)) ((p.deg + q.deg : Nat) : Int),
          toCRat (p.coeff j) * toCRat (q.coeff (m - j)) * (ikCRat m) ^ n) =
      ∑ j ∈ Finset.Icc (-(p.deg : Int)) (p.deg : Int),
        ∑ l ∈ Finset.Icc (-(q.deg : Int)) (q.deg : Int),
          ∑ a ∈ Finset.range (n + 1),
            (n.choose a : CRat) * (toCRat (p.coeff j) * (ikCRat j) ^ a) *
              (toCRat (q.coeff l) * (ikCRat l) ^ (n - a)) := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [sum_mul_shift_eq p q n j hj]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [ikCRat_add, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  rw [hstep2]
  simp_rw [Finset.sum_comm (s := Finset.Icc (-(q.deg : Int)) (q.deg : Int))]
  rw [Finset.sum_comm (s := Finset.Icc (-(p.deg : Int)) (p.deg : Int))]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- `fact` agrees with `Nat.factorial`. -/
theorem fact_eq_factorial : ∀ n : Nat, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by
    dsimp [fact, Nat.factorial]
    rw [fact_eq_factorial n]

/-- Evaluating `Jet.cauchyConvAux F G n m` in `Rat` yields a `Finset.range m` sum. -/
theorem cauchyConvAux_val (F G : Jet) (n : Nat) : ∀ m : Nat,
    (Jet.cauchyConvAux F G n m).val =
      ∑ a ∈ Finset.range m, (F.coeff a).val * (G.coeff (n - a)).val
  | 0 => by simp [Jet.cauchyConvAux, Q.val_zero]
  | m + 1 => by
    dsimp [Jet.cauchyConvAux]
    rw [Q.val_add, Q.val_mul, cauchyConvAux_val F G n m, Finset.sum_range_succ]

/-- For real polynomials, `toJet` turns the convolution product into the Cauchy product. -/
theorem toJet_mul (p q : TrigPoly) (hp : IsReal p) (hq : IsReal q) (n : Nat) :
    ((toJet (mul p q)).coeff n).val = (((toJet p).mul (toJet q)).coeff n).val := by
  rw [toJet_coeff_val, moment_mul, CRat.re_sum, Finset.sum_div]
  dsimp [Jet.mul]
  rw [cauchyConvAux_val]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at ha
  rw [hp.moment_im_eq_zero a, hq.moment_im_eq_zero (n - a),
    toJet_coeff_val p a, toJet_coeff_val q (n - a)]
  have hchoose_nat : n.choose a * fact a * fact (n - a) = fact n := by
    rw [fact_eq_factorial, fact_eq_factorial, fact_eq_factorial]
    exact Nat.choose_mul_factorial_mul_factorial ha
  have hchoose_rat : (fact n : Rat) = (n.choose a : Rat) * (fact a : Rat) * (fact (n - a) : Rat) := by
    exact_mod_cast hchoose_nat.symm
  have hc : (n.choose a : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos ha))
  have hfa : (fact a : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (fact_pos a))
  have hfb : (fact (n - a) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (fact_pos (n - a)))
  rw [hchoose_rat]
  field_simp
  ring

/-- For `k ≠ 0`, `(Q.invInt k).val` equals `1 / (k : Rat)`. -/
theorem invInt_val {k : Int} (hk : k ≠ 0) : (Q.invInt k).val = 1 / (k : Rat) := by
  have habs_pos : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk
  have hden : (Q.invInt k).den = k.natAbs := by
    unfold Q.invInt Q.den
    dsimp
    omega
  unfold Q.val
  rw [hden, natAbs_cast_rat]
  unfold Q.invInt
  dsimp
  split_ifs with hlt
  · have hlt_rat : (k : Rat) < 0 := by exact_mod_cast hlt
    rw [abs_of_neg hlt_rat]
    push_cast
    ring
  · have hge_rat : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Int.not_lt.mp hlt
    rw [abs_of_nonneg hge_rat]
    push_cast
    rfl

/-- `d/dx ∘ ∫` is the identity on mean-zero polynomials. -/
theorem deriv_integ (p : TrigPoly) (h0 : (p.coeff 0).re.val = 0 ∧ (p.coeff 0).im.val = 0)
    (k : Int) :
    ((deriv (integ p)).coeff k).re.val = (p.coeff k).re.val ∧
    ((deriv (integ p)).coeff k).im.val = (p.coeff k).im.val := by
  suffices h : toCRat ((deriv (integ p)).coeff k) = toCRat (p.coeff k) from
    ⟨congrArg CRat.re h, congrArg CRat.im h⟩
  by_cases hdeg : k.natAbs ≤ p.deg
  · have hcoeff_di : (deriv (integ p)).coeff k =
        CQ.mul ⟨Q.zero, ⟨k, 0⟩⟩ ((integ p).coeff k) := if_pos hdeg
    have hcoeff_i : (integ p).coeff k =
        if k = 0 then CQ.zero
        else CQ.mul ⟨Q.zero, Q.sub Q.zero (Q.invInt k)⟩ (p.coeff k) := if_pos hdeg
    rw [hcoeff_di, hcoeff_i]
    by_cases hk0 : k = 0
    · subst hk0
      rw [if_pos rfl, toCRat_mul, toCRat_zero, mul_zero]
      ext
      · exact h0.1.symm
      · exact h0.2.symm
    · rw [if_neg hk0, toCRat_mul, toCRat_mul, toCRat_ik]
      have hk_rat : (k : Rat) ≠ 0 := Int.cast_ne_zero.mpr hk0
      have hinv : toCRat ⟨Q.zero, Q.sub Q.zero (Q.invInt k)⟩ = ⟨0, -(1 / (k : Rat))⟩ := by
        ext
        · exact Q.val_zero
        · show (Q.sub Q.zero (Q.invInt k)).val = -(1 / (k : Rat))
          rw [Q.val_sub, Q.val_zero, zero_sub, invInt_val hk0]
      rw [hinv]
      ext <;>
        dsimp [ikCRat] <;>
        field_simp <;>
        ring
  · have h1 : (deriv (integ p)).coeff k = CQ.zero := if_neg hdeg
    have h2 : p.coeff k = CQ.zero := if_neg hdeg
    rw [h1, h2]

/-- Summing a function supported on `{K, -K}` over `Finset.Icc (-K) K` for `K = k + 1` gives `f K + f (-K)`. -/
theorem sum_Icc_pair (k : Nat) (f : Int → CRat)
    (h0 : ∀ j ∈ Finset.Icc (-((k + 1 : Nat) : Int)) ((k + 1 : Nat) : Int),
      j ≠ ((k + 1 : Nat) : Int) → j ≠ -((k + 1 : Nat) : Int) → f j = 0) :
    (∑ j ∈ Finset.Icc (-((k + 1 : Nat) : Int)) ((k + 1 : Nat) : Int), f j) =
      f ((k + 1 : Nat) : Int) + f (-((k + 1 : Nat) : Int)) := by
  let K : Int := ((k + 1 : Nat) : Int)
  have hsub : ({K, -K} : Finset Int) ⊆ Finset.Icc (-K) K := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_Icc]
    rcases hj with rfl | rfl <;> omega
  have hzero : ∀ j ∈ Finset.Icc (-K) K, j ∉ ({K, -K} : Finset Int) → f j = 0 := by
    intro j hj hnot
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact h0 j hj hnot.1 hnot.2
  rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : K ≠ -K)]

/-- Real part of `moment (cosMode (k + 1)) n` and `moment (sinMode (k + 1)) n` in terms of `(ikCRat (k + 1)) ^ n`. -/
theorem moment_modes_re (k n : Nat) :
    (moment (cosMode (k + 1)) n).re = ((ikCRat (k + 1)) ^ n).re ∧
    (moment (sinMode (k + 1)) n).re = ((ikCRat (k + 1)) ^ n).im := by
  let K : Int := ((k + 1 : Nat) : Int)
  have hhalf_pos : (⟨1, 1⟩ : Q).val = 1 / 2 := by
    unfold Q.val Q.den
    norm_num
  have hhalf_neg : (⟨-1, 1⟩ : Q).val = -1 / 2 := by
    unfold Q.val Q.den
    norm_num
  have hconj_pow : (ikCRat (-K)) ^ n = CRat.conj ((ikCRat K) ^ n) := by
    rw [ikCRat_neg, CRat.conj_pow]
  refine ⟨?_, ?_⟩
  · unfold moment
    change (∑ j ∈ Finset.Icc (-((k + 1 : Nat) : Int)) ((k + 1 : Nat) : Int),
      toCRat ((cosMode (k + 1)).coeff j) * (ikCRat j) ^ n).re = _
    rw [sum_Icc_pair k]
    · have hc1 : (cosMode (k + 1)).coeff K = ⟨⟨1, 1⟩, Q.zero⟩ := by
        unfold coeff cosMode
        dsimp
        rw [if_pos (by omega), if_pos (by omega)]
      have hc2 : (cosMode (k + 1)).coeff (-K) = ⟨⟨1, 1⟩, Q.zero⟩ := by
        unfold coeff cosMode
        dsimp
        rw [if_pos (by omega), if_pos (by omega)]
      change (toCRat ((cosMode (k + 1)).coeff K) * (ikCRat K) ^ n +
        toCRat ((cosMode (k + 1)).coeff (-K)) * (ikCRat (-K)) ^ n).re = ((ikCRat K) ^ n).re
      rw [hc1, hc2, hconj_pow]
      dsimp [toCRat, CRat.conj]
      rw [hhalf_pos, Q.val_zero]
      ring
    · intro j hj hj1 hj2
      have hcj : (cosMode (k + 1)).coeff j = CQ.zero := by
        unfold coeff cosMode
        dsimp
        split_ifs with h1 h2
        · rcases h2 with h2 | h2 <;> omega
        · rfl
        · rfl
      rw [hcj, toCRat_zero, zero_mul]
  · unfold moment
    change (∑ j ∈ Finset.Icc (-((k + 1 : Nat) : Int)) ((k + 1 : Nat) : Int),
      toCRat ((sinMode (k + 1)).coeff j) * (ikCRat j) ^ n).re = _
    rw [sum_Icc_pair k]
    · have hs1 : (sinMode (k + 1)).coeff K = ⟨Q.zero, ⟨-1, 1⟩⟩ := by
        unfold coeff sinMode
        dsimp
        rw [if_pos (by omega), if_pos (by omega)]
      have hs2 : (sinMode (k + 1)).coeff (-K) = ⟨Q.zero, ⟨1, 1⟩⟩ := by
        unfold coeff sinMode
        dsimp
        rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      change (toCRat ((sinMode (k + 1)).coeff K) * (ikCRat K) ^ n +
        toCRat ((sinMode (k + 1)).coeff (-K)) * (ikCRat (-K)) ^ n).re = ((ikCRat K) ^ n).im
      rw [hs1, hs2, hconj_pow]
      dsimp [toCRat, CRat.conj]
      rw [hhalf_pos, hhalf_neg, Q.val_zero]
      ring
    · intro j hj hj1 hj2
      have hsj : (sinMode (k + 1)).coeff j = CQ.zero := by
        unfold coeff sinMode
        dsimp
        split_ifs with h1 h2 h3
        · omega
        · omega
        · rfl
        · rfl
      rw [hsj, toCRat_zero, zero_mul]

/-- `Jet.sinCosFreqCoeffs K n` equals the imaginary and real parts of `(ikCRat K)^n / n!`. -/
theorem sinCosFreqCoeffs_eq_ikCRat_pow (K : Nat) : ∀ n : Nat,
    ((Jet.sinCosFreqCoeffs K n).1).val = ((ikCRat K) ^ n).im / (fact n : Rat) ∧
    ((Jet.sinCosFreqCoeffs K n).2).val = ((ikCRat K) ^ n).re / (fact n : Rat)
  | 0 => by
    dsimp [Jet.sinCosFreqCoeffs, fact]
    rw [Q.val_zero, Q.val_ofNat]
    change (0 : Rat) = (1 : CRat).im / 1 ∧ ((1 : Nat) : Rat) = (1 : CRat).re / 1
    change (0 : Rat) = 0 / 1 ∧ ((1 : Nat) : Rat) = 1 / 1
    norm_num
  | n + 1 => by
    have ih := sinCosFreqCoeffs_eq_ikCRat_pow K n
    have hn_num : (Q.ofNat (n + 1)).num ≠ 0 :=
      Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n)
    have hn_rat : ((n + 1 : Nat) : Rat) ≠ 0 := by positivity
    have hfact : (fact (n + 1) : Rat) = ((n + 1 : Nat) : Rat) * (fact n : Rat) := by
      dsimp [fact]
      push_cast
      ring
    dsimp [Jet.sinCosFreqCoeffs]
    rw [pow_succ, hfact]
    refine ⟨?_, ?_⟩
    · rw [Q.val_div _ _ hn_num, Q.val_mul, Q.val_ofNat, Q.val_ofNat, ih.2]
      change (K : Rat) * (((ikCRat K) ^ n).re / (fact n : Rat)) / ((n + 1 : Nat) : Rat) =
        (((ikCRat K) ^ n).re * ((K : Int) : Rat) + ((ikCRat K) ^ n).im * 0) /
          (((n + 1 : Nat) : Rat) * (fact n : Rat))
      push_cast
      field_simp
      ring
    · rw [Q.val_div _ _ hn_num, Q.val_neg, Q.val_mul, Q.val_ofNat, Q.val_ofNat, ih.1]
      change -((K : Rat) * (((ikCRat K) ^ n).im / (fact n : Rat))) / ((n + 1 : Nat) : Rat) =
        (((ikCRat K) ^ n).re * 0 - ((ikCRat K) ^ n).im * ((K : Int) : Rat)) /
          (((n + 1 : Nat) : Rat) * (fact n : Rat))
      push_cast
      field_simp
      ring

/-- The Fourier modes of frequency `k + 1 ≥ 1` map to the existing Taylor jets of
    `cos((k+1)x)`, `sin((k+1)x)`. (At frequency `0` the two exponentials coincide,
    so `cosMode 0` is `1/2`, not `cos 0 = 1`; the constant is `⟨0, fun _ ↦ 1⟩`.) -/
theorem toJet_modes (k n : Nat) :
    ((toJet (cosMode (k + 1))).coeff n).val = ((Jet.cosFreq (k + 1)).coeff n).val ∧
    ((toJet (sinMode (k + 1))).coeff n).val = ((Jet.sinFreq (k + 1)).coeff n).val := by
  have hm := moment_modes_re k n
  have hsc := sinCosFreqCoeffs_eq_ikCRat_pow (k + 1) n
  dsimp [Jet.cosFreq, Jet.sinFreq]
  rw [toJet_coeff_val, toJet_coeff_val, hm.1, hm.2, hsc.1, hsc.2]
  exact ⟨rfl, rfl⟩

end TrigPoly

#print axioms TrigPoly.toJet_deriv
#print axioms TrigPoly.toJet_mul
#print axioms TrigPoly.deriv_integ
#print axioms TrigPoly.toJet_modes

end HAomega
