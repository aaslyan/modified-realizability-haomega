/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import HAomega.ExtractedPrograms

/-!
# Tower of Hanoi in HA^ω — the encoding wall, removed

The first-order development codes a move sequence into a **single natural
number** (cons-list through the triangular pairing), and that encoding is its
wall: code bit-length squares per move, and `n = 5` is unreachable.  STATUS
records that deleting the ambient tower did not move that wall — the encoding
is the cost.

Here a move sequence is a **pair `(len, moves)` with `moves : ℕ → ℕ`** — data
as a function, which is the whole point of having higher types.  There is no
encoding to blow up, and the `#guard`s below run the solver at `n = 10`
(1023 moves, checked move-for-move against a reference) — double the
first-order reach, limited only by the answer's own size.

Two higher-type devices carry the construction, neither available first-order:

* **the recursion carries a function of the pegs**: `hanoiT` recurses at type
  `ℕ → ℕ → ℕ → (ℕ × (ℕ → ℕ))`, so the classic peg-permuting recursion
  `H (n+1) f t v = H n f v t ++ [f→t] ++ H n v t f` is *structural*;
* **sequence append is function surgery** (`appT`), an offset-shifted merge —
  no cons cells, no codes.

## Scope

`hanoiSpec` below is witness-style, like the Fibonacci case studies: the
existentials are discharged by the solver term itself, so the extract is the
solver, not a proof-computed object.  What is genuinely new in it: the second
existential is **`∃moves^(ℕ→ℕ)` — an existential over a function**, and the
extracted witness read off it *is* a function.  The `Solves`-checker theorem
(where an induction proves the produced sequence valid) is future work and is
not claimed.
-/

namespace HAomega

/-- The solution type: length paired with the move function.
A move is `3 * from + to`. -/
abbrev TySol : Ty := .prod .nat (.arrow .nat .nat)

/-- Append of two solutions: lengths add, the second function is consulted at
an offset.  The branch `i < len₁` is the usual `recNat` zero-test on
`isPos (len₁ ∸ i)`. -/
def appT {Γ : List Ty} : Tm Γ (.arrow TySol (.arrow TySol TySol)) :=
  .lam (.lam (.pair
    (.add (.fst (.var (.there .here))) (.fst (.var .here)))
    (.lam (.recNat
      (.app (.snd (.var (.there .here)))
        (.app (.app Tm.subT (.var .here)) (.fst (.var (.there (.there .here))))))
      (.lam (.lam (.app (.snd (.var (.there (.there (.there (.there .here))))))
        (.var (.there (.there .here))))))
      (.app Tm.isPos (.app (.app Tm.subT
        (.fst (.var (.there (.there .here))))) (.var .here)))))))

/-- The one-move solution `[3f + t]`. -/
def singleT {Γ : List Ty} : Tm Γ (.arrow .nat (.arrow .nat TySol)) :=
  .lam (.lam (.pair (.succ .zero)
    (.lam (.add (.var (.there (.there .here)))
      (.add (.var (.there (.there .here)))
        (.add (.var (.there (.there .here))) (.var (.there .here))))))))

/-- **The Hanoi solver.**  Recursion on the disk count at the higher type
`ℕ → ℕ → ℕ → TySol` — the carrier is a *function of the pegs*, so the
peg permutation of the classical recursion is just application order. -/
def hanoiT {Γ : List Ty} :
    Tm Γ (.arrow .nat (.arrow .nat (.arrow .nat (.arrow .nat TySol)))) :=
  .lam (.recNat
    (.lam (.lam (.lam (.pair .zero (.lam .zero)))))
    (.lam (.lam (.lam (.lam (.lam
      (.app (.app appT
        (.app (.app (.app (.var (.there (.there (.there .here))))
          (.var (.there (.there .here)))) (.var .here)) (.var (.there .here))))
      (.app (.app appT
        (.app (.app singleT (.var (.there (.there .here)))) (.var (.there .here))))
        (.app (.app (.app (.var (.there (.there (.there .here))))
          (.var .here)) (.var (.there .here))) (.var (.there (.there .here)))))))))))
    (.var .here))

/-! ## It runs — past the first-order wall -/

/-- The solver at the value level. -/
def hanoi (n f t v : Nat) : Nat × (Nat → Nat) :=
  (hanoiT (Γ := [])).eval Env.nil n f t v

/-- Decoded move list, `(from, to)` pairs. -/
def hanoiMoves (n : Nat) : List (Nat × Nat) :=
  let (len, mv) := hanoi n 0 2 1
  (List.range len).map (fun i ↦ (mv i / 3, mv i % 3))

/-- Reference implementation, plain Lean. -/
def hanoiRef : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | n + 1, f, t, v => hanoiRef n f v t ++ [3 * f + t] ++ hanoiRef n v t f

-- The classical small cases, matching the first-order `hanoiMoves` output.
#guard hanoiMoves 0 == []
#guard hanoiMoves 1 == [(0, 2)]
#guard hanoiMoves 2 == [(0, 1), (0, 2), (1, 2)]
#guard hanoiMoves 3 ==
  [(0,2),(0,1),(2,1),(0,2),(1,0),(1,2),(0,2)]

-- Lengths are 2^n − 1 …
#guard (List.range 11).map (fun n ↦ (hanoi n 0 2 1).1)
  == (List.range 11).map (fun n ↦ 2 ^ n - 1)

-- … and at n = 10 — double the first-order encoding wall — all 1023 moves
-- agree with the reference, move for move.
#guard (let (len, mv) := hanoi 10 0 2 1
        (List.range len).map mv == hanoiRef 10 0 2 1)

/-! ## The theorem, and the higher-type witness -/

/-- `∀n. ∃len. ∃moves^(ℕ→ℕ). len = fst (hanoi n 0 2 1) ∧ moves = snd (…)`.

The second existential quantifies over a **function**; equality at the arrow
type is the every-type `Formula.eq`.  Witness-style (see the header). -/
def hanoiSpec : Formula []
    (.arrow .nat (.prod .nat (.prod (.arrow .nat .nat) (.prod .unit .unit)))) :=
  .all .nat (.ex .nat (.ex (.arrow .nat .nat)
    (.and
      (.eq (.var (.there .here))
        (.fst (.app (.app (.app (.app hanoiT (.var (.there (.there .here))))
          .zero) (.succ (.succ .zero))) (.succ .zero))))
      (.eq (.var .here)
        (.snd (.app (.app (.app (.app hanoiT (.var (.there (.there .here))))
          .zero) (.succ (.succ .zero))) (.succ .zero)))))))

def hanoiDeriv : Deriv Ctx.nil hanoiSpec := by
  refine Deriv.allI ?_
  refine Deriv.exI (.fst (.app (.app (.app (.app hanoiT (.var .here))
    .zero) (.succ (.succ .zero))) (.succ .zero))) ?_
  refine Deriv.exI (.snd (.app (.app (.app (.app hanoiT (.var .here))
    .zero) (.succ (.succ .zero))) (.succ .zero))) ?_
  exact Deriv.andI (Deriv.eqRefl _) (Deriv.eqRefl _)

/-- The extracted program: length and the **function-valued** move witness. -/
def hanoiExtracted (n : Nat) : Nat × (Nat → Nat) :=
  let r := (extractClosed hanoiDeriv).eval Env.nil n
  (r.1, r.2.1)

-- The extracted witness agrees with the reference at n = 8 (255 moves).
#guard (let (len, mv) := hanoiExtracted 8
        len == 255 && (List.range len).map mv == hanoiRef 8 0 2 1)

#print axioms hanoiT
#print axioms hanoiDeriv
#print axioms hanoiExtracted

end HAomega
