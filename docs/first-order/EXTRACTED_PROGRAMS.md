# Extracted Programs

This file is the quick index for the concrete programs exported by the
modified-realizability pipeline.

The uniform core is:

```lean
extract D ρ [] n
```

where `D : Deriv [] φ` is a closed proof in the object fragment.  The helper
API in `Realizability/Meta/ProgramExtraction.lean` turns common theorem shapes
into ordinary readers:

```lean
extractedFamily D
extractedAt D n
extractedCtQ D
witness1 D m a
witness2 D m a b
witness3 D m a b c
witness4 D m a b c d
tag2 D m a b
```

These helpers do not re-prove anything. They apply the extracted realizer to
numeral arguments and read the witness or disjunction tag.

## User-Facing Extracted Programs

The short definitions below are the callable readers.  The "expanded extracted
program body" blocks show the actual program skeleton printed by `#realizer`:
they are the extracted program before it is applied/read as an ordinary witness
function.

### Fibonacci

File: `Realizability/Theorems/Fibonacci/FibonacciExtraction.lean`

```lean
def fibonacci (n : ℕ) : ℕ :=
  fstPT (fstPT (app₁ (extract fibPairedTheorem (fun _ ↦ 0) [] 5) (natPT 5 n)))
    (defaultPT 4)

def fibNext (n : ℕ) : ℕ :=
  fstPT (sndPT (app₁ (extract fibPairedTheorem (fun _ ↦ 0) [] 5) (natPT 5 n)))
    (defaultPT 4)
```

Correctness:

```lean
theorem fibonacci_spec (n : ℕ) : fibonacci n = fibN n
theorem fibNext_spec (n : ℕ) : fibNext n = fibN (n + 1)
```

Continuous/CtQ program:

```lean
theorem fib_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract fibPairedTheorem ρ [] 1)

noncomputable def fibRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2
```

Expanded extracted program body:

```text
ind / indRecC  (recurse on succ)
   andI  ⟨_,_⟩
      exI  ⟨witness = 0, ·⟩
         · ⟨contentless⟩  fib(0) = 0
      exI  ⟨witness = 1, ·⟩
         · ⟨contentless⟩  fib(1) = 1
   allI  (Λk)
      impI  (λ)
         exE  (let ⟨w,p⟩ := …)
            andE₁  (π₁)
               ax  (head hypothesis)
            exE  (let ⟨w,p⟩ := …)
               andE₂  (π₂)
                  wk  (weaken)
                     ax  (head hypothesis)
               andI  ⟨_,_⟩
                  exI  ⟨witness = x4, ·⟩
                     · ⟨contentless⟩  fib(S(x0)) = x4
                  exI  ⟨witness = (x3+x4), ·⟩
                     · ⟨contentless⟩  fib(S(S(x0))) = (x3+x4)
```

Reading this as a program: ordinary induction builds the pair
`(fib n, fib (n+1))`.  The step extracts the previous two witnesses `x3`,
`x4`, returns `x4` as the next first component, and returns `x3 + x4` as the
next second component.

### Pascal Mod 2

File: `Realizability/Theorems/Pascal/PascalExtraction.lean`

```lean
def pasTag (n k : ℕ) : ℕ :=
  tag₂ pasTotal 6 n k

def pasDecide (n k : ℕ) : ℕ :=
  if pasTag n k = 0 then 1 else 0
```

Correctness:

```lean
theorem pasDecide_eq (n k : ℕ) : pasDecide n k = pasN n k
```

Continuous/CtQ program:

```lean
theorem pas_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract pasTotal ρ [] 1)

noncomputable def pasRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2
```

Expanded extracted program body:

```text
ind / indRecC  (recurse on succ)
   ind / indRecC  (recurse on succ)
      orI₁  (inl, tag 0)
         · ⟨contentless⟩  pas(0,0) = 1
      allI  (Λk)
         impI  (λ)
            orI₂  (inr, tag 1)
               · ⟨contentless⟩  pas(0,S(x2)) = 0
   allI  (Λk)
      impI  (λ)
         ind / indRecC  (recurse on succ)
            orI₁  (inl, tag 0)
               · ⟨contentless⟩  pas(S(x1),0) = 1
            allI  (Λk)
               impI  (λ)
                  orE  (case)
                     allE[x2]  (inst)
                        wk  (weaken)
                           ax  (head hypothesis)
                     orE  (case)
                        wk  (weaken)
                           allE[S(x2)]  (inst)
                              wk  (weaken)
                                 ax  (head hypothesis)
                        orI₂  (inr, tag 1)
                           · ⟨contentless⟩  pas(S(x1),S(x2)) = 0
                        orI₁  (inl, tag 0)
                           · ⟨contentless⟩  pas(S(x1),S(x2)) = 1
                     orE  (case)
                        wk  (weaken)
                           allE[S(x2)]  (inst)
                              wk  (weaken)
                                 ax  (head hypothesis)
                        orI₁  (inl, tag 0)
                           · ⟨contentless⟩  pas(S(x1),S(x2)) = 1
                        orI₂  (inr, tag 1)
                           · ⟨contentless⟩  pas(S(x1),S(x2)) = 0
```

Reading this as a program: the extracted value is a decision tag.  `orI₁`
returns tag `0` for the branch `pas(n,k) = 1`; `orI₂` returns tag `1` for the
branch `pas(n,k) = 0`; the nested `orE` nodes are the XOR/case split for the
Pascal recurrence.

### Goodstein

File: `Realizability/Theorems/Goodstein/GoodsteinExtraction.lean`

```lean
def goodsteinStopTime (m : ℕ) : ℕ :=
  witness₁ goodsteinTheorem 11 m
```

Correctness:

```lean
theorem goodsteinStopTime_spec (m : ℕ) :
    goodN m (goodsteinStopTime m) = 0
```

Continuous/CtQ program:

```lean
theorem goodstein_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract goodsteinTheorem ρ [] 1)

noncomputable def goodsteinRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2
```

Expanded extracted program body:

```text
allI  (Λk)
   impE  (app)
      allE[0]  (inst)
         allE[ord(2,good(x2,0))]  (inst)
            tiEps0 / tiRecC  (recurse along ≺)
               allI  (Λk)
                  impI  (λ)
                     allI  (Λk)
                        impI  (λ)
                           orE  (case)
                              eqDec  ⟨decide good(x2,x3) = 0⟩
                              exI  ⟨witness = x3, ·⟩
                                 · ⟨contentless⟩  good(x2,x3) = 0
                              impE  (app)
                                 allE[ord(S(S(S(x3))),good(x2,S(x3)))]  (inst)
                                    allI  (Λk)
                                       impI  (λ)
                                          impE  (app)
                                             allE[S(x3)]  (inst)
                                                impE  (app)
                                                   allE[x5]  (inst)
                                                      wk  (weaken)
                                                         wk  (weaken)
                                                            wk  (weaken)
                                                               ax  (head hypothesis)
                                                   · ⟨contentless⟩  prec(x5,x1) = 1
                                             · ⟨contentless⟩  ord(S(S(S(x3))),good(x2,S(x3))) = x5
                                 · ⟨contentless⟩  ord(S(S(S(x3))),good(x2,S(x3))) = ord(S(S(S(x3))),good(x2,S(x3)))
      · ⟨contentless⟩  ord(2,good(x2,0)) = ord(2,good(x2,0))
```

Reading this as a program: bind the input `m`; start transfinite recursion
along the ordinal of the initial Goodstein state; at state `x3`, decide whether
`good(m,x3) = 0`; if yes, return witness `x3`; if no, use the induction
hypothesis/recursive call at the strictly smaller ordinal for the next state.
The ordinal-descent proof is contentless at runtime but certifies termination.

### Tower of Hanoi

File: `Realizability/Theorems/Hanoi/HanoiExtraction.lean`

```lean
def hanoiSolution (n f t v : ℕ) : ℕ :=
  witness₄ hanoiTheorem 22 n f t v

def hanoiMoves (n : ℕ) : List (ℕ × ℕ) :=
  decodeMoves (n + 32) (hanoiSolution n 0 2 1)
```

Continuous/CtQ program:

```lean
theorem hanoi_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract hanoiTheorem ρ [] 1)

noncomputable def hanoiRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2
```

Expanded extracted program body, abbreviated only by indentation:

```text
allI  (Λk)
   allI  (Λk)
      allI  (Λk)
         allI  (Λk)
            exE  (let ⟨w,p⟩ := …)
               allE[x4]  (inst)
                  allE[x3]  (inst)
                     allE[x2]  (inst)
                        allE[x1]  (inst)
                           ind / indRecC  (recurse on succ)
                              allI  (Λk)
                                 allI  (Λk)
                                    allI  (Λk)
                                       exI  ⟨witness = 0, ·⟩
                                          andI  ⟨_,_⟩
                                             · ⟨contentless⟩  solves(0,x2,x3,x4,0) = 1
                                             · ⟨contentless⟩  S(mvcount(0)) = exp(2,0)
                              allI  (Λk)
                                 impI  (λ)
                                    allI  (Λk)
                                       allI  (Λk)
                                          allI  (Λk)
                                             exE  (let ⟨w,p⟩ := …)
                                                allE[x3]  (inst)
                                                   allE[x4]  (inst)
                                                      allE[x2]  (inst)
                                                         allI  (Λk)
                                                            allI  (Λk)
                                                               allI  (Λk)
                                                                  allE[x8]  (inst)
                                                                     allE[x7]  (inst)
                                                                        allE[x6]  (inst)
                                                                           ax  (head hypothesis)
                                                exE  (let ⟨w,p⟩ := …)
                                                   wk  (weaken)
                                                      exE  (let ⟨w,p⟩ := …)
                                                         allE[x2]  (inst)
                                                            allE[x3]  (inst)
                                                               allE[x4]  (inst)
                                                                  allI  (Λk)
                                                                     allI  (Λk)
                                                                        allI  (Λk)
                                                                           allE[x8]  (inst)
                                                                              allE[x7]  (inst)
                                                                                 allE[x6]  (inst)
                                                                                    ax  (head hypothesis)
                                                         exI  ⟨witness = x5, ·⟩
                                                            ax  (head hypothesis)
                                                   exI  ⟨witness = happ(x5,hcons(((x2·3)+x3),x9)), ·⟩
                                                      andI  ⟨_,_⟩
                                                         · ⟨contentless⟩  solves(S(x1),x2,x3,x4,happ(x5,hcons(((x2·3)+x3),x9))) = 1
                                                         · ⟨contentless⟩  S(mvcount(happ(x5,hcons(((x2·3)+x3),x9)))) = exp(2,S(x1))
               exI  ⟨witness = x5, ·⟩
                  andI  ⟨_,_⟩
                     · ⟨contentless⟩  solves(x1,x2,x3,x4,x5) = 1
                     · ⟨contentless⟩  mvcount(x5) = pred(exp(2,x1))
```

Reading this as a program: ordinary induction on disk count.  The base witness
is the empty move list `0`.  The step extracts the two recursive solutions
`x5` and `x9`, inserts the middle move `((x2·3)+x3)`, and returns the
concatenated encoded list `happ(x5,hcons(((x2·3)+x3),x9))`.

### Euclid / GCD

File: `Realizability/Theorems/Euclid/GcdExtraction.lean`

```lean
def gcdWitness (a b : ℕ) : ℕ :=
  fstPT (app₁ (app₁ (extract gcdTheorem (fun _ ↦ 0) [] 41) (natPT 41 a)) (natPT 40 b))
    (defaultPT 39)
```

Correctness:

```lean
theorem gcdWitness_dvd (a b : ℕ) :
    gcdWitness a b ∣ a ∧ gcdWitness a b ∣ b
```

Continuous/CtQ program:

```lean
theorem gcd_extract_continuous' (ρ : ℕ → ℕ) :
    Continuous2 (extract gcdTheorem ρ [] 1)

noncomputable def gcdRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2
```

### Sperner

File: `Realizability/Theorems/Sperner/SpernerExtraction.lean`

```lean
def spernerWitness (n w : ℕ) : ℕ :=
  fstPT (app₁ (app₁ (extract spernerBody (spEnv n w) [] 11) (defaultPT 11))
    (defaultPT 10)) (defaultPT 9)
```

Correctness:

```lean
theorem spernerWitness_spec (n w : ℕ)
    (h0 : lookN w 0 = 0) (hn : lookN w n = 1) :
    spernerWitness n w < n
      ∧ lookN w (spernerWitness n w) ≠ lookN w (spernerWitness n w + 1)
```

Continuous/CtQ program:

```lean
theorem sperner_extract_continuous' (ρ : ℕ → ℕ) :
    Continuous2 (extract spernerTheorem ρ [] 1)

noncomputable def spernerRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2
```

### Hydra

File: `Realizability/Theorems/Hydra/HydraExtraction.lean`

```lean
def hydraBattleLength (h : ℕ) : ℕ :=
  fstPT (app₁ (extract hydraTheorem (fun _ ↦ 0) [] 12) (natPT 12 h))
    (defaultPT 11)
```

Correctness:

```lean
theorem hydraBattleLength_spec (h : ℕ) :
    hydraSeqN h (hydraBattleLength h) = 0
```

Continuous/CtQ program:

```lean
theorem hydra_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract hydraTheorem ρ [] 1)

noncomputable def hydraRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2
```

Expanded extracted program body:

```text
allI  (Λk)
   impE  (app)
      allE[0]  (inst)
         allE[hord(hydra(x2,0))]  (inst)
            tiEps0 / tiRecC  (recurse along ≺)
               allI  (Λk)
                  impI  (λ)
                     allI  (Λk)
                        impI  (λ)
                           orE  (case)
                              eqDec  ⟨decide hydra(x2,x3) = 0⟩
                              exI  ⟨witness = x3, ·⟩
                                 · ⟨contentless⟩  hydra(x2,x3) = 0
                              impE  (app)
                                 allE[hord(hydra(x2,S(x3)))]  (inst)
                                    allI  (Λk)
                                       impI  (λ)
                                          impE  (app)
                                             allE[S(x3)]  (inst)
                                                impE  (app)
                                                   allE[x5]  (inst)
                                                      wk  (weaken)
                                                         wk  (weaken)
                                                            wk  (weaken)
                                                               ax  (head hypothesis)
                                                   · ⟨contentless⟩  prec(x5,x1) = 1
                                             · ⟨contentless⟩  hord(hydra(x2,S(x3))) = x5
                                 · ⟨contentless⟩  hord(hydra(x2,S(x3))) = hord(hydra(x2,S(x3)))
      · ⟨contentless⟩  hord(hydra(x2,0)) = hord(hydra(x2,0))
```

Reading this as a program: bind the encoded hydra `h`; start transfinite
recursion along the ordinal `hord(hydra(h,0))`; at move counter `x3`, decide
whether the current hydra is dead; if yes, return witness `x3`; if no, call the
induction hypothesis at the strictly smaller ordinal for the next state.  The
descent proof `prec(x5,x1) = 1` certifies the recursive call and erases at
runtime.

## Printed Realizer Trees

For proof-shape/program-shape output, use:

```lean
#realizer goodThreeExDeriv
#realizer goodsteinTheorem
#realizerCH goodsteinTheorem
```

For decompiled pseudocode, use the generic command:

```lean
#program goodThreeExDeriv
#program fibPairedTheorem
#program goodsteinTheorem
#program hydraTheorem
```

For example, `#program hydraTheorem` prints:

```text
decompiled extracted realizer (pseudocode)
------------------------------------------
fun k =>
  apply
    instantiate 0
      instantiate hord(hydra(x2,0))
        wellFoundedRecOnPrec
          fun k =>
            fun proof_arg =>
              fun k =>
                fun proof_arg =>
                  case split
                    decide(hydra(x2,x3) = 0)
                    return witness x3 with certificate
                      erase(hydra(x2,x3) = 0)
                    apply
                      instantiate hord(hydra(x2,S(x3)))
                        fun k =>
                          fun proof_arg =>
                            apply
                              instantiate S(x3)
                                apply
                                  instantiate x5
                                    weaken
                                      weaken
                                        weaken
                                          recursive_or_hypothesis_value
                                  erase(prec(x5,x1) = 1)
                              erase(hord(hydra(x2,S(x3))) = x5)
                      erase(hord(hydra(x2,S(x3))) = hord(hydra(x2,S(x3))))
    erase(hord(hydra(x2,0)) = hord(hydra(x2,0)))
```

The paper includes generated output from these commands in:

```text
paper/xray-small.tex
paper/xray-goodstein.tex
```
