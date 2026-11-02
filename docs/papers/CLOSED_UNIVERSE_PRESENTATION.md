# Plain-English Presentation Guide: A Closed Algebraic Universe of Calculus & Ordinal Differential Equations

> **Why this guide exists:** Instead of throwing Lean theorem names at you, this guide explains **from scratch, in plain English**, what problem we solved, what our **two main theories** actually say, how to explain each slide out loud, and what we **have** vs. **do not have**.

---

## Part 0: How to Explain the Whole Project in 60 Seconds

If someone asks you in a hallway: *"What did you build?"*, here is the plain-English answer:

1. **The Problem:** If you give a computer a function as a "black box" (plug in $x$, get out $f(x)$), the computer **cannot** reliably take its derivative (because tiny hidden wiggles smaller than your step $h$ can fool $\frac{f(x+h)-f(x)}{h}$), and integrating it to 10 digits of precision by Riemann rectangles takes **billions of steps**.
2. **Our Fix (Taylor Recipes + 2 Numbers):** Instead of a black box, every function in our system is stored as:
   - Its infinite list of Taylor coefficients $(c_0, c_1, c_2, \dots)$ where $f(x) = c_0 + c_1 x + c_2 x^2 + \cdots$, and
   - Two whole numbers $(M, R)$ that guarantee $|c_n| \le 2^M \cdot (2^R)^n$.
   With those two numbers, derivatives and integrals take **1 step**, and computing $f(x)$ to $k$ bits of precision only needs the first **$k + M + 3$ terms** (about 38 terms instead of 8 billion rectangles!).
3. **Theory #1 (The Closed Algebraic Box):** Start with just 5 basic functions ($\mathbb{Q}, x, e^x, \sin x, \cos x$). Combine them using $+, -, \times, \div$, derivatives $\frac{d}{dx}$, integrals $\int_0^x$, composition $f(g(x))$, polynomial differential equations $y' = P(y)$, local inverse functions $g^{-1}(x)$, and 2-variable implicit equations $E(x, y(x)) = 0$. **Theorem #1:** You *never leave the box*! Every operation automatically produces the new Taylor recipe $c_n$ and its new $(M, R)$ bounds.
4. **Theory #2 (Grading Differential Equations by Ordinal Numbers $< \varepsilon_0$):** Some functions in the box are simple ($1+x^2$) and some are wild ($e^{e^{e^x}}$). We attach a **Cantor ordinal number below $\varepsilon_0$** ($k < \omega, \omega, \omega^2, \omega^\omega, \dots$) to every equation and prove **4 strict impossibility theorems**:
   - Finite ordinals $k < \omega$ only make polynomials of degree $\le k$.
   - Level $\omega$ makes global waves ($e^x, \sin x, \cos x$) whose coefficients shrink with $n!$.
   - Level $\omega^2$ makes functions with finite-time blowup like $\frac{1}{1-x}$ (solving $y' = y^2$) — and **no formula below $\omega^2$ can ever equal $\frac{1}{1-x}$**.
   - The exponential tower $\omega^\omega, \omega^{\omega^\omega}, \dots$ makes nested exponentials $e^{e^{\cdot^{\cdot^x}}}$ whose Taylor coefficients are the **Bell numbers**, with $[x^2]f_h = \frac{h+1}{2}$, proving every level of the tower is a genuinely new function.

---

## Slide-by-Slide Plain-English Walkthrough (Matching `CLOSED_UNIVERSE_SLIDES.pdf`)

### Slide 1: Title & 4-Step Roadmap
- **What is on the slide:** The 4 questions the talk answers:
  1. Why is 100%-certain calculus on a computer hard?
  2. **Theory #1:** What is in our closed algebraic box, and why is it closed?
  3. **Theory #2:** How do ordinal numbers ($\omega, \omega^2, \omega^\omega < \varepsilon_0$) grade differential equations?
  4. **The Honest Ledger:** What do we have (100% proved in Lean 4) vs. what do we not have?

---

### Slide 2: The Problem — Why Black-Box Functions Break Calculus
- **The Simple Idea:** Suppose you only know how to evaluate a function $x \mapsto f(x)$ at points.
  - **Why derivatives fail:** To estimate $f'(x) \approx \frac{f(x+h)-f(x)}{h}$, how small should $h$ be? A function can sit completely flat at your sample points and wiggle wildly in between (*Myhill's Theorem, 1971*). Without knowing how fast $f''(x)$ can change, no finite test can certify $f'(x)$.
  - **Why integrals are slow:** To guarantee $\int_0^1 f(x)\,dx$ to 10 decimal places ($2^{-33}$) using Riemann sums, you have to slice $[0,1]$ into $2^{33} \approx 8.5\text{ billion}$ intervals.
- **How to say it out loud:**
  > *"If you treat a function as a black box that just plugs in $x$ and spits out $f(x)$, a computer cannot take its derivative with certainty, and integrating it to 10 digits takes billions of evaluations. We need a smarter representation of functions."*

---

### Slide 3: The Fix — Represent a Function by Its Taylor Recipe + 2 Numbers $(M, R)$
- **The Simple Idea:** Every smooth function around $0$ can be written as a power series:
  $$f(x) = c_0 + c_1 x + c_2 x^2 + c_3 x^3 + \cdots$$
  In our system ([`HAomega/RadiusJet.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RadiusJet.lean)), a function is a package of **two things**:
  1. **A computer recipe** $n \mapsto c_n \in \mathbb{Q}$ that computes the $n$-th Taylor coefficient.
  2. **Two whole numbers $(M, R)$** that guarantee the coefficients don't grow too fast:
     $$|c_n| \le 2^M \cdot (2^R)^n.$$
- **Why those two numbers $(M, R)$ solve everything:**
  - **Derivative $f'(x)$ is 1 line of code:** The $n$-th coefficient of $f'(x)$ is just $(n+1) c_{n+1}$. No limits!
  - **Integral $\int_0^x f(t)\,dt$ is 1 line of code:** The $(n+1)$-th coefficient is just $\frac{c_n}{n+1}$.
  - **Fast, 100% guaranteed evaluation:** Pick any $x$ inside the disk $|x| \le \frac{1}{2^{R+1}}$. Then:
    $$|c_n x^n| \le 2^M (2^R)^n \left(\frac{1}{2^{R+1}}\right)^n = \frac{2^M}{2^n}.$$
    Each term is at least **half as big** as the one before! So if you want $k$ bits of precision ($2^{-k}$), you just **add the first $k + M + 3$ terms** and stop. The remaining infinite tail is guaranteed to be smaller than $2^{-k}$!

---

### Slide 4: Theory #1 — Our Closed Algebraic System of Functions
- **What is inside the box?** ([`HAomega/UniverseGPAC.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseGPAC.lean), [`HAomega/UniverseExpr.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseExpr.lean), [`HAomega/SystemEval.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean))
  - **5 Seeds:** Any rational $q \in \mathbb{Q}$, the variable $x$, $e^x$, $\sin(x)$, and $\cos(x)$.
  - **6 Ways to Combine Functions:**
    1. **Add, Subtract, Multiply:** $f + g$, $f - g$, $f \cdot g$
    2. **Divide:** $f / g$ (whenever $g(0) \neq 0$)
    3. **Differentiate & Integrate:** $f'(x)$ and $\int_0^x f(t)\,dt$
    4. **Compose (Plug one inside another):** $f(g(x))$ (whenever $g(0) = 0$)
    5. **Solve any Polynomial Differential Equation:** $Y'(x) = P(Y(x))$, $Y(0) = Y_0$
    6. **Invert a Function or Solve an Implicit Equation:** Solve $g(y(x)) = x$ for $y = g^{-1}(x)$ ($g(0)=0, g'(0) \neq 0$) or $E(X(x), Z(y(x))) = 0$ ($E(0,0)=0, E_y(0,0) \neq 0$)
- **What "Closed" means:** Whenever you apply *any* of these 6 operations to functions in the box, the result is **still in the box** — the computer automatically builds its new Taylor recipe $c_n$ and calculates its new $(M, R)$ bounds!

---

### Slide 5: How Differential Equations, Inverse Functions & Implicit Curves Work Inside the Box
- **Why Differential Equations are Easy for Power Series:**
  Suppose $y(x) = y_0 + \int_0^x P(y(t))\,dt$. Because integrating $\int_0^x$ turns $x^n$ into $\frac{x^{n+1}}{n+1}$, the $(n+1)$-th coefficient of $y$ only depends on the earlier coefficients $c_0, c_1, \dots, c_n$!
  - Example: $\tan'(x) = 1 + \tan^2(x)$ with $\tan(0)=0$ locks in $c_0=0 \Rightarrow c_1=1 \Rightarrow c_2=0 \Rightarrow c_3=1/3 \Rightarrow c_5=2/15\dots$ one coefficient at a time, and Cauchy's method of majorants gives computed $(M, R) = (1, 8)$ ([`sysParams`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean#L82-L84)).
- **How Inverse & Implicit Functions Become Differential Equations ([`HAomega/UniverseInvFun.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseInvFun.lean), [`HAomega/UniverseImpFun.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseImpFun.lean)):**
  - Suppose you know $\sin(y)$ and want its inverse $y(x) = \arcsin(x)$, which satisfies $\sin(y(x)) = x$.
  - Differentiate both sides with respect to $x$: $\cos(y(x)) \cdot y'(x) = 1$, so $y'(x) = \frac{1}{\cos(y(x))}$.
  - Our theorem [`InGPAC_invFun`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseInvFun.lean) automatically compiles $g(y(x)) = x$ into a polynomial ODE system ([`invFunSys`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseInvFun.lean)) and outputs the exact Taylor series for $\arcsin(x) = x + \frac{1}{6}x^3 + \frac{3}{40}x^5 + \frac{5}{112}x^7 + \cdots$.
  - More generally, [`InGPAC_impFun`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseImpFun.lean#L938-L1044) compiles any 2-variable non-separable implicit equation $E(X(x), Z(y(x))) = 0$ via $y' = -E_x / E_y$ into [`impFunSys`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseImpFun.lean#L95-L108) (tested on $\sin(y) + x \cdot y - x = 0$).

---

### Slide 6: A Key Discovery — Global Waves vs. Functions That Can Blow Up
Inside our closed box, we proved there are **two distinct tiers of functions**:

| Feature | Tier 1: Global Functions ([`AnalyticJet`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/AnalyticJet.lean)) | Tier 2: Local Functions ([`RadiusJet`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RadiusJet.lean)) |
| :--- | :--- | :--- |
| **Growth Bound** | $|c_n| \cdot \mathbf{n!} \le 2^M \cdot (2^R)^n$ | $|c_n| \le 2^M \cdot (2^R)^n$ *(no $n!$)* |
| **Examples** | Polynomials, $e^x, \sin x, \cos x, \sinh x, \cosh x$ | $\frac{1}{1-x} = 1+x+x^2+\cdots$, $\tan x$, $\arcsin x$, $\ln(1+x)$ |
| **Where does it converge?** | **Everywhere** on $(-\infty, \infty)$ because $n!$ grows faster than any exponential | Only on a **finite disk** $|x| < 2^{-R}$ (e.g., $\frac{1}{1-x}$ blows up to $\infty$ at $x=1$!) |
| **What happens when you differentiate?** | $(n+1)$ is absorbed into $n! \mapsto (n+1)!$, so **the domain never shrinks** | Multiplying by $(n+1) \le 2 \cdot 2^n$ **halves the certified disk radius** ($R \mapsto R+1$) |

---

### Slide 7: All 7 "Rooms" of First-Year Calculus Are Built and Tested
Because the box is closed, every theorem of first-year calculus becomes a **working, verified computer program**:

1. **Symbolic Rules ([`QEquiv.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/QEquiv.lean), [`ProductRuleD.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ProductRuleD.lean), [`ChainRuleD.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ChainRuleD.lean), [`PythagorasD.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/PythagorasD.lean)):** Proves product rule, chain rule, FTC1/FTC2, and $\sin^2 x + \cos^2 x = 1$ inside `Deriv`.
2. **Definite Integrals ([`UExpr.defIntegral`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/DefiniteIntegral.lean)):** Computes $\int_a^b f(x)\,dx = F(b) - F(a)$ (tested on $\int_0^{1/2}\cos x\,dx = \sin(1/2)$ to $2^{-30}$).
3. **Finding Roots ([`UExpr.root`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/RootOperator.lean) & [`UExpr.newton`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/NewtonUniverse.lean)):** Uses extracted Bisection to bracket a root, then **Newton's Method** to double the number of accurate digits every step (computes $\ln(41/40)$ to **28 decimal places** in 4 steps!).
4. **Max / Min ([`UExpr.critical`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/CriticalPoints.lean)):** Differentiates $f$ to get $f'$, then finds where $f'(c) = 0$.
5. **Stepping ODEs ([`stepData`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemStep.lean), [`stepIterApprox`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemStep.lean)):** Re-centers a differential equation at a new point $x_0$ with explicit syntax-computed radius [`stepRadius`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemStep.lean) and convergence modulus [`stepModulus`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemStep.lean) so you can march along the curve across overlapping disks.
6. **Fourier Series ([`HAomega/TrigPolyInner.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/TrigPolyInner.lean)):** Proves $\cos(kx) \perp \sin(jx)$ and **Parseval's Identity** $\langle p, p \rangle = a_0^2 + \frac{1}{2}\sum (a_k^2 + b_k^2)$.
7. **Implicit & Boundary Equations ([`HAomega/UniverseInvFun.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseInvFun.lean), [`HAomega/UniverseImpFun.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/UniverseImpFun.lean), [`HAomega/ShootingBVP.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ShootingBVP.lean)):** Automatically compiles $g(y(x)) = x$ and 2-variable $E(X(x), Z(y(x))) = 0$ into polynomial ODE systems (tested on $\arcsin x$ and $\sin(y) + x \cdot y - x = 0$), and solves 2-point boundary value problems $y(0) = \alpha, y(b) = \beta$ via the certified shooting operator [`shootBVP`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ShootingBVP.lean) (tested on harmonic and nonlinear Duffing oscillators to $10^{-10}$).

---

### Slides 8 & 9: Theory #2 — How Ordinal Numbers Grade Differential Equations
- **The Simple Idea ([`HAomega/OrdinalODEHierarchy.lean`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean)):**
  How do we measure how complex a differential equation is? We attach a **Cantor ordinal number below $\varepsilon_0$** ($0, 1, 2, \dots, \omega, \omega^2, \omega^\omega, \dots$) to every formula:
  - Rational constants $q$ have ordinal $0$; variable $x$ has ordinal $1$; multiplying adds ordinals.
  - Linear waves ($e^x, \sin x, \cos x$, solving $y' = y$) jump to the first infinite ordinal **$\omega$**.
  - Division / reciprocal ($\frac{1}{1-x}$, solving the nonlinear ODE $y' = y^2$) jumps to **$\omega^2$**.
  - Plugging an exponential inside another ($e^{e^x}, e^{e^{e^x}}$) climbs the exponential tower **$\omega^\omega, \omega^{\omega^\omega}, \dots < \varepsilon_0$**.
- **What about "fake complexity" like $e^x - e^x = 0$?**
  A formula like $e^x - e^x$ looks like it uses $e^x$ (ordinal $\omega$), even though the function is just $0$! To prove that higher ordinals create **genuinely new functions**, we proved **4 unbreakable mathematical barriers** in Lean 4:

| Ordinal Level | What Functions Live Here | What We Proved (No Formula From a Lower Level Can Cross!) |
| :--- | :--- | :--- |
| **Level 1: Finite $k < \omega$** | **Polynomials of degree $\le k$** ($c_0 + c_1 x + \cdots + c_k x^k$) | Every Taylor coefficient $c_n = 0$ for $n > k$ ([`soundness_polyDegLe`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L844-L852)). **Impossibility ([`intrinsic_lower_bound_poly`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L912-L926)):** No polynomial expression of ordinal $\le k$ (even with cancellations!) can ever equal $x^{k+1}$. |
| **Level 2: $\omega \preceq \alpha \prec \omega^2$** | **Entire Waves & Linear ODE Systems** (`LinearGPACSys`, $\sum P_j(x)e^{k_j x}\sin(\omega_j x)$) | Coefficients never stop ($e^x$ is not a polynomial!), *but* they shrink fast: $|c_n|\cdot n! \le 2^M(2^R)^n$ ([`solN_linear_factorial_bound_computed`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1830-L1869), [`soundness_below_omegaSq`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1072-L1077)). |
| **Level 3: $\alpha = \omega^2$** | **Finite-Time Blowup / Poles** ($\frac{1}{1-x} = 1 + x + x^2 + \cdots$, solving $y' = y^2$) | Here $c_n = 1$ forever, so $c_n \cdot n! = n!$ grows faster than any exponential $2^M(2^R)^n$. **Impossibility ([`no_linearGPACSys_semJetEq_uGeom`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1885-L1890), [`no_isExpPoly_semJetEq_uGeom`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1145-L1148)):** **No linear ODE system of any dimension $N$ and no formula of ordinal $< \omega^2$ can ever equal $\frac{1}{1-x}$!** |
| **Level 4: Tower $\omega^\omega, \omega^{\omega^\omega}, \dots < \varepsilon_0$** | **Iterated Exponentials & "Waves Over Waves"** ([`uTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L588-L592), [`uWaveTower`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1950-L1952)) | Generates the combinatorial **Bell numbers** and transfinite wave-modulation cascades ($\sin x \mapsto \exp(\sin x) \mapsto \cdots$) inside the cumulative Descriptive Differential Hierarchy [`InDescDiff`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1907-L1909)! We proved $[x^2]\mathrm{uTower}(h+2) = \frac{h+1}{2}$ ([`uTower_eval_two`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L1225-L1235)) and $[x^2]\mathrm{uWaveTower}(h) = \frac{h}{2}$ ([`uWaveTower_eval_two`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2010-L2020)), proving all tower levels are distinct ([`uWaveTower_hierarchy_strictness`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/OrdinalODEHierarchy.lean#L2024-L2037)). |

---

### Slide 10: The Honest Ledger — What We Have vs. What We Do Not Have

#### What We HAVE (100% Proved in Lean 4, Zero `sorry`s)
1. **Complete Closed Algebra:** $+, -, \times, \div, \frac{d}{dx}, \int_0^x$, composition $f(g(x))$, polynomial ODE systems $Y' = P(Y)$, local inverse functions $g^{-1}(x)$, and 2-variable implicit functions $E(X(x), Z(y(x))) = 0$.
2. **Automatic $(M, R)$ Compiler & Evaluator:** Reads any formula or ODE system, extracts $(M, R)$ via [`sysParams`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/SystemEval.lean), and computes $f(x)$ to any accuracy $2^{-k}$.
3. **All 7 Calculus Rooms:** Symbolic rules in `Deriv`, definite integrals, bisection, quadratic Newton's method, critical points, multi-step ODE continuation with computed radii/moduli, finite Fourier inner products (Parseval), and 2-point boundary value problems via shooting ([`shootBVP`](file:///Users/araaslyan/modified-realizability-haomega/HAomega/ShootingBVP.lean)).
4. **The 4-Level $\varepsilon_0$ Ordinal Hierarchy:** Complete impossibility and separation proofs across $k < \omega$, $\omega$, $\omega^2$, and the $\omega$-exponential tower.

#### What We DO NOT Have (And Why)
1. **Non-Smooth Functions ($|x|$, step functions, ReLU):** They have sharp corners at $0$, so they do not have Taylor series. (Outside our analytic box by design.)
2. **Non-ODE Transcendental Functions ($\Gamma(x)$, $\zeta(s)$):** By Hölder's theorem (1887), Euler's Gamma function $\Gamma(x)$ cannot satisfy *any* polynomial differential equation, so it is outside our box.
3. **Automatic "Is $f = g$?" Button:** By Richardson's theorem, no computer algorithm can decide whether two arbitrary transcendental expressions equal $0$ everywhere (though we can prove identities like $\sin^2 x + \cos^2 x = 1$ using proof trees).
4. **Optional Future Extensions:**
   - **Dyadic Rounding in Newton's Method:** Rounding $x_m$ to $2^{-2^m}$ at each Newton step so rational denominators don't grow huge.
   - **Differential Transcendence of $e^{e^x}$:** Proving inside Lean that $e^{e^x}$ cannot be generated by a 1-variable polynomial ODE without composition.

---

### Slide 11: Bonus Idea — "Ordinal Music" (Hearing the Hierarchy!)
Because an analog music synthesizer (like a Moog) is physically a box of coupled integrators ($\int dt$), our ordinal hierarchy maps **every ordinal below $\varepsilon_0$ to a musical sound** ([`docs/foundations/UDE_COMPLEXITY_HIERARCHY.md`](file:///Users/araaslyan/modified-realizability-haomega/docs/foundations/UDE_COMPLEXITY_HIERARCHY.md)):
- **Finite Ordinals ($k < \omega$):** Polynomials $t^k$ $\longrightarrow$ **Volume fade-in / fade-out ramps** (no oscillation).
- **Level $\omega$ ($e^{-\gamma t}\sin(\omega_0 t)$):** Linear ODEs $\longrightarrow$ **Pure musical notes & chords** (clean harmonic overtones).
- **Level $\omega^\omega$ and $\omega^{\omega^\omega}$ ($\sin(t + \sin(t))$):** Nested compositions $\longrightarrow$ **FM Synthesizer Timbres** (Chowning FM synthesis, creating rich metallic sideband clouds).
- **A "Hydra" Song:** A Kirby–Paris Hydra or Goodstein sequence counting down $\omega^{\omega^\omega} \to \omega^2 \to \omega \cdot 3 \to 1 \to 0$ starts as a wild shimmering FM synthesizer cloud and resolves step-by-step into a pure harmonic chord before fading to silence!
