# A. R. Aslyan, *On Recursive Equations* (1997) — the foundation

Candidate of Sciences (Phys.-Math.) dissertation, Institute for Informatics and
Automation Problems (IIAP), National Academy of Sciences of Armenia, Yerevan, 1997.
Specialty A.01.09, Mathematical Cybernetics and Mathematical Logic.

This file is an English translation of the dissertation's **author's abstract
(автореферат)**, transcribed from the scan in the National Library of Armenia
(elib.am). It is the primary source for the results it states; the full
dissertation text is not in this repository. Original Russian terms are kept in
brackets where a translation choice matters. `[?]` marks places illegible in the
scan; editorial notes are marked *Note*.

Sections 1–3 are the translation. Section 4 records which results are proved
where, and section 5 the questions the text raises for the current programme.

---

## 1. Front matter

- **Title:** *On Recursive Equations* (О рекурсивных уравнениях; Armenian: Անդրադարձ հավասարումների մասին).
- **Scientific advisor:** H. B. Marandjian (Г. Б. Маранджян), Cand. Phys.-Math. Sci., senior researcher.
- **Official opponents:** Prof. I. D. Zaslavsky (И. Д. Заславский), Dr. Phys.-Math. Sci.; R. V. Topchyan (Р. В. Топчян), Cand. Phys.-Math. Sci., docent.
- **Leading organization:** Laboratory of Heuristic Physics of Armenia (Лаборатория эвристической физики Армении).
- **Defense:** 28 November 1997, 11:00, specialized council 037 "Mathematical Cybernetics and Mathematical Logic", IIAP NAS RA, 1 P. Sevak St., Yerevan 375044.
- **Abstract distributed:** 28 [?] October 1997 (the day is handwritten). Scientific secretary of the council: A. E. Melkonyan.

## 2. General characteristics of the dissertation

### Relevance of the topic

In recent decades researchers' interest in solving various kinds of recursive
equations, under various restrictions on those equations, has grown
considerably. This is driven in particular by the search for methods of
automated program synthesis for modern computers, and by methods of
transforming programs and other dynamic discrete systems to make them more
efficient. G. Kreisel [6] proposed an interesting application, in proof theory,
of methods for solving recursive (functional) equations and of the so-called
E-theorems, to finding and analysing computer programs.

But the need to solve recursive equations is by no means confined to
theoretical programming; mathematical logic is full of such examples. The
problem of constructing a functional satisfying given conditions arises, for
instance, in Gödel's famous consistency proof for intuitionistic arithmetic [1].
A problem of the same kind arises with **Kreisel's no-counterexample
interpretation** (интерпретация опровержением контрпримера) [5].

What these cases have in common is that the functionals (conditions) occurring
in the equations, and the solutions themselves, are subject to specific
restrictions dictated by the nature of the problem. On the one hand this
narrows the class of problems considerably; on the other, depending on the
problem, it can rule out powerful tools such as **Kleene's first recursion
(fixed point) theorem** [2, 3] — which is nothing other than the statement that
equations of the form

$$f(\tilde x) \simeq F(f, \tilde x),$$

with $F$ a recursive functional, have solutions in the class of partial
recursive functions.

Marandjian [7] considered the more general case of a *system* of recursive
equations

$$
\begin{aligned}
F_1\{f_1,\dots,f_n\}(\tilde x) &\simeq G_1\{f_1,\dots,f_n\}(\tilde x)\\
&\;\;\vdots\\
F_m\{f_1,\dots,f_n\}(\tilde x) &\simeq G_m\{f_1,\dots,f_n\}(\tilde x),
\end{aligned}
$$

where $F_1,\dots,F_m,G_1,\dots,G_m$ are recursive terms (terms denoting
recursive functionals of the functions $f_1,\dots,f_n$ and the variables
$\tilde x$). Following [7] we call these **general form recursive equations**
(G.F.R.E.; Russian Р.У.О.В., рекурсивные уравнения общего вида). In [7]
Marandjian formulated a necessary and sufficient condition for these equations
to have solutions.

Modern recursion theory — so-called generalized recursion theory — knows many
generalizations of recursive function and effective computability to various
domains. This work analyses the results of [7] for those generalizations, namely
for **functionals computable in the sense of Kleene** [3, 4, 5].

### Aim of the work

To find conditions for the existence of solutions of general form recursive
equations over **functionals of higher finite types** [3, 9], analogous to
Marandjian's condition [7] for G.F.R.E. over the natural numbers. The work also
studies the totalities of functions and functionals that are solutions of
G.F.R.E.; in particular it determines the classes of number-theoretic functions
(characteristic functions of predicates) that are **unique solutions** of systems
of G.F.R.E., i.e. that are uniquely representable by such a system.

### Scientific novelty and theoretical value

- A necessary and sufficient condition for the existence of solutions of
  recursive equations over functionals of higher finite types.
- For the first time, the classes of number-theoretic predicates and functions
  characterized as unique solutions of systems of G.F.R.E. are determined.
- For the first time, examples of recursive equations illustrating various
  properties of, and relations between, the functionals that solve them.

These and other results of the work are new. The questions treated matter both
for recursion theory itself and for its applications, such as proof theory and
theoretical programming, and may stimulate further research in this direction.
All results of the dissertation are new.

**Methods.** Classical recursion theory and mathematical logic.

**Presentation.** The main results were presented at the international
conference CSIT-97 (Computer Science and Information Technologies), at a
conference of the Armenian Mathematical Society, at a general meeting of the
IIAP scientific council, and at the theoretical programming seminar of HPL
Armenia.

**Publications.** Four papers (listed in section 3.5).

**Structure.** An introduction, three chapters and a bibliography.

## 3. Content of the dissertation

The introduction describes the problems studied and summarizes the work.

### 3.1 Chapter 1 — existence of solutions over higher types

General form recursive equations are introduced as equations

$$
\begin{aligned}
F_1\{f_1,\dots,f_n\}(\tilde\alpha) &\simeq G_1\{f_1,\dots,f_n\}(\tilde\alpha)\\
&\;\;\vdots\\
F_m\{f_1,\dots,f_n\}(\tilde\alpha) &\simeq G_m\{f_1,\dots,f_n\}(\tilde\alpha)
\end{aligned}
\qquad (1)
$$

where $F_1,\dots,G_m$ are recursive terms denoting recursive functionals. They
contain occurrences of **free variables $\tilde\alpha$ for functionals of higher
finite types** and function symbols $f_1,\dots,f_n$ for the unknown solutions.

Equations (1) were first considered by Marandjian [7] in the case where
$\tilde\alpha$ ranges over the natural numbers. He found a necessary and
sufficient condition for solvability and showed that the solvability problem
for these equations is **$\Sigma^0_3$-complete**. *(Note: the indices are read
from the scan as $\Sigma^0_3$.)* The condition proved here for (1) is the
analogue of Marandjian's result.

The condition uses the notion of an **$i$-fragment**. Given finitely many terms
$Q_1,\dots,Q_k$ and function symbols $f_1,\dots,f_n$:

1. every term $Q_i[f_1,\dots,f_n]$ is an $i$-fragment of $\langle \bar Q,\bar f\rangle$;
2. a term obtained from an $i$-fragment of $\langle \bar Q,\bar f\rangle$ by replacing
   one fixed occurrence of the function symbol $f_j$ with a $j$-fragment of
   $\langle \bar Q,\bar f\rangle$ is again an $i$-fragment of $\langle \bar Q,\bar f\rangle$.

**Theorem 1.1.** A system of recursive equations has a solution if and only if
there is a system of terms, and a corresponding replacement of the function
symbols $f_1,\dots,f_n$ in (1) by $i$-fragments of $\langle \bar Q,\bar f\rangle$, that turns
(1) into a system of **identities**

$$
\tilde F_1\{f_1,\dots,f_n\}(\tilde\alpha) \simeq \tilde G_1\{f_1,\dots,f_n\}(\tilde\alpha),\quad\dots,\quad
\tilde F_m\{f_1,\dots,f_n\}(\tilde\alpha) \simeq \tilde G_m\{f_1,\dots,f_n\}(\tilde\alpha).
$$

#### Quasi-solutions

When the variables $\tilde\alpha$ in (1) range only over number-theoretic
functions (type 1), the notion of a **quasi-solution** (квази-решение) is
introduced.

**Definition.** Let $\mathfrak I$ be a class of number-theoretic functions. A
system of functions $f_1^*,\dots,f_n^*$ is an **$\mathfrak I$-quasi-solution** of
the system (1) if for all $\tilde\alpha$ from $\mathfrak I$ and all $0<i\le m$ the
identity

$$F_i\{f_1^*,\dots,f_n^*\}(\tilde\alpha) \simeq G_i\{f_1^*,\dots,f_n^*\}(\tilde\alpha) \qquad (2)$$

holds.

**Theorem 1.3.** For every class $\mathfrak I$ of number-theoretic functions that
has a $\Pi^1_1$ definition, there is a G.F.R.E.

$$G\{f\}[\alpha_1,\alpha_2](x) \simeq 0$$

which **has no solutions**, but has an **everywhere defined recursive
$\mathfrak I$-quasi-solution**.

Now let $\Sigma^*$ be the class of functions **recursive in the class of all
$\Sigma^1_1$ predicates** (рекурсивных в классе всех предикатов рода $\Sigma^1_1$).
The next theorem shows that once the identities (2) are verified for a system
$f_1^*,\dots,f_n^*$ at every $\tilde\alpha$ from $\Sigma^*$, it already follows that
$f_1^*,\dots,f_n^*$ is a solution of (1).

**Theorem 1.4.** A system of recursive functions $f_1^*,\dots,f_n^*$ is a solution
of the G.F.R.E. system (1) if and only if it is a **$\Sigma^*$-quasi-solution**
of (1).

**Theorem 1.5.** The problem of whether a G.F.R.E. has a solution, when its free
variables $\tilde\alpha$ range only over number-theoretic functions, is
**$\Pi^1_1$-complete**.

### 3.2 Chapter 2 — predicates represented by G.F.R.E.

**Definition.** A solution $f_1^*,\dots,f_n^*$ of the system (1) **represents**,
with respect to the function symbol $f_j$, the number-theoretic predicate
$P(\tilde x)$ if the system (1) has a **unique** solution and $f_j^*$ is the
characteristic function of $P(\tilde x)$.

**Theorem 2.6.** When the variables $\tilde\alpha$ in (1) range over the natural
numbers, every **hyperarithmetical** predicate is represented by some system of
recursive equations.

Conversely, the class of hyperarithmetical predicates is the **largest** class of
predicates representable by general form recursive equations.

### 3.3 Chapter 3 — two examples

Two equations illustrating the following possibilities.

**Example 1.** The first equation has an **everywhere defined continuous
solution that is not computable in the sense of Kleene** (see [4], [5], [9]).
However, there is a **Kleene-computable functional that satisfies the equation
whenever the number-theoretic functions $\tilde\alpha$ are general recursive**.
So in some concrete cases one can achieve more by a **specifically
constructivist interpretation of the universal quantifier**.

**Example 2.** An equation whose **unique solution is a functional that is not
Kleene-computable but is recursive** (for a comparison of these notions see [9],
Normann's recursion on the countable functionals).

### 3.4 Bibliography cited in the abstract

1. K. Gödel. On a hitherto unutilized extension of the finitary standpoint. Russian translation in *The Mathematical Theory of Logical Inference*, Moscow: Nauka, 1967, pp. 499–510.
2. S. C. Kleene. *Introduction to Metamathematics*. Van Nostrand, 1952.
3. S. C. Kleene. Recursive functionals and quantifiers of finite types I, *Trans. AMS* 91 (1959), 1–52; II, *Trans. AMS* 108 (1963), 106–142. *(Note: the abstract prints "V 142" for part I; the Trans. AMS volume of part I is 91. Checked from bibliographic memory, not from the journal.)*
4. S. C. Kleene. Countable functionals. In A. Heyting (ed.), *Constructivity in Mathematics*, North-Holland, 1959, pp. 81–100.
5. G. Kreisel. Interpretation of analysis by means of constructive functionals of finite types. Same volume, pp. 101–128.
6. G. Kreisel. Some uses of proof theory for finding computer programs. Colloque International de Logique, Clermont-Ferrand, 1975; CNRS, Paris, 1977, pp. 123–134.
7. H. B. Marandjian. General form recursive equations. *Computer Science Logic*, LNCS 933, Springer, 1995, pp. 501–511.
8. J. Myhill. Finitely representable functions. In *Constructivity in Mathematics*, 1959, pp. 195–207.
9. D. Normann. *Recursion on the Countable Functionals*. LNM 811, Springer, 1980.

### 3.5 The author's publications on the topic

1. A. Aslyan. On a class of number-theoretic predicates represented by means of general form recursive equations. *Mathematical Problems of Cybernetics and Computer Engineering* XVII, Yerevan 1997, pp. 30–34.
2. A. Aslyan. On a representation of hyperarithmetical predicates. Same series, XVIII, Yerevan 1997, pp. 1–13.
3. A. Aslyan. On higher level recursive equations. *Proceedings of CSIT-97*, Yerevan 1997, pp. 3–5.
4. A. Aslyan. On number-theoretic predicates represented by means of general form recursive equations. Deposited in ArmNIINTI, Yerevan 1997, 14 pp., A205-AR97.

### 3.6 Armenian summary (Ամփոփագիր), translated

The dissertation investigates necessary and sufficient conditions for the
existence of solutions of higher-order general form recursive equations. It
also determines the classes of number-theoretic predicates and functions that
can be the unique solution of these equations and can be described uniquely by
means of equations. The algorithmic complexity of the existence problem for
solutions in the class of partial recursive functionals is also considered.

A necessary and sufficient condition for the existence of solutions of
higher-order general form recursive equations is obtained; it is the analogue,
for higher-order equations, of H. B. Marandjian's condition [7].

It is proved that the existence problem for higher-order general form recursive
equations (with free variables for number-theoretic functions only) is
$\Pi^1_1$-complete.

It is shown that for every hyperarithmetical predicate or function there is a
system of general form recursive equations one of whose unique solution's
components is the characteristic function of the given predicate, or the given
function.

---

## 4. Where each result stands

| Result | Statement | Status |
|---|---|---|
| Thm 1.1 | solvability over higher types ⟺ an $i$-fragment substitution turns (1) into identities | stated here only |
| **Def. of quasi-solution** | (2) holds for all $\tilde\alpha \in \mathfrak I$ | stated here only |
| **Thm 1.3** | no solution, but a total recursive $\mathfrak I$-quasi-solution, for $\Pi^1_1$-definable $\mathfrak I$ | stated here only; see question 1 |
| **Thm 1.4** | recursive $f^*$ is a solution ⟺ it is a $\Sigma^*$-quasi-solution | stated here only |
| Thm 1.5 | solvability (type-1 free variables) is $\Pi^1_1$-complete | stated here only |
| Thm 2.6 + maximality | representable predicates = hyperarithmetical | written up: `~/hyperarithmetical-gfre/paper.tex` (with uniformity and the two-symbol normal form); arithmetical case `arithmetical_paper.tex`; forcing-term arithmetic machine-checked in `~/hyperarithmetical-gfre/lean/` |
| Ch. 3, Ex. 1 | continuous non-Kleene-computable solution; Kleene-computable functional satisfying the equation for general recursive $\tilde\alpha$ | stated here only |
| Ch. 3, Ex. 2 | unique solution recursive (Normann) but not Kleene-computable | stated here only |

Nothing from chapters 1 and 3 is formalized anywhere yet.

## 5. Questions the text raises (for the author)

1. **The hypothesis of Theorem 1.3.** As printed, the class $\mathfrak I$ is
   arbitrary $\Pi^1_1$-definable. The class of *all* number-theoretic functions is
   $\Pi^1_1$-definable (trivially), and for it a quasi-solution is a solution, so
   the theorem must carry an extra condition. Theorem 1.4 suggests what it is:
   $\mathfrak I$ must not contain $\Sigma^*$ (otherwise every recursive
   $\mathfrak I$-quasi-solution is a solution). The likely intended class is, for
   example, the recursive or the hyperarithmetical functions ($\mathrm{HYP}$ is
   itself $\Pi^1_1$ as a set of functions). The full dissertation should say;
   the abstract does not.
2. **The meaning of $\Sigma^*$.** "Functions recursive in the class of all
   $\Sigma^1_1$ predicates" can be read as: functions Turing-reducible to some
   $\Sigma^1_1$ set. Under that reading Theorems 1.3 and 1.4 bracket the frontier
   between $\Pi^1_1$-definable test classes and the $\Sigma^1_1$-oracle class.
3. **Example 1 and the constructive quantifier.** The abstract says only that a
   Kleene-computable functional satisfies the equation *when $\tilde\alpha$ is
   general recursive* — a restriction of the domain of $\forall$. It does not
   mention Kreisel–Lacombe–Shoenfield or inspection of indices; the description
   of this example in `RESEARCH_PLAN.md` (pillar 3) adds that mechanism, and it
   should be checked against the full text.
4. **Publication data.** The abstract fixes the two papers as XVII pp. 30–34 and
   XVIII pp. 1–13. That agrees with `~/hyperarithmetical-gfre/README.md`; the
   bibliography entry for the first paper inside `paper.tex` (`18:61–69`) is
   therefore wrong.
