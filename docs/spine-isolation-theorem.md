---
title: "A Spine Isolation Theorem for Magma Implications"
author: Adam McKenna
date: April 2026
abstract: |
  We classify the 4,694 magma equations of the Equational Theories Project by
  spine type, the path from the parse-tree root to the leftmost occurrence
  of the distinguished variable, into pure left-spine, pure right-spine,
  mixed, trivial, and product-LHS families. We prove that a pure left-spine
  equation of depth $n$ cannot imply any equation with an incompatible spine:
  neither right-spine, nor mixed-spine, nor left-spine of depth $m$ where
  $n \nmid m$. Parts (b) and (c) extend the first-letter invariant of
  Corollary 10.4 in the Equational Theories Project blueprint to a systematic spine-type classification. Part (a)
  introduces a new family of separating magmas, cyclic groups with the
  successor operation, yielding a complete divisibility characterization.
  The theorem is validated with zero exceptions on the full 22-million-pair
  Lean-verified implication graph, resolving 1,540,946 ordered pairs. The
  core separation arguments are formally verified in Lean 4, with no
  Mathlib dependency.
header-includes:
  - \usepackage{booktabs}
  - \usepackage{amssymb}
  - \usepackage{amsthm}
  - \newtheorem{theorem}{Theorem}
  - \newtheorem{corollary}{Corollary}
  - \newtheorem{definition}{Definition}
  - \newtheorem{remark}{Remark}
---

# Introduction

The Equational Theories Project (ETP) of Tao et al. \cite{tao2025etp}
catalogues 4,694 magma equations and determines, via Lean-verified proofs, the
complete implication graph among them: 22,033,636 ordered pairs, each labelled
TRUE (implication holds in every magma) or FALSE. The resulting structure
(1,415 equivalence classes connected by 4,824 edges in the transitive
reduction) is rich enough to motivate a search for systematic separation
principles.

One such principle appears in the ETP blueprint \cite{tao2025blueprint},
Chapter 10 ("Some abstract nonsense"). Corollary 10.4 defines the *first
letter of $w$* invariant: for
any magma word $w$, the leftmost leaf of the term tree is preserved by the
left-zero magma $M = (S, \cdot)$ where $a \cdot b = a$ for all $a, b \in S$.
If two equations $E_1$ and $E_2$ differ on this invariant (that is, if the
leftmost leaf of the right-hand side of $E_1$ is the left-hand-side variable
$x$, while the leftmost leaf of $E_2$ is not) then the left-zero magma
satisfies $E_1$ but not $E_2$, proving $E_1 \not\Rightarrow E_2$.

This paper extends the first-letter invariant in two directions.
First, we introduce a spine-type classification that
partitions the equations into pure left-spine, pure right-spine, and
mixed-spine families (plus trivial and product-LHS families outside the
theorem's scope). Parts (b) and (c) of our main theorem show that the
left-zero magma separates not only by the identity of the leftmost leaf but by
the entire spine type: pure left-spine equations cannot imply pure right-spine
or mixed-spine equations.
Second, Part (a) introduces a new family of separating magmas (the cyclic
groups $\mathbb{Z}/n\mathbb{Z}$ equipped with the successor operation
$a \cdot b = a + 1 \pmod{n}$) that stratifies equations within each spine
type by depth, yielding the complete divisibility characterization:
depth $n$ implies depth $m$ only if $n \mid m$.

The theorem applies when $E_1$ has a pure left-spine (or, by a mirror
construction, a pure right-spine) and $E_2$ has a bare variable as its
left-hand side. It does not apply when $E_2$ belongs to Family C, where the
left-hand side is itself a product.

# Definitions and Classification

\begin{definition}[Spine]
Let $E$ be a magma equation of the form $x = t$, where $t$ is a magma term
over the variable set containing $x$. The \emph{spine} of $E$ is the sequence
of directions $d_1 d_2 \cdots d_k \in \{L, R\}^*$ obtained by recording, at
each binary operator node from the root of $t$ to the leftmost occurrence of
$x$, whether $x$ lies in the left ($L$) or right ($R$) subtree.
\end{definition}

\begin{definition}[Pure left-spine of depth $n$]
An equation $x = t$ has a \emph{pure left-spine of depth $n$} if the spine
is $L^n$: the leftmost occurrence of $x$ in $t$ is reached by taking the left
child at every node from the root, traversing exactly $n$ operator nodes.
Equivalently, the right-hand side has the form
$(\cdots((x \cdot T_1) \cdot T_2) \cdots T_n)$
where $T_1, \ldots, T_n$ are arbitrary magma terms.
\end{definition}

\begin{definition}[Pure right-spine; mixed spine]
An equation has a \emph{pure right-spine of depth $n$} if the spine is $R^n$.
An equation has a \emph{mixed spine} if the spine contains both $L$ and $R$
steps.
\end{definition}

We classify the 4,694 equations of the ETP catalog \cite{tao2025etp}
(reproduced in the accompanying repository \cite{mckenna2026lean}) by
spine type. The
distribution is as follows.

| Spine type | Count | Depth 1 | Depth 2 | Depth 3 | Depth 4 |
|:-----------|------:|--------:|--------:|--------:|--------:|
| Pure left  |   815 |     297 |     295 |     171 |      52 |
| Pure right |   240 |      88 |      87 |      50 |      15 |
| Mixed      | 1,267 |     --- |     --- |     --- |     --- |
| Trivial    |   817 |     --- |     --- |     --- |     --- |
| Family C   | 1,555 |     --- |     --- |     --- |     --- |

The pure left-spine and pure right-spine families admit a natural
depth grading. The remaining 3,639 equations (mixed, trivial, and
Family C) fall outside the scope of the present theorem.

# Main Result

\begin{theorem}[Spine Isolation]
\label{thm:lsi}
Let $E_1$ be a magma equation of the form
$x = (\cdots((x \cdot T_1) \cdot T_2) \cdots T_n)$, so that the leftmost
leaf of the right-hand side is $x$, reached by taking the left child at every
node from the root, a pure left-spine of depth $n \geq 1$. The variable $x$ may
appear elsewhere in the right-hand side. Let $E_2$ be any magma equation whose
left-hand side is a bare variable. All separating magma arguments below
require $|S| \geq 2$. Then:

\begin{itemize}
\item[(a)] If $E_2$ has a pure left-spine of depth $m$ where $n \nmid m$,
  then $E_1$ does not imply $E_2$.
\item[(b)] If $E_2$ has a pure right-spine, then $E_1$ does not imply $E_2$.
\item[(c)] If $E_2$ has a mixed spine, then $E_1$ does not imply $E_2$.
\end{itemize}
\end{theorem}

\begin{corollary}[Right-Spine Isolation]
\label{cor:rsi}
Let $E_1$ have a pure right-spine of depth $n$, and let $E_2$ have a pure
right-spine of depth $m$ with $n \nmid m$. Then $E_1$ does not imply $E_2$.
\end{corollary}

\begin{remark}
The divisibility condition $n \mid m$ is necessary but not sufficient for
implication between same-spine equations. On the ETP catalog, the fraction
of TRUE implications among divisible left-spine depth pairs ranges from
$24\%$ to $39\%$, confirming a substantial gap between the necessary
condition and sufficiency.
\end{remark}

# Proofs

## Proof of Parts (b) and (c)

\begin{proof}
We construct a separating magma that satisfies every pure left-spine equation
but fails every pure right-spine and every mixed-spine equation.

Let $S$ be any set with $|S| \geq 2$, and define the \emph{left-zero magma}
$M = (S, \cdot)$ by $a \cdot b = a$ for all $a, b \in S$.

\textbf{$M$ satisfies every pure left-spine equation.}
Let $E_1$ be a pure left-spine equation of depth $n$:
$x = (\cdots((x \cdot T_1) \cdot T_2) \cdots T_n)$.
We show by induction on depth that the right-hand side evaluates to $x$ under
every assignment in $M$.

\emph{Base case} ($n = 1$): The right-hand side is $x \cdot T_1$.
In $M$, $x \cdot T_1 = x$.

\emph{Inductive step}: Suppose the claim holds for depth $n - 1$.
The right-hand side of a depth-$n$ equation is
$(\cdots((x \cdot T_1) \cdots T_{n-1}) \cdot T_n)$.
By the inductive hypothesis, the inner expression
$(\cdots((x \cdot T_1) \cdots T_{n-1}))$ evaluates to $x$.
Then $x \cdot T_n = x$ in $M$, completing the induction.

\textbf{$M$ fails every pure right-spine equation.}
Let $E_2$ be a pure right-spine equation of depth $k$:
$x = (T_1 \cdot (T_2 \cdot \ldots (T_k \cdot x) \ldots))$.
In $M$, the outermost operation evaluates to
$T_1 \cdot (\text{anything}) = v(T_1)$,
the value of $T_1$ under the given assignment $v$.
Since $E_2$ has a pure right-spine, the leftmost leaf of the right-hand side
is the leftmost leaf of $T_1$, which is not $x$ (the leftmost leaf is $x$
only for left-spine equations). In $M$, every term evaluates to its leftmost
leaf, so $v(T_1)$ equals the leftmost leaf of $T_1$.
Choose an assignment sending this leaf to some $a \in S$ with $a \neq x$
(possible since $|S| \geq 2$). Then the right-hand side evaluates to
$a \neq x$, so $E_2$ fails in $M$.

\textbf{$M$ fails every mixed-spine equation.}
Let $E_2$ have a mixed spine. Following the spine from the root, at some node
we take the right child for the first time. At that node the left-zero
operation discards the right subtree (which contains the leftmost occurrence
of $x$) and retains the left subtree, which does not contain $x$ along the
spine path. The right-hand side therefore evaluates to a term whose value is
independent of $x$ (it equals the leftmost leaf of the left subtree at that
node). Choosing an assignment where this value differs from $x$ gives a
counterexample.

Since $M$ satisfies $E_1$ but fails $E_2$ in all cases, $E_1$ does not
imply $E_2$.
\end{proof}

## Proof of Part (a)

\begin{proof}
We construct, for each depth $n$, a magma that satisfies every pure
left-spine equation of depth $n$ but fails every pure left-spine equation of
depth $m$ whenever $n \nmid m$.

Define the \emph{cyclic magma} $M_n = (\mathbb{Z}/n\mathbb{Z}, \cdot)$ by
$a \cdot b = a + 1 \pmod{n}$.

\textbf{$k$-fold left-composition equals $a + k \pmod{n}$.}
We verify by induction. For $k = 1$: $a \cdot T_1 = a + 1$.
Assuming the $(k-1)$-fold left-composition equals $a + (k-1)$, the $k$-fold
composition is $(a + (k-1)) \cdot T_k = (a + (k-1)) + 1 = a + k \pmod{n}$.
Note that the right operand $T_k$ does not affect the result: $M_n$ discards
the right operand in the same way as the left-zero magma, except that it
increments the left operand by one.

\textbf{Depth-$n$ equations hold in $M_n$.}
A pure left-spine equation of depth $n$ evaluates to
$x + n \equiv x \pmod{n}$. Hence $M_n \models E_1$.

\textbf{Depth-$m$ equations fail in $M_n$ when $n \nmid m$.}
A pure left-spine equation of depth $m$ evaluates to $x + m \pmod{n}$.
When $n \nmid m$, we have $x + m \not\equiv x \pmod{n}$, so the equation
fails for every $x \in \mathbb{Z}/n\mathbb{Z}$.

Since $M_n$ satisfies $E_1$ (depth $n$) but not $E_2$ (depth $m$, $n \nmid
m$), the implication $E_1 \Rightarrow E_2$ fails.
\end{proof}

## Proof of the Right-Spine Corollary

\begin{proof}
Given a magma $(S, \cdot)$, define the \emph{opposite magma}
$M^{\mathrm{op}} = (S, \cdot')$ by $a \cdot' b = b \cdot a$.
A pure right-spine equation of depth $n$ under $\cdot$ becomes a pure
left-spine equation of depth $n$ under $\cdot'$: the sequence of $R$-steps
in the original parse tree becomes a sequence of $L$-steps when left and
right operands are exchanged at every node.

Apply Theorem \ref{thm:lsi}(a) to $M^{\mathrm{op}}$: if $E_1$ has a pure
left-spine of depth $n$ under $\cdot'$ (equivalently, a pure right-spine of
depth $n$ under $\cdot$) and $E_2$ has a pure left-spine of depth $m$ under
$\cdot'$ (a pure right-spine of depth $m$ under $\cdot$) with $n \nmid m$,
then $E_1$ does not imply $E_2$ in $M^{\mathrm{op}}$. Since
$M^{\mathrm{op}}$ is a magma, this witnesses $E_1 \not\Rightarrow E_2$.
\end{proof}

# Empirical Validation

We validated the theorem on the complete ETP implication graph: 4,694
equations, 22,033,636 ordered pairs, each resolved by Lean-verified proof.
The spine classification was computed by a C parser operating on the equation
parse trees. All parts of the theorem produce zero violations.

## Part (a): Non-divisible left-spine depths

Table 1 shows all eight non-divisible depth pairs among pure left-spine
equations. Every pair yields zero TRUE implications, confirming Part (a).

**Table 1.** Non-divisible left-spine depth pairs ($n \nmid m$). All
implications are FALSE.

| Source depth | Target depth | $n \nmid m$ | Pairs   | TRUE |
|:-------------|:-------------|:------------|--------:|-----:|
| 2            | 1            | $2 \nmid 1$ | 87,615  |    0 |
| 2            | 3            | $2 \nmid 3$ | 50,445  |    0 |
| 3            | 1            | $3 \nmid 1$ | 50,787  |    0 |
| 3            | 2            | $3 \nmid 2$ | 50,445  |    0 |
| 3            | 4            | $3 \nmid 4$ |  8,892  |    0 |
| 4            | 1            | $4 \nmid 1$ | 15,444  |    0 |
| 4            | 2            | $4 \nmid 2$ | 15,340  |    0 |
| 4            | 3            | $4 \nmid 3$ |  8,892  |    0 |

Table 2 shows the divisible depth pairs, where implication is permitted by
the theorem. The nonzero TRUE rates (24--39\%) confirm that the divisibility
condition is tight: replacing $n \nmid m$ with a weaker condition would
introduce false negatives.

**Table 2.** Divisible left-spine depth pairs ($n \mid m$). Implication is
possible; the theorem does not apply.

| Source depth | Target depth | $n \mid m$ | TRUE    | FALSE   | Rate   |
|:-------------|:-------------|:-----------|--------:|--------:|-------:|
| 1            | 2            | $1 \mid 2$ | 21,966  | 65,649  | 25.1\% |
| 1            | 3            | $1 \mid 3$ | 12,355  | 38,432  | 24.3\% |
| 1            | 4            | $1 \mid 4$ |  3,726  | 11,718  | 24.1\% |
| 2            | 4            | $2 \mid 4$ |  6,021  |  9,319  | 39.3\% |

## Parts (b) and (c): Cross-spine isolation

Every pure left-spine $\to$ pure right-spine pair and every pure left-spine
$\to$ mixed-spine pair yields zero TRUE implications across approximately
1,228,000 ordered pairs.

**Table 3.** Cross-spine pairs from pure left-spine sources.

| Source type  | Target type  | Pairs (approx.) | TRUE |
|:-------------|:-------------|:----------------|-----:|
| Pure left    | Pure right   | 195,600          |    0 |
| Pure left    | Mixed        | 1,032,605        |    0 |

## Right-spine corollary

Table 4 confirms the right-spine analogue. All eight non-divisible
right-spine depth pairs yield zero TRUE implications.

**Table 4.** Non-divisible right-spine depth pairs ($n \nmid m$). All
implications are FALSE.

| Source depth | Target depth | $n \nmid m$ | Pairs | TRUE |
|:-------------|:-------------|:------------|------:|-----:|
| 2            | 1            | $2 \nmid 1$ | 7,656 |    0 |
| 2            | 3            | $2 \nmid 3$ | 4,350 |    0 |
| 3            | 1            | $3 \nmid 1$ | 4,400 |    0 |
| 3            | 2            | $3 \nmid 2$ | 4,350 |    0 |
| 3            | 4            | $3 \nmid 4$ |   750 |    0 |
| 4            | 1            | $4 \nmid 1$ | 1,320 |    0 |
| 4            | 2            | $4 \nmid 2$ | 1,305 |    0 |
| 4            | 3            | $4 \nmid 3$ |   750 |    0 |

We note an asymmetry in the catalog: pure right-spine $\to$ pure left-spine
implications are 14--17\% TRUE, not universally FALSE. This is because the
4,694-equation catalog is not closed under mirroring: 554 of the 4,694
equations (predominantly Family C, with product left-hand sides) have no
mirror image in the catalog. The cross-spine isolation
(Parts (b) and (c)) is a statement about left-spine sources; it does not
assert the converse. Within any mirror-closed subset of equations, full
left-right symmetry would hold.

In total, the theorem resolves **1,540,946 ordered pairs** with zero
violations.

# Formal Verification

The core separation arguments of all three parts of Theorem \ref{thm:lsi}
are formally verified in Lean 4 (v4.29.0) with no Mathlib dependency
\cite{mckenna2026lean}. The formalization comprises three modules totalling
approximately 300 lines.

**Definitions** (`SpineIsolation/Defs.lean`). An inductive type `MagmaTerm`
represents magma terms over natural-number variables, with constructors `var`
and `op`. The predicates `IsLeftSpine x n t` and `IsRightSpine x n t` are
defined inductively, capturing the spine classification of Section 2. A
structure `MagmaEq` pairs a left-hand-side variable with a right-hand-side
term; `MagmaEq.holds` quantifies universally over assignments and carriers,
while `MagmaEq.notImplies` witnesses separation existentially.

**Parts (b) and (c)** (`SpineIsolation/LeftZero.lean`). The key lemma
`leftZero_eval_eq_leftmostVar` establishes that in the left-zero magma,
evaluating any term yields the assignment at its leftmost leaf variable. The
proof proceeds by structural induction on `MagmaTerm`. The main theorem
`leftSpine_notImplies_nonLeftSpine` constructs the separating witness on
`Bool`: assigning `true` to the left-hand-side variable and `false` to all
others.

**Part (a)** (`SpineIsolation/Cyclic.lean`). The lemma `cyclic_eval` proves
that in the cyclic magma on `Fin n`, evaluating a term $t$ under assignment
$f$ yields $f(\text{leftmostVar}(t)) + \text{leftSpineDepth}(t) \pmod{n}$.
The main theorem `leftSpine_depth_notImplies` combines this with the witness
$f = \lambda\_.\ 0$ to separate depth $n$ from depth $m$ when $n \nmid m$.

The formalization is self-contained: no external libraries beyond Lean's core
are required. All proofs are constructive, producing explicit separating
magmas rather than asserting their existence.

# Discussion

The divisibility characterization of Part (a) is sharp in one direction:
$n \mid m$ is necessary for $E_1 \Rightarrow E_2$ when both equations are
pure left-spine. The gap between necessary and sufficient is substantial:
even when $n \mid m$, only 24--39\% of pairs in the catalog are TRUE. Closing
this gap, perhaps by enriching the separating magma family, is an open
problem.

The left-right asymmetry observed in the empirical data is a catalog
artifact, not an algebraic phenomenon. The ETP catalog enumerates equations
by a left-to-right tree-structure convention, producing 554 equations
(predominantly Family C) with no mirror image in the catalog. Within any mirror-closed extension, the
right-spine analogue of Parts (b) and (c) would hold with identical force.

More broadly, the results illustrate a methodology: structural features of
equation parse trees (here, the spine path) can serve as algebraic
separation witnesses when paired with appropriately chosen magma families.
The left-zero magma and the cyclic successor magmas
$(\mathbb{Z}/n\mathbb{Z}, a \cdot b = a + 1)$ are elementary objects. The
contribution is not the magmas themselves but the systematic classification
of which equations they separate.

\begin{thebibliography}{1}

\bibitem{tao2025etp}
T.~Tao et al.,
``The Equational Theories Project: Advancing Collaborative Mathematical
Research at Scale,''
\emph{arXiv:2512.07087}, 2025.

\bibitem{tao2025blueprint}
T.~Tao et al.,
``Equational Theories Project Blueprint,''
\url{https://teorth.github.io/equational_theories/blueprint/}, 2025.
Chapter 10, ``Some abstract nonsense,'' Corollary 10.4.

\bibitem{mckenna2026lean}
A.~McKenna,
``Spine Isolation Theorem: Lean 4 Formalization,''
\url{https://github.com/mysticflounder/equational-magma-theorems}, 2026.

\end{thebibliography}
