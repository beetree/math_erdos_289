# Statement of faithfulness: Erdős Problem 289

**Version: 4 September 2026. Status: statement audit; formal proof incomplete and uncompiled.**

This statement identifies the mathematical assertion that the Lean project is intended to prove and explains why that assertion would answer Erdős Problem 289 in its nonadjacent formulation. It distinguishes the human task of checking that the formal statement captures the problem from the kernel's task of checking a proof of that statement. It does **not** assert that the current project contains a completed, kernel-checked proof.

The intended problem asks whether, for every sufficiently large integer $k$, there exist exactly $k$ distinct finite intervals of positive integers, each containing at least two integers, which neither overlap nor are adjacent, and whose reciprocals sum to $1$. Here an interval $[a,b]$ includes both endpoints. After ordering the intervals, nonadjacency means

$$
b_i+1<a_{i+1},
$$

so at least one integer is omitted between consecutive intervals. This is the formulation identified in the supplied reviews of the [maintained problem statement](https://www.erdosproblems.com/289) and its [discussion](https://www.erdosproblems.com/forum/thread/289). Those pages could not be fetched during this audit; the same nonadjacent formulation is independently reproduced in [Jig's statement of Problem 289](https://www.jig.so/p/102).

The project's principal target, `Erdos289.CandidateStatement`, strengthens this assertion: there is $k_0\in\mathbb N$ such that, for every $k\ge k_0$, there are intervals $[a_i,b_i]$, indexed by $0\le i<k$, satisfying

$$
1\le a_i,\qquad
b_i-a_i+1\in\{2,3\},\qquad
b_i\le20k,
$$

$$
b_i+1<a_j\quad(i<j),\qquad
\sum_{i=0}^{k-1}\sum_{n=a_i}^{b_i}\frac1n=1.
$$

In particular, the restrictions to lengths $2$ and $3$ and to denominators at most $20k$ are **additional conclusions**, not assumptions about the original problem. Proving this target would give an affirmative answer by retaining the intervals and forgetting these additional restrictions. No equivalence between the original problem and this stronger target is claimed.

The relevant source declarations, inside the `Erdos289` namespace, are:

```lean
structure FamilyWitness (k : ℕ) where
  intervals : Fin k → NatInterval
  positive : ∀ i, 1 ≤ (intervals i).lo
  short : ∀ i, (intervals i).hi = (intervals i).lo + 1 ∨
    (intervals i).hi = (intervals i).lo + 2
  separated : ∀ i j, i < j → (intervals i).Separated (intervals j)
  bounded : ∀ i, (intervals i).hi ≤ 20 * k
  total_mass : ∑ i, (intervals i).mass = 1

def CandidateStatement : Prop :=
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Nonempty (FamilyWitness k)
```

The definitions used here have the following meanings:

| Formal expression | Mathematical meaning |
| --- | --- |
| `NatInterval` | A pair of natural-number endpoints `lo`, `hi`. |
| `I.carrier := Finset.Icc I.lo I.hi` | All integers from the lower endpoint through the upper endpoint, inclusive. |
| `I.Separated J := I.hi + 1 < J.lo` | An omitted integer separates the two ordered intervals. |
| `I.mass := ∑ n ∈ I.carrier, (1 : ℚ) / (n : ℚ)` | The exact rational sum of the reciprocals of the integers in the interval. |
| `Fin k` | The index set $\{0,\ldots,k-1\}$, containing exactly $k$ indices. |
| `Nonempty (FamilyWitness k)` | Existence of interval data satisfying every field of the witness. |

These definitions address the relevant conventions explicitly. The `positive` field excludes denominator zero, so Lean's totalized convention $1/0=0$ cannot be used to satisfy the target. The endpoint equations in `short` give exactly two or three members and avoid any ambiguity from subtraction on natural numbers. Separation and nonemptiness force different indices to represent different intervals; indexing by `Fin k` therefore gives exactly $k$ intervals, rather than merely $k$ labels. They also prevent any denominator from being counted twice. Ordering a finite separated family imposes no restriction, since its intervals can be sorted by their lower endpoints.

The reciprocal equality is exact, with no numerical tolerance or limiting interpretation. Using $\mathbb Q$ is faithful because a finite sum of reciprocals of positive integers equals $1$ in $\mathbb Q$ if and only if its image equals $1$ in $\mathbb R$. The quantifier order requires every $k$ above a single threshold; infinitely many values of $k$ alone would not suffice.

The adjacency issue in Formal Conjectures is substantive. The [file inspected on 4 September 2026](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/289.lean) requires, for distinct indices, the endpoint condition

$$
b_i<a_j\quad\text{or}\quad b_j<a_i.
$$

That condition permits adjacent intervals. For example, $[4,5]$ and $[6,7]$ satisfy it, despite leaving no omitted integer. Our condition excludes this pair, since $5+1<6$ is false, while permitting $[4,5]$ and $[7,8]$. This demonstrates that the older separation predicate is insufficient; it is not an assertion that the truth values of the two complete existential conjectures differ. Consequently, a proof of that Formal Conjectures statement alone would not establish the intended nonadjacent assertion. Merging adjacent intervals changes their number, and splitting an interval into adjacent pieces cannot be used to reach the required count. The present target requires separation between **every** ordered pair of final intervals, regardless of their role in the construction.

The project also defines `Erdos289.Problem289Statement`, which permits any interval length at least two and an arbitrary fixed positive integer $C$ in the bound $b_i\le Ck$. Despite its name, this still includes a linear-bound strengthening of the problem stated above. The source contains a draft implication `candidate_implies_problem289`, obtained by taking $C=20$. This implication assumes `CandidateStatement`; it does not prove that assumption.

For the intended kernel guarantee, the completed artifact must contain an **unconditional theorem of type `Erdos289.CandidateStatement`**, with its definitions agreeing with those audited here. A theorem that assumes the candidate, its construction, or unproved analytic inputs would certify only an implication. Merely defining the proposition, compiling auxiliary lemmas, or obtaining a successful build is insufficient.

The final theorem's complete dependency chain must be checked. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`, corresponding to propositional extensionality, classical choice, and quotient soundness in Lean's usual foundations. No `sorryAx`, conjecture-specific axiom, or additional computational trust axiom may occur. These foundations and the role of kernel checking are described in [Lean's account of axioms](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/) and its [description of the kernel](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#the-kernel).

In particular, the results of Bourgain–Garaev, Conlon and collaborators, and Liu–Sawhney must be supplied through checked Lean proofs, including their dependencies, if they are used. Their publication or citation cannot substitute for those proofs under this guarantee. The current `OpenObligations` declarations only define propositions; they supply no proofs of them.

Once these requirements are met, a reader need not trust the manuscript's analytic arguments, the tactics, or the AI that wrote the proof scripts as independent mathematical authorities: the proof terms and their dependencies supply the justification. The remaining trust is in the correspondence explained here, Lean's logical foundations and checker, and the integrity of the checking environment and identified source artifact. The kernel cannot itself establish that a formal proposition is the problem Erdős intended.

This audit applies to `Erdos289/Intervals.lean` in the starter project, with SHA-256:

```text
178e26470eb61a81f183761d053b697d1800bda64a622dd69858ad065f441871
```

The intended toolchain is Lean 4.19.0 with mathlib v4.19.0. A completed certificate must identify the final source revision, resolved dependency revisions, checked terminal theorem, and its axiom report. Changes to the target or its definitions require this correspondence to be checked again. **At this version, no kernel build or axiom audit has run, and no proof of the principal target is present.** This document records the faithfulness claim and the conditions for a future certificate; it is not that certificate.
