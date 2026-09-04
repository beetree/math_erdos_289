# Erdős Problem 289: Lean 4 formalization

This repository formalizes, in Lean 4 with Mathlib, the candidate proof in
`erdos_289_full_proof.pdf` (revised nonadjacent version, 4 September 2026) of a
strengthened form of Erdős Problem 289.

**Status: conditional certificate achieved.** The terminal theorem builds with no `sorry`,
and its axiom report is exactly the three standard axioms plus the six audited literature
axioms. The unconditional certificate (no literature axioms) is not achieved. See "Current
status" below.

## How to read this repository

The trust chain has exactly two links.

1. **The statement of faithfulness** (reproduced verbatim in the next section). It is
   the human-checked claim that the formal proposition `Erdos289.CandidateStatement`,
   as declared in the audited file `Erdos289/Intervals.lean`, is a faithful strengthening
   of the nonadjacent formulation of Erdős Problem 289. This is the one thing a reader
   must examine and believe; no machine can check it.
2. **The Lean kernel.** Once the terminal theorem `Erdos289.CandidateStatement` is proved
   and `#print axioms` on it reports only `propext`, `Classical.choice`, and `Quot.sound`,
   nothing else needs to be trusted: not the manuscript, not the tactics, not the AI
   that wrote the proof scripts, and not any cited paper.

The audited file is included unchanged. Its SHA-256 is the one recorded in the
statement of faithfulness:

```text
178e26470eb61a81f183761d053b697d1800bda64a622dd69858ad065f441871  Erdos289/Intervals.lean
```

It compiles as is on the pinned toolchain (Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2`).
Do not edit it. Any change to it invalidates the audit.

## Statement of faithfulness

The following is the statement supplied by the author of the proof, reproduced verbatim
as supplied by the author (the source file is kept outside the repository). (Its remarks about the
toolchain and about the uncompiled starter refer to the author's original starter
project, whose `Intervals.lean` is the audited file used here. The toolchain named there,
Lean 4.19, is out of date: this repository pins Lean and Mathlib `v4.34.0-rc2`, on which the
audited file compiles unchanged.)

---

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

---

## Statement of faithfulness for the six external axioms

The six literature inputs are declared as axioms in the author's audited module, included
unchanged as `Erdos289/ExternalAxioms.lean` with SHA-256

```text
6a4affa2cecb731c87ec21433305842bd3c0c92bc7c62a8ca86f410f3647c5d7  Erdos289/ExternalAxioms.lean
```

The document below, supplied by the author, is reproduced verbatim. It gives, for each
axiom, the exact Lean proposition and a human-readable argument that the cited published
theorem implies it. These six correspondences are the second and last human-checked link in
the trust chain: a reader who accepts the target audit above and these six statements need
trust nothing else but the kernel.

Note on the toolchain: the document names Lean 4.19 / Mathlib 4.19 as its baseline. That is
out of date. This repository pins Lean `v4.34.0-rc2` and Mathlib `v4.34.0-rc2`, and the
audited module compiles unchanged on that toolchain.

---

# Six external axioms for Erdős Problem 289: formal statements and faithfulness

**Version: 4 September 2026. Status: proposed Lean specifications and human-readable faithfulness statements; uncompiled and externally assumed.**

The companion `Erdos289ExternalAxioms.lean` is a standalone module importing mathlib. It defines six propositions and declares exactly six corresponding axioms under `Erdos289.External.Assumed`. It also defines an `ExternalInputs` record for a future proof with explicit hypotheses. There is no proof of Erdős Problem 289 in this module.

Each faithfulness statement below makes the same claim: the identified published mathematical result, with the specialization explained here, implies the exact displayed Lean proposition. These are statements for human review, not Lean proofs of that correspondence or of the external results. While the axioms remain, any completed proof using them is conditional on their truth. Lean checks deductions from assumptions; it does not validate the assumptions themselves.

All snippets use the namespace `Erdos289.External` and `open scoped BigOperators`. Definitions of every project-specific helper are reproduced in Appendix A. Natural numbers include zero, so positivity is explicitly imposed wherever zero would be inappropriate. Every logarithm is natural except `logTwo`, used only in the GAP input. Every nonintegral power, density comparison, norm, and discrepancy subtraction is taken in the indicated real or complex type.

The intended baseline is Lean 4.19.0 with mathlib v4.19.0. Lean and Lake are absent from the authoring environment, so these files have not been elaborated or kernel-checked. Source inspection is not a substitute for the first compiler run.

## 1. `liu_sawhney`

**Source.** Yang P. Liu and Mehtaab Sawhney, *On further questions regarding unit fractions*, [arXiv:2404.07113v1, Theorem 1.3](https://arxiv.org/html/2404.07113v1).

**Exact proposition.**

```lean
def LiuSawhneyStatement : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < (1 : ℝ) / 2 →
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
          (1 - Real.exp (-1) + ζ) * (N : ℝ) ≤ (A.card : ℝ) →
          ∃ D : Finset ℕ, D ⊆ A ∧ rationalMass D = 1
```


**Assumption declaration**, inside `Erdos289.External.Assumed`:

```lean
axiom liu_sawhney : LiuSawhneyStatement
```

**Faithfulness statement 1.** `LiuSawhneyStatement` is a specialization of the cited theorem to finite sets represented by `Finset ℕ`. `Finset.Icc 1 N` includes both endpoints and excludes zero. Its cardinality is cast to the reals for the density comparison; `Real.exp (-1)` denotes $1/e$. The threshold `N₀` is chosen after $\zeta$ and before both $N$ and $A$, preserving the required uniformity over all eligible sets. Requiring `N₀ ≥ 1` is harmless because any threshold can be increased.

The conclusion uses a subset, so denominators are distinct. `rationalMass D = 1` expresses exact equality in $\mathbb Q$, equivalent to the usual equality for a finite sum of positive integer reciprocals. No interval-location or deletion-stability hypothesis has been added to the conclusion; applications to the protected bands must be proved separately.

This input is Liu–Sawhney's finite density-threshold theorem. Porting the [Bloom–Mehta positive-density formalization](https://github.com/b-mehta/unit-fractions) would provide useful infrastructure but would not, by itself, discharge this stronger finite assertion.

## 2. `cfhmpsv_structure`

**Precise source and conventions.** Conlon–Fox–Pham, *Homogeneous structures in subset sums and non-averaging sets*, [arXiv:2311.01416v1](https://arxiv.org/pdf/2311.01416v1), Theorem 1.5 (printed p. 3), logarithm convention (p. 5), Definition 2.5 (p. 7), and the supplied representation in the proof (pp. 26–27). The result is restated as Theorem 3 in Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte, [arXiv:2404.16016v2](https://arxiv.org/html/2404.16016v2). The name `cfhmpsv_structure` is retained, but CFP supplies the precise coordinate-dilation convention used here.

**Exact proposition.**

```lean
def CFHMPSVStructureStatement : Prop :=
  ∀ β η : ℝ, 1 < β → 0 < η → η < 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ m₀ : ℕ, 2 ≤ m₀ ∧
      ∀ (m n s : ℕ) (A : Finset ℤ),
        m₀ ≤ m →
        A ⊆ Finset.Icc (1 : ℤ) (n : ℤ) →
        A.card = m →
        (n : ℝ) ≤ (m : ℝ) ^ β →
        (m : ℝ) ^ η ≤ (s : ℝ) →
        (s : ℝ) ≤ c * (m : ℝ) / logTwo (m : ℝ) →
        ∃ (J : Finset ℤ) (P : GAPRepresentation) (J' : Finset ℤ),
          J ⊆ A ∧
          (m : ℝ) - (s : ℝ) * logTwo (m : ℝ) / c ≤ (J.card : ℝ) ∧
          P.rank ≤ d₀ ∧
          P.properAt 1 ∧
          ((J : Set ℤ) ∪ {0}) ⊆ P.carrierAt 1 ∧
          J' ⊆ J ∧ J'.card ≤ s ∧
          P.properAt (c * (s : ℝ)) ∧
          ∃ z : ℤ, ∀ x ∈ P.carrierAt (c * (s : ℝ)),
            z + x ∈ integerSubsetSums J'
```


**Assumption declaration**, inside `Erdos289.External.Assumed`:

```lean
axiom cfhmpsv_structure : CFHMPSVStructureStatement
```

**Faithfulness statement 2.** This proposition records the source's bounded-rank structure conclusion using finite sets of integers. The constants `c`, `d₀`, and `m₀` depend only on $\beta,\eta$. Restricting to natural-number $s$ and sufficiently large $m\ge2$ weakens the source's assertion. `integerSubsetSums J'` permits each element at most once and includes the empty sum. Requesting an arbitrary integer translate drops the source's additional homogeneity condition on that translate, another weakening.

The data type also allows rank zero and non-strict coordinate bounds. These are harmless relaxations of the source's representation requirements. The GAP is represented by its actual generators and real coordinate bounds:

$$
P_t=\left\{\sum_i z_i d_i:\ z_i\in\mathbb Z,\quad
t\alpha_i\le z_i\le t\beta_i\right\}.
$$

The same data define $P_1$ and $P_{cs}$. Properness means that their coordinate maps are injective, with nonemptiness explicitly required. No symmetric representation or subsequent recentering is assumed. For the nonempty dilate, the source proof supplies a centered intermediate $Q$, rescales it by $h^{-1}$, and finishes with $P=\phi^{-1}(Q)$ using a centered parent's identification map. Retaining those coordinates gives a zero coordinate vector in each positive dilate. This is a proof-level justification of the nonemptiness clause, not an inference that arbitrary representations containing zero have that property.

`logTwo m = Real.log m / Real.log 2` preserves CFP's explicit base-two convention. This is an intentional precision beyond the earlier shorthand “$\log m$”. Callers written with natural logarithms must account for the factor $\log 2$ in their elementary estimates; the axiom does not silently alter `c` or the supplied dilate. Coordinate dilation is used at **every** positive real scale. No identity with an iterated sumset is assumed for arbitrary real coordinate bounds. Integer trimming, taking faces, volume estimates, and the sparse inverse-covering extension remain downstream proof obligations.

## 3. `bourgain_garaev`

**Source.** Jean Bourgain and Moubariz Z. Garaev, *Kloosterman sums in residue rings*, [arXiv:1309.1124v1, Theorem 5](https://arxiv.org/pdf/1309.1124v1), printed pp. 3–4.

**Exact proposition.**

```lean
def BourgainGaraevStatement : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ c : ℝ, 0 < c → c < c₀ →
      ∀ ε : ℝ, 0 < ε →
        ∃ m₀ : ℕ, 2 ≤ m₀ ∧
          ∀ m : ℕ, m₀ ≤ m →
            ∀ N : ℕ, (m : ℝ) ^ c < (N : ℝ) → N < m →
              ∀ a : ZMod m, IsUnit a →
                ‖inversePrefix m N a‖ ≤ ε * (N : ℝ)
```


**Assumption declaration**, inside `Erdos289.External.Assumed`:

```lean
axiom bourgain_garaev : BourgainGaraevStatement
```

**Faithfulness statement 3.** This is the uniform $o(N)$ consequence of the source's quantitative estimate, restricted to sufficiently small fixed positive exponents. The source permits constants depending on $c$ only and bounds the normalized sum by a fixed power of $\log\log m$ divided by $\sqrt{\log m}$, which tends to zero. For each $c$ and tolerance $\varepsilon$, one therefore chooses a single `m₀` before all later moduli, cutoffs, and coefficients. Requiring `m₀ ≥ 2` merely excludes irrelevant small moduli.

`inversePrefix m N a` sums exactly over $1\le n\le N$ with $\gcd(n,m)=1$. Both multiplication and inversion occur in `ZMod m`; `expPhase` is the additive character $z\mapsto\exp(2\pi i\,\operatorname{val}(z)/m)$. `IsUnit a` is the residue-ring form of the coprimality condition on the coefficient. Consequently the norm is the source's complex absolute value. General composite moduli remain allowed.

No estimates for nonunit coefficients, interval differences, or growing Fourier cutoffs are directly assumed. The reductions needed for those applications must be proved from this input.

## 4. `erdos_turan`

**Source.** The classical Erdős–Turán discrepancy inequality for points on the unit circle. The supplied bibliographic reference is Hugh L. Montgomery, *Ten Lectures on the Interface Between Analytic Number Theory and Harmonic Analysis*, AMS CBMS 84 (1994), Chapter 1, “Uniform Distribution”. The [book's bibliographic record and chapter listing](https://books.google.com/books/about/Ten_Lectures_on_the_Interface_Between_An.html?id=9x8IamaDb4MC) were checked; the proposed precise locator “Corollary 1.1” was not independently verified. The specialization below explicitly identifies the standard inequality being invoked, so that source-locator check can be completed without guessing the intended statement.

**Exact proposition.**

```lean
def ErdosTuranStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ U : ℕ, 1 ≤ U →
      ∀ N : ℕ, ∀ x : Fin N → ZMod U,
        ∀ H : ℕ, 1 ≤ H →
          ∀ α ℓ : ℕ, α + ℓ ≤ U →
            |(residueIntervalCount x α ℓ : ℝ) -
                (N : ℝ) * (ℓ : ℝ) / (U : ℝ)| ≤
              C * ((N : ℝ) / (H : ℝ) +
                (∑ h ∈ Finset.Icc 1 H,
                  (1 : ℝ) / (h : ℝ) * ‖fourierSum x h‖))
```


**Assumption declaration**, inside `Erdos289.External.Assumed`:

```lean
axiom erdos_turan : ErdosTuranStatement
```

**Faithfulness statement 4.** Apply the usual unnormalized discrepancy bound

$$
\left|\#\{j:y_j\in[a,b)\}-N(b-a)\right|
\le C\left(\frac{N}{H+1}
+\sum_{h=1}^{H}\frac1h\left|\sum_j e^{2\pi i h y_j}\right|\right)
$$

to $y_j=\operatorname{val}(x_j)/U$, $a=\alpha/U$, and $b=(\alpha+\ell)/U$. The hypotheses `U ≥ 1` and `α + ℓ ≤ U`, with natural endpoints, place this interval inside $[0,1]$. The counts agree exactly, including multiplicities and half-open endpoints. Character periodicity identifies the complex sums with `fourierSum x h`. Finally, $N/(H+1)\le N/H$ for $H\ge1$, giving the stated weakening. Any fixed differences in the conventional absolute constants can be absorbed into `C`.

The quantifiers require one constant independent of every modulus, sequence, cutoff, and interval. No condition $H<U$ is imposed or needed. Every division and subtraction is in $\mathbb R$, and the sum excludes frequency zero. The case $N=0$ has both sides zero. Thus the declared proposition is the specified standard discrepancy theorem's discrete specialization; confirmation of the exact Montgomery corollary number remains a bibliographic task, not a claim already verified here.

## 5. `mertens_second`

**Source.** Mertens' second theorem, in its convergent form. An accessible proof source is Terence Tao, [*Mertens' theorems* (11 December 2013)](https://terrytao.wordpress.com/2013/12/11/mertens-theorems/), Theorem 1, equation (3), together with the convergent correction explained below. That source's equation (2) alone states only an $O(1)$ error and would not suffice for this axiom.

**Exact proposition.**

```lean
def MertensSecondStatement : Prop :=
  ∃ B₁ : ℝ,
    Filter.Tendsto
      (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      Filter.atTop (nhds B₁)
```


**Assumption declaration**, inside `Erdos289.External.Assumed`:

```lean
axiom mertens_second : MertensSecondStatement
```

**Faithfulness statement 5.** `primeReciprocalSum x` includes exactly the primes $p\le x$ for $x\ge0$, since it filters the natural numbers through $\lfloor x\rfloor$. `Filter.atTop` is the limit $x\to+\infty$, and `nhds B₁` expresses convergence to one finite real constant. Both logarithms are natural. Behavior at nonpositive $x$ has no effect on this limit.

For a direct deduction from the cited source, put

$$
r_p=\log(1-1/p)+1/p.
$$

The estimate $r_p=O(p^{-2})$ implies $\sum_{p\le x}r_p\to R$. The source proves

$$
\sum_{p\le x}\log(1-1/p)=-\log\log x-\gamma+o(1).
$$

Subtracting gives $\sum_{p\le x}1/p-\log\log x\to R+\gamma$, so choosing $B_1=R+\gamma$ proves the declared proposition. No numerical value for $B_1$ is required. Subtraction at two varying cutoffs, including real powers, remains a downstream limit argument.

## 6. `divisor_bound`

**Source.** G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, [Theorem 315, §18.1](https://ia802804.us.archive.org/33/items/hardy-wright-theory_of_numbers/hardy-wright-theory_of_numbers.pdf#page=276), printed p. 260 in the linked scan. The source states $d(n)=O(n^\delta)$ for every $\delta>0$ and discusses the equivalent little-$o$ formulation.

**Exact proposition.**

```lean
def DivisorBoundStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → (divisorCount n : ℝ) ≤ (n : ℝ) ^ ε
```


**Assumption declaration**, inside `Erdos289.External.Assumed`:

```lean
axiom divisor_bound : DivisorBoundStatement
```

**Faithfulness statement 6.** For $n>0$, `divisorCount n` is exactly the number $d(n)=\tau(n)$ of positive divisors, including $1$ and $n$. The threshold is at least $1$, excluding mathlib's separate convention for divisors of zero. The exponent and comparison are real-valued, and the threshold depends only on $\varepsilon$.

To obtain coefficient $1$ from Theorem 315, apply it with exponent $\varepsilon/2$: for some fixed $C$ and all sufficiently large $n$,

$$
\tau(n)\le Cn^{\varepsilon/2}\le n^\varepsilon,
$$

where the second inequality holds after increasing the threshold until $n^{\varepsilon/2}\ge C$. This proves the exact eventual assertion. A useful consequence, $\max_{1\le n\le X}\tau(n)\le X^\varepsilon$ for sufficiently large $X$, follows by treating finitely many small $n$ separately, but it is not silently included in this axiom.

## Appendix A. Exact helper definitions

The following are definitions, not additional axioms. They determine the meaning of the six formal statements above. The companion Lean file is the source of these verbatim snippets.


```lean
def rationalMass (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, (1 : ℚ) / (d : ℚ)
```

```lean
def expPhase (U : ℕ) (z : ZMod U) : ℂ :=
  Complex.exp
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (z.val : ℂ) / (U : ℂ))
```

```lean
def inversePrefix (U N : ℕ) (a : ZMod U) : ℂ := by
  classical
  exact ∑ n ∈ ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n U)),
    expPhase U (a * (n : ZMod U)⁻¹)
```

```lean
def fourierSum {U N : ℕ} (x : Fin N → ZMod U) (h : ℕ) : ℂ :=
  ∑ j : Fin N, expPhase U ((h : ZMod U) * x j)
```

```lean
def residueIntervalCount {U N : ℕ} (x : Fin N → ZMod U)
    (α ℓ : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin N =>
    α ≤ (x j).val ∧ (x j).val < α + ℓ)).card
```

```lean
def primeReciprocalSum (x : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime),
    (1 : ℝ) / (p : ℝ)
```

```lean
def divisorCount (n : ℕ) : ℕ :=
  (Nat.divisors n).card
```

```lean
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2
```

```lean
structure GAPRepresentation where
  rank : ℕ
  step : Fin rank → ℤ
  lower : Fin rank → ℝ
  upper : Fin rank → ℝ
```

Inside `namespace GAPRepresentation`:


```lean
def eval (P : GAPRepresentation) (v : Fin P.rank → ℤ) : ℤ :=
  ∑ i, v i * P.step i
```

```lean
def coordinateBox (P : GAPRepresentation) (t : ℝ) :
    Set (Fin P.rank → ℤ) :=
  {v | ∀ i, t * P.lower i ≤ (v i : ℝ) ∧
    (v i : ℝ) ≤ t * P.upper i}
```

```lean
def carrierAt (P : GAPRepresentation) (t : ℝ) : Set ℤ :=
  P.eval '' P.coordinateBox t
```

```lean
def properAt (P : GAPRepresentation) (t : ℝ) : Prop :=
  (P.coordinateBox t).Nonempty ∧ Set.InjOn P.eval (P.coordinateBox t)
```

Back in `namespace Erdos289.External`:


```lean
def integerSubsetSums (A : Finset ℤ) : Set ℤ :=
  {z | ∃ B : Finset ℤ, B ⊆ A ∧ (∑ b ∈ B, b) = z}
```


## Appendix B. Conditional use and future discharge

The source collects the six propositions as explicit hypotheses:


```lean
structure ExternalInputs : Prop where
  liu_sawhney : LiuSawhneyStatement
  cfhmpsv_structure : CFHMPSVStructureStatement
  bourgain_garaev : BourgainGaraevStatement
  erdos_turan : ErdosTuranStatement
  mertens_second : MertensSecondStatement
  divisor_bound : DivisorBoundStatement
```


The intended main theorem has type `ExternalInputs → Erdos289.CandidateStatement`. That implication is **not** supplied here. `Assumed.inputs` only packages the six assumed facts. Our correction fibers, sparse inverse coverage, descent, interval separation, and exact-count arguments must be proved from them.

After a successful build, inspect both the final theorem's full type and its transitive axiom report. Explicit hypotheses appear in the type, while global assumptions appear in `#print axioms`; checking one alone is insufficient. A wrapper using `Assumed.inputs` may depend on these six named external axioms and the ordinary foundational axioms, but should contain no `sorryAx` or further unlisted mathematical assumptions. These inspection commands can be placed after importing the module:

```lean
#print Erdos289.External.ExternalInputs
#print axioms Erdos289.External.Assumed.inputs
```

To discharge an input, replace its named axiom with a theorem of the same type, or supply that theorem directly to the conditional main result. Merely placing a proof of the same proposition beside the old axiom does not remove the old dependency: consumers must use the proof and be rebuilt. The prime-counting estimate and any other external result used downstream must likewise be proved or found in the pinned library; they are not hidden inside this six-field record.

The source intentionally contains exactly six `axiom` declarations and no theorem claiming the candidate conclusion. It has no `sorry` or `admit` proof placeholders. These are source properties, not a kernel certificate. An independent source review, the first compiler run, and an audit of the eventual main theorem remain distinct tasks.

**Source identity.** The SHA-256 of `Erdos289ExternalAxioms.lean` audited by this document is:

```text

6a4affa2cecb731c87ec21433305842bd3c0c92bc7c62a8ca86f410f3647c5d7
```


---

## Terminal theorem and verification procedure

The terminal theorem is intended to be

```lean
theorem Erdos289.candidateStatement : Erdos289.CandidateStatement
```

with `CandidateStatement` and `FamilyWitness` exactly as in the audited
`Erdos289/Intervals.lean`. To verify a completed certificate:

```sh
lake build                      # must succeed with no errors
lake env lean scripts/Axioms.lean   # prints the axioms of the terminal theorem
```

For the unconditional certificate described in the statement of faithfulness, the axiom
report must list only `propext`, `Classical.choice`, and `Quot.sound`.

**Conditional form.** The six literature inputs are the axioms
`Erdos289.External.Assumed.*` of the audited module `Erdos289/ExternalAxioms.lean` (see the
statement of faithfulness for the six axioms above). A build of the terminal theorem whose
axiom report lists exactly the three standard axioms plus those six names certifies the
implication "the six cited results imply `CandidateStatement`". If `sorryAx` appears, some
other dependency is unproved. The planned final form states the theorem as
`ExternalInputs → CandidateStatement`, with the six inputs visible in its type.

## Current status

The formalization is organized as follows (paper section → Lean file).

| Component | File | Status |
|---|---|---|
| Audited target (`FamilyWitness`, `CandidateStatement`) | `Intervals.lean` | audited, unchanged |
| Working definitions and `Statement k` | `Defs.lean` | done |
| Bridge `Statement k → FamilyWitness k` | `Target.lean` | proved |
| Separated family → ordered statement | `Sorting.lean` | proved |
| §1 literature inputs (Liu–Sawhney; Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte Thm 3; Bourgain–Garaev; Mertens; divisor bound; Erdős–Turán) | `External.lean`, `ErdosTuran.lean` | **named axioms** (Chebyshev's bound and the prime-power count are proved) |
| §2 Lemma 1 (powersmooth fibers) | `Lemma1*.lean` | proved (equidistribution follows the author's blueprint) |
| §2 Lemma 2 (separation of correction pairs) | `Lemma2.lean` | proved |
| §3 Lemma 3 (sparse inverse covering) | `Lemma3*.lean` | proved |
| §4 Lemma 4 (powersmooth supply) | `Lemma4.lean` | proved |
| §4 cancellation identity (4.6) | `Cancel.lean`, `DenBound.lean` | proved |
| §4 Lemma 5 (auxiliary pairs), (4.2), (4.5) | `Lemma5.lean` | proved |
| §4 correction procedure, (4.8), (4.9) | `Descent.lean`, `CorrData.lean`, `Tail.lean` | proved |
| §5 Lemma 6 and the core | `Lemma6.lean`, `Core.lean`, `Harmonic.lean` | proved (Lemma 6 from the Liu–Sawhney axiom) |
| §6 main pairs | `MainPairs.lean`, `Greedy.lean` | proved |
| §7 assembly | `Assembly.lean` | proved |
| Terminal theorem `candidateStatement` | `Main.lean` | proved; axiom report = 3 standard + 6 audited axioms, no `sorryAx` |
| Audited six-axiom module | `ExternalAxioms.lean` | audited, unchanged |
| Bridge from our input statements to the audited axioms | `ExternalBridge.lean` | proved (all six) |
| Ported elementary lemmas from the author's starter | `Expert.lean` | proved |

Every row is proved; the only non-standard axioms in the terminal theorem's report are the
six audited ones. Until those are replaced by proofs, the unconditional certificate does not
exist.

The literature inputs are the largest remaining obligation. Under the statement of
faithfulness, citing them is not enough: they must be supplied as checked Lean proofs.

## Layout

- `erdos_289_full_proof.pdf`: the manuscript being formalized.
- The author's statement of faithfulness is reproduced above; the audited `Intervals.lean` is included unchanged.
- `Erdos289/`: the Lean sources. `lakefile.toml` pins Mathlib to tag `v4.34.0-rc2`.
- `FORMALIZATION_PLAN.md`: the file map and order of work.
