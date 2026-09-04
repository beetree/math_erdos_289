# Erdős Problem 289: Lean 4 formalization

## Verification transcript

`lake build` on `main` produces no errors and no warnings; the single info line is the axiom
report of the terminal theorem, printed by `Erdos289/Main.lean`:

```console
$ cat lean-toolchain
leanprover/lean4:v4.34.0-rc2
$ lake exe cache get
$ lake build
ℹ [9101/9104] Replayed Erdos289.Main
info: Erdos289/Main.lean:21:0: 'Erdos289.candidateStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9104 jobs).
$
```

`propext`, `Classical.choice`, and `Quot.sound` are Lean's standard foundational axioms.
No `sorryAx`, no `Lean.ofReduceBool`, and no project-declared axiom appears: the theorem
`Erdos289.candidateStatement : Erdos289.CandidateStatement` is proved from Mathlib alone
(Mathlib `v4.34.0-rc2`, revision `85e3a25e`, pinned in `lake-manifest.json`). The transcript
above was recorded at tag `v1.0-unconditional-certificate` (commit `6de963b`).

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

The following statement, supplied by the author of the proof, is reproduced verbatim except
that its title is demoted to a subheading for layout. Its remarks about the toolchain and the
uncompiled starter refer to the author's original starter project, whose `Intervals.lean` is the
audited file used here; the toolchain named there (Lean 4.19) is out of date, as this repository
pins Lean and Mathlib `v4.34.0-rc2`, on which the audited file compiles unchanged.

---

### Statement of faithfulness: Erdős Problem 289

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

## Terminal theorem and verification procedure

The terminal theorem is intended to be

```lean
theorem Erdos289.candidateStatement : Erdos289.CandidateStatement
```

with `CandidateStatement` and `FamilyWitness` exactly as in the audited
`Erdos289/Intervals.lean`. To verify a completed certificate:

```sh
lake build   # must succeed with no errors; the axiom report is printed by Erdos289/Main.lean
```

For the unconditional certificate described in the statement of faithfulness, the axiom
report must list only `propext`, `Classical.choice`, and `Quot.sound`.

At tag `v1.0-unconditional-certificate` (commit `6de963b`) this is the case: the build is
warning-free and its single info line is that report. The module `Erdos289/ExternalAxioms.lean`
(the author's audited declarations of six literature results as axioms) is kept unchanged for the
record; none of its axioms is in the terminal theorem's dependency chain.

## Current status

Complete. The formalization follows the manuscript except that Lemma 1 (the correction fibers,
which the manuscript obtains from inverse equidistribution via Bourgain–Garaev and Erdős–Turán)
is replaced by the author's elementary signed-fiber construction, recorded in
`docs/elementary_replacements.md`, Sections 2–4. Paper section → Lean file:

| Component | File | Status |
|---|---|---|
| Audited target (`FamilyWitness`, `CandidateStatement`) | `Intervals.lean` | audited, unchanged |
| Working definitions and `Statement k` | `Defs.lean` | proved |
| Bridge `Statement k → FamilyWitness k`; corrected nonadjacent `Fin k → ℕ × ℕ` formulation (`erdos_289_nonadjacent_statement`, adapted from Formal Conjectures) | `Target.lean`, `Compat.lean` | proved |
| Separated family → ordered statement | `Sorting.lean` | proved |
| Literature inputs used (Liu–Sawhney; Conlon–Fox–Pham structure theorem; Mertens; divisor bound) | `ExternalBridge.lean`, `CFPBridge.lean`, vendored libraries | proved (vendored, kernel-checked) |
| Signed correction fibers (replaces §2 Lemma 1): F1, F2, D1 | `SignedDefs.lean`, `SignedF1.lean`, `SignedF2.lean`, `SignedD1.lean`, `Sieve.lean` | proved |
| §2 Lemma 2 (separation of unsigned pairs) | `Lemma2.lean` | proved |
| §3 Lemma 3 (sparse inverse covering), widened to multipliers `≤ C·q^ε` | `Lemma3Basic.lean`, `Lemma3Steps45.lean`, `Lemma3.lean` | proved |
| §4 Lemma 4 (powersmooth supply) | `Lemma4.lean` | proved |
| §4 cancellation identity, signed form | `Cancel.lean`, `DenBound.lean`, `SignedCancel.lean` | proved |
| §4 Lemma 5 (auxiliary pairs), signed form | `Lemma5.lean`, `Lemma5S.lean` | proved |
| §4 correction procedure and mass bounds, signed form | `Descent.lean`, `DescentS.lean`, `CorrDataS.lean`, `Tail.lean`, `SignedTail.lean` | proved |
| §5 Lemma 6 and the core | `Lemma6.lean`, `Core.lean`, `CoreS.lean`, `Harmonic.lean` | proved |
| §6 main pairs | `MainPairs.lean`, `Greedy.lean` | proved |
| §7 assembly | `AssemblyS2.lean` | proved |
| Terminal theorem `candidateStatement` | `Main.lean` | proved; axiom report = `propext`, `Classical.choice`, `Quot.sound` |
| Ported elementary lemmas from the author's starter | `Expert.lean` | proved |

## Vendored proofs

The `SolveMath` library holds 41 modules (about 30,700 lines) copied verbatim from Boris
Alexeev's `plby/lean-proofs` corpus via the `solve-math` repository, each set minimized by
walking the proof terms of the main theorem: 1 module for the divisor bound, 3 for Mertens,
37 for Liu–Sawhney. The only entry points are the three bridge files `SolveMath/Ported/*.lean`,
and the only `Erdos289` file importing them is `Erdos289/ExternalBridge.lean`.
The `ErdosProblems` library holds the 258 modules (about 90,000 lines, Apache-2.0) of the
Conlon–Fox–Pham structure theorem from the same corpus's Erdős 186 development, bridged to the
audited statement in `Erdos289/CFPBridge.lean`; see `ErdosProblems/PROVENANCE.md`. Provenance, upstream authorship (Codex / GPT-5.6, no LICENSE
file upstream) and every edit are recorded per port in `PROVENANCE.md` files kept with the
reference copies outside the repository. No dependency on the `solve-math` repository exists.

## Layout

- `erdos_289_full_proof.pdf`, `erdos_289_full_proof.tex`: the manuscript being formalized
  (`scripts/build_proof_pdf.sh` rebuilds the PDF).
- `docs/elementary_replacements.md`: the author's replacement argument for Lemma 1, as formalized.
- `Erdos289/`: the Lean sources; `Erdos289/Main.lean` holds the terminal theorem. The audited
  files `Intervals.lean` and `ExternalAxioms.lean` are included unchanged.
- `SolveMath/`, `ErdosProblems/`: vendored proofs of the literature inputs (see "Vendored proofs").
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: pins to Lean and Mathlib `v4.34.0-rc2`.
