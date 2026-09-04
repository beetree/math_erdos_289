# Erdős Problem 289: Lean 4 formalization

## Verification transcript

Recorded on 4 September 2026 in the maintainer's working copy at commit `61f54d7` of `main`
(clean status), with the pinned toolchain and the existing lockfile. `lake build` replays the
up-to-date modules from the build cache; an earlier from-scratch build of the same sources in a
fresh clone (at tag `v1.0-unconditional-certificate`, commit `6de963b`, whose Lean sources differ
from `61f54d7` only by comment edits and one filename made ASCII) produced the same report.

```console
$ git rev-parse HEAD
61f54d7ba430b3869854bb51ccefb16e48e5c11d
$ cat lean-toolchain
leanprover/lean4:v4.34.0-rc2
$ sha256sum Erdos289/Intervals.lean lake-manifest.json
178e26470eb61a81f183761d053b697d1800bda64a622dd69858ad065f441871  Erdos289/Intervals.lean
119e31567cce06a9f16a6fe8dd2fab7636ce8483c1a2687efc38ced5bc53e773  lake-manifest.json
$ lake build
ℹ [9101/9104] Replayed Erdos289.Main
info: Erdos289/Main.lean:25:0: 'Erdos289.candidateStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9104 jobs).
$ cat AxiomCheck.lean
import Erdos289.Main
#check (Erdos289.candidateStatement : Erdos289.CandidateStatement)
#print axioms Erdos289.candidateStatement
#print axioms Erdos289.Ported.cfhmpsv_structure_audited
#print axioms Erdos289.Ported.liu_sawhney_audited
#print axioms Erdos289.Ported.mertens_second_audited
#print axioms Erdos289.Ported.divisor_bound_audited
$ lake env lean AxiomCheck.lean
Erdos289.candidateStatement : Erdos289.CandidateStatement
'Erdos289.candidateStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos289.Ported.cfhmpsv_structure_audited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos289.Ported.liu_sawhney_audited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos289.Ported.mertens_second_audited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos289.Ported.divisor_bound_audited' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The build produces no errors and no warnings; the single info line is the axiom report printed
by `Erdos289/Main.lean`. `propext`, `Classical.choice`, and `Quot.sound` are Lean's standard
foundational axioms. No `sorryAx`, no `Lean.ofReduceBool`, and no project-declared axiom
appears: the theorem `Erdos289.candidateStatement : Erdos289.CandidateStatement` is proved using
Mathlib (`v4.34.0-rc2`, revision `85e3a25e`, pinned in `lake-manifest.json`) and the vendored
proved lemmas under `SolveMath/` and `ErdosProblems/`, with only the stated standard foundational
axioms. The last four lines are diagnostics for the retained theorem interfaces; the terminal
report is the essential gate. This check was run on the maintainer's side; no independent third
party has yet reproduced it.

## How to read this repository

The trust chain has two links, plus the integrity of the checking environment.

1. **The statement of faithfulness** (reproduced in the next section, with the status updates
   noted there). It is the human-checked claim that the formal proposition
   `Erdos289.CandidateStatement`, as declared in the audited file `Erdos289/Intervals.lean`,
   is a faithful strengthening of the nonadjacent formulation of Erdős Problem 289. This is
   the one thing a reader must examine and believe; no machine can check it.
2. **The Lean kernel.** Once the terminal theorem `Erdos289.candidateStatement` (lowercase
   `c`; it is the proof of the proposition `Erdos289.CandidateStatement`) is checked and
   `#print axioms Erdos289.candidateStatement` reports only `propext`, `Classical.choice`,
   and `Quot.sound`, the manuscript's analytic arguments, the tactics, the AI that wrote the
   proof scripts, and the cited papers need not be trusted as independent authorities: the
   proof terms and their dependencies supply the justification. Printing the axioms of the
   proposition definition `CandidateStatement` is not the proof audit; the theorem is.

The remaining trust is in this correspondence, in Lean's logical foundations and checker, and
in the integrity of the checking environment and of the identified source artifact. A
transcript does not authenticate itself: reproduce the check from a fresh checkout of the
pinned revision (see "Terminal theorem and verification procedure").

The audited file is included unchanged. Its SHA-256 is the one recorded in the
statement of faithfulness:

```text
178e26470eb61a81f183761d053b697d1800bda64a622dd69858ad065f441871  Erdos289/Intervals.lean
```

It compiles as is on the pinned toolchain (Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2`).
Do not edit it. Any change to it invalidates the audit.

## Statement of faithfulness

The following statement was supplied by the author of the proof at the time of the audit,
before the formalization existed. It is reproduced with its title demoted to a subheading and
its status remarks, toolchain, and certificate data updated to the completed state; the audit's
substance, the correspondence between the formal proposition and the problem, is unchanged, and
so is the audited file.

---

### Statement of faithfulness: Erdős Problem 289

**Version: 4 September 2026. Status: statement audit; formal proof complete, kernel-checked (see the verification transcript above).**

This statement identifies the mathematical assertion that the Lean project is intended to prove and explains why that assertion would answer Erdős Problem 289 in its nonadjacent formulation. It distinguishes the human task of checking that the formal statement captures the problem from the kernel's task of checking a proof of that statement. The completed, kernel-checked proof is `Erdos289.candidateStatement` in `Erdos289/Main.lean`.

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

The project also defines `Erdos289.Problem289Statement`, which permits any interval length at least two and an arbitrary fixed positive integer $C$ in the bound $b_i\le Ck$. Despite its name, this still includes a linear-bound strengthening of the problem stated above. The source contains the proved implication `candidate_implies_problem289`, obtained by taking $C=20$. This implication assumes `CandidateStatement`; it does not prove that assumption.

For the intended kernel guarantee, the completed artifact must contain an **unconditional theorem of type `Erdos289.CandidateStatement`**, with its definitions agreeing with those audited here. A theorem that assumes the candidate, its construction, or unproved analytic inputs would certify only an implication. Merely defining the proposition, compiling auxiliary lemmas, or obtaining a successful build is insufficient.

The final theorem's complete dependency chain must be checked. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`, corresponding to propositional extensionality, classical choice, and quotient soundness in Lean's usual foundations. No `sorryAx`, conjecture-specific axiom, or additional computational trust axiom may occur. These foundations and the role of kernel checking are described in [Lean's account of axioms](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/) and its [description of the kernel](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#the-kernel).

In particular, the results of Bourgain–Garaev, Conlon and collaborators, and Liu–Sawhney must be supplied through checked Lean proofs, including their dependencies, if they are used. Their publication or citation cannot substitute for those proofs under this guarantee. In the completed formalization, the results of Conlon and collaborators and Liu–Sawhney are supplied by checked Lean proofs (vendored, see "Vendored proofs"), and Bourgain–Garaev is not used.

Once these requirements are met, a reader need not trust the manuscript's analytic arguments, the tactics, or the AI that wrote the proof scripts as independent mathematical authorities: the proof terms and their dependencies supply the justification. The remaining trust is in the correspondence explained here, Lean's logical foundations and checker, and the integrity of the checking environment and identified source artifact. The kernel cannot itself establish that a formal proposition is the problem Erdős intended.

This audit applies to `Erdos289/Intervals.lean`, with SHA-256:

```text
178e26470eb61a81f183761d053b697d1800bda64a622dd69858ad065f441871
```

The toolchain is Lean `v4.34.0-rc2` with Mathlib `v4.34.0-rc2` (revision `85e3a25e`, pinned in `lake-manifest.json`). A completed certificate must identify the final source revision, resolved dependency revisions, checked terminal theorem, and its axiom report. Changes to the target or its definitions require this correspondence to be checked again. **This certificate: tag `v1.0-unconditional-certificate` (commit `6de963b`); terminal theorem `Erdos289.candidateStatement : Erdos289.CandidateStatement`; axiom report `[propext, Classical.choice, Quot.sound]`.**

---

## Terminal theorem and verification procedure

The terminal theorem is

```lean
theorem Erdos289.candidateStatement : Erdos289.CandidateStatement
```

with `CandidateStatement` and `FamilyWitness` exactly as in the audited
`Erdos289/Intervals.lean`. To verify a completed certificate:

```sh
lake build   # must succeed with no errors; the axiom report is printed by Erdos289/Main.lean
```

or, after the build, with a check file `AxiomCheck.lean` containing

```lean
import Erdos289.Main
#check (Erdos289.candidateStatement : Erdos289.CandidateStatement)
#print axioms Erdos289.candidateStatement
```

run `lake env lean AxiomCheck.lean`. Use the lowercase theorem name; `Erdos289.CandidateStatement`
is the proposition, not the proof. For the unconditional certificate described in the statement of faithfulness, the axiom
report must list only `propext`, `Classical.choice`, and `Quot.sound`.

At tag `v1.0-unconditional-certificate` (commit `6de963b`) this is the case: the build is
warning-free and its single info line is that report. The module `Erdos289/ExternalAxioms.lean`
(the author's audited declarations of six literature results as axioms) is kept unchanged for the
record; none of its axioms is in the terminal theorem's dependency chain.

## Current status

Complete, according to the certificate recorded above. The formalization and the accompanying
manuscript (`erdos_289_full_proof.pdf`) use signed correction fibers and finite orientation
selection. Sparse inverse covering retains the Conlon–Fox–Pham structure theorem, supplied by a
vendored formal proof. Bourgain–Garaev and Erdős–Turán are not used by the terminal theorem. The
paper and the Lean development differ in some intermediate estimates, as described in the paper's
Appendix A.3 (for example the fixed-loss lower bound in `Lemma3Steps45.lean` versus the paper's
divisor-envelope bound). Paper section → Lean file:

| Paper component | Section | Principal Lean files |
|---|---:|---|
| Audited target (`FamilyWitness`, `CandidateStatement`) | App. A.1 | `Intervals.lean` (audited, unchanged) |
| Working definitions and `Statement k`; bridge to `FamilyWitness`; sorted statement | 8 | `Defs.lean`, `Target.lean`, `Sorting.lean`, `Compat.lean` |
| Literature inputs (Liu–Sawhney; Conlon–Fox–Pham structure theorem; Mertens; divisor bound) | 2 | `ExternalBridge.lean`, `CFPBridge.lean`, `External.lean`, vendored libraries |
| Signed fibers and finite orientation (Lemmas 1–2) | 3 | `SignedDefs.lean`, `SignedF1.lean`, `SignedF2.lean`, `Sieve.lean` |
| Sparse inverse covering (Lemma 3, wide form with `C = 8`) | 4 | `Lemma3Basic.lean`, `Lemma3Steps45.lean`, `Lemma3.lean`, `CFPBridge.lean` |
| Endpoint density, powersmooth supply, auxiliary pairs, signed cancellation, descent (Prop. 3, Lemmas 4–5, Prop. 4) | 5 | `SignedD1.lean`, `Lemma4.lean`, `Lemma5S.lean`, `SignedCancel.lean`, `DescentS.lean`, `SignedTail.lean`, `CorrDataS.lean` |
| Protected core (Lemma 6, Prop. 5) | 6 | `Lemma6.lean`, `CoreS.lean`, `Harmonic.lean` |
| Main pairs (Prop. 6) | 7 | `MainPairs.lean`, `Greedy.lean` |
| Final assembly and terminal theorem | 8 | `AssemblyS2.lean`, `Sorting.lean`, `Target.lean`, `Main.lean` |
| Elementary lemmas ported from the author's starter | — | `Expert.lean` |

Files retained from the earlier unsigned development and not on the terminal theorem's path in
the same role: `Lemma2.lean` (separation of the earlier unsigned pairs; **not** the paper's current
Lemma 2, which is finite simultaneous orientation), `Lemma5.lean`, `Cancel.lean`, `DenBound.lean`,
`Descent.lean`, `Tail.lean`, `Core.lean` (unsigned versions, some of which supply helper lemmas to
their signed counterparts), and the historical axiom-based bridges in `ExternalBridge.lean`.

## Vendored proofs

The `SolveMath` library holds 41 modules (about 30,700 lines) ported from Boris Alexeev's
`plby/lean-proofs` corpus (commit `61fce10e`) via the `solve-math` repository, each set
minimized by walking the proof terms of the main theorem: 1 module for the divisor bound, 3 for
Mertens, 37 for Liu–Sawhney. The only entry points are the three bridge files
`SolveMath/Ported/{DivisorBound,MertensSecond,LiuSawhney}.lean` (theorems `Erdos289.Ported.<name>`
and `Erdos289.Ported.<name>_audited`), and the only `Erdos289` file importing them is
`Erdos289/ExternalBridge.lean`. The `ErdosProblems` library holds the 258 modules (about 90,000
lines; Apache-2.0 headers on all but three files, see `ErdosProblems/PROVENANCE.md` and
`ErdosProblems/LICENSE.upstream`) of the Conlon–Fox–Pham structure theorem from the same corpus's
Erdős 186 development, bridged to the audited statement by `Erdos289.Ported.cfhmpsv_structure_audited`
in `Erdos289/CFPBridge.lean`. The files are ported from the identified snapshot with the documented
changes (compatibility and warning-cleanup edits, and one filename made ASCII), not byte-identical
copies. Provenance, upstream authorship (Codex / GPT-5.6; the `solve-math` route had no LICENSE
file) and every edit are summarized in `SolveMath/PROVENANCE.md` and `ErdosProblems/PROVENANCE.md`;
the full port records are included under `docs/provenance/`. The upstream reference snapshot
itself is not included. No dependency on the `solve-math` repository exists.

## Layout

- `erdos_289_full_proof.pdf`, `erdos_289_full_proof.tex`: the manuscript accompanying the
  formalization (`scripts/build_proof_pdf.sh` rebuilds the PDF).
- `docs/elementary_replacements.md`: the author's replacement proposal (historical); its
  Sections 2–4 (signed fibers) were formalized, its Section 1 (weighted-Fourier covering) was not.
- `docs/provenance/`: the port records for the vendored proofs.
- `Erdos289/`: the Lean sources; `Erdos289/Main.lean` holds the terminal theorem. The audited
  files `Intervals.lean` and `ExternalAxioms.lean` are included unchanged.
- `SolveMath/`, `ErdosProblems/`: vendored proofs of the literature inputs (see "Vendored proofs").
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: pins to Lean and Mathlib `v4.34.0-rc2`.

## Authorship and use of AI

Author: Johan Land, 4 September 2026.

Large language models were used extensively in this work: in developing and checking the
argument, in drafting this manuscript, and in writing the accompanying Lean formalization. The
models used were GPT 6 Astra (OpenAI), Claude Fable 5.1 (Anthropic) and Gemini 3.8 Flash
(Google). The Lean formalization builds on Mathlib and, in addition, on an extensive library of
Lean proofs of roughly three million lines. All mathematical content was reviewed by the author,
who takes sole responsibility for it. The author thanks the reviewers whose comments on earlier
drafts led to the present formulation.
