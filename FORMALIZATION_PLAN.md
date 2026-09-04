# Formalization plan for Erdős Problem 289 (Lean 4 / Mathlib v4.34.0-rc2)

Source: `erdos_289_full_proof.pdf` (candidate proof, 4 Sept 2026).

## Conventions

- `Erdos289/Defs.lean`: shared definitions. `Powersmooth y n`, `mass a b`, `w a`,
  `Iv` (integer interval), `Iv.Sep` (separated by ≥ 1 unused integer),
  `GoodFamily k` (k separated intervals of length 2/3 in [1,20k] with mass 1),
  `Statement k` (the theorem for fixed k). Target: `∀ᶠ k in atTop, Statement k`.
- Black-box literature inputs live in `Erdos289/External.lean` as `theorem … := by sorry`
  with docstrings. Nothing else may contain `sorry` in the finished state.
- Asymptotics are expressed with `Filter.Eventually`/`atTop` and explicit constants,
  not with informal `o(1)`.

## File map (paper section → Lean file)

| Paper | File | Status |
|---|---|---|
| Statement, defs | `Defs.lean` | done |
| Family → ordered statement | `Sorting.lean` | in progress |
| §1 external inputs (Liu–Sawhney, CFHMPSV Thm 3, Bourgain–Garaev, Mertens, Chebyshev, divisor bound) | `External.lean` | in progress |
| §2 Lemma 1 (powersmooth fibers `I_q`) | `Lemma1.lean` | todo (hard: Erdős–Turán + Bourgain–Garaev) |
| §2 Lemma 2 (separation of correction pairs) | `Lemma2.lean` | in progress |
| §3 Lemma 3 (sparse inverse covering) | `Lemma3.lean` | todo (hard: GAP argument) |
| §4 Lemma 4 (powersmooth supply) | `Lemma4.lean` | todo (Mertens) |
| §4 (4.6) cancellation algebra | `Cancel.lean` | in progress |
| §4 Lemma 5 (auxiliary pairs) + descent procedure | `Descent.lean` | todo |
| §5 Lemma 6 + core pairs/triples | `Core.lean` | todo |
| §6 main pairs, exact count | `Main.lean` | todo |
| §7 assembly | `Assembly.lean` | todo |

## Order of work

1. Skeleton: state Lemmas 1, 3, 4, 5, 6 and the assembly theorem with `sorry`, get
   `erdos289` compiling from them (Assembly first, so the interfaces are validated).
2. Fill elementary leaves: Lemma 2, Cancel, Sorting, descent bookkeeping, Section 6 counting.
3. Analytic leaves: Lemma 4 (Mertens + Chebyshev), Lemma 6 (from Liu–Sawhney).
4. Deep leaves: Lemma 1, Lemma 3.
