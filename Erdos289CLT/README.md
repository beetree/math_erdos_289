# `Erdos289CLT`: formalization of *Separated intervals with reciprocal sum one*

This library formalizes the proof in `separated_intervals_reciprocal_sum_one.tex` (S. Cambie, J. Land, Y. Tang).
The target is `Erdos289.CLT.MainStatement` (`Basic.lean`): for every sufficiently large `k`
there is a configuration of `k` pairwise separated integer intervals in `{2, 3, …}`, each of
length `2`, `3` or `4`, with reciprocal sum `1`, all intervals longer than two belonging to a
fixed finite set. `Main.lean` also derives the ordered form `Statement234`
(`Fin k`-indexed `NatInterval`s, consecutive separation), the analogue of the audited
`FamilyWitness` of the earlier formalization in `Erdos289/`.

Conventions: `Erdos289.Iv` intervals with `Iv.mass` (exact rational reciprocal sum) and the
symmetric separation `Iv.Sep`; membership in `G_n = D_n⁻¹ℤ/ℤ` is the predicate `InG n x` on
`ℚ` (`x · lcm(1..n) ∈ ℤ`); the quota is `s q = ⌈q^{3/4}⌉`.

| Paper | Lean file | Main statements |
|---|---|---|
| definitions, Theorem `main` | `Basic.lean` | `Config`, `InG`, `s`, `lpp`, `MainStatement`, block separation `sep_of_blocks` |
| Lemma `pairs` (construction) | `PairsCore.lean` | `mOf`, `loOf`, `TOf`, `carrier_props`, `good_carrier_powersmooth` |
| Lemma `pairs` (exceptions, fibres) | `SqRoots.lean`, `PairsCount.lean` | `card_sq_roots_le_four`, `card_bad_b_le`, `card_bad_two_le`, `carriers_per_m_le_four` |
| Lemma `pairs` (statement) | `Pairs.lean` | `pairs_lemma` |
| Chebyshev estimates | `Chebyshev.lean` | `primeCounting_lower`, `primeCounting_upper`, `primes_in_range` |
| Lemma `subsets` | `Subsets.lean` | `subsets_lemma` (roots of unity) |
| weights mod `G_{q-1}`, covering | `StagePool.lean` | `stage_pool_props` |
| §3 finite starting family | `Seed.lean` | `seed_family` (chains, small intervals, stage-`B` pool) |
| §4 transfer observation | `Transfer.lean` | `Fam`, `transfer` |
| §4 marriage theorem | `Hall.lean`, `Stages.lean` | `hall_stages`, `choose_pools` |
| §4 iteration over stages | `Stages.lean`, `Counts.lean` | `iterate_transfer`, `Ucount`, `width_invariant`, `exists_cutoff` |
| §4 uniform bounds | `Asymptotics.lean` | `tail_small`, `cand_enough`, `pool_pair_mass_le` |
| assembly | `Pools.lean`, `Main.lean` | `seed_pool_exists`, `stage_pools_exist`, `main_theorem`, `statement234` |

Deviations from the paper's text (all strengthen or make explicit what the paper leaves implicit):
the exclusions of chain terms are bounded crudely by the number of chain terms at most `q²`
(`O(log q)` rather than `O(log log q)`), which suffices; the width invariant of the count
intervals is phrased with the largest power of two `≤ n`; the trivial transfer step at
non-prime-power levels replaces "the group changes only at prime powers".

Verification: `scripts/check_clt.sh` builds the library, greps for `sorry`, and prints the
axioms of `Erdos289.CLT.statement234` (expected: `propext`, `Classical.choice`, `Quot.sound`).
