# Lean formalisation: a problem of Erdős and van Lint (Erdős problem 879)

This directory contains a Lean 4 formalisation of the paper
[On a problem of Erdős and van Lint on sums of pairwise coprime integers](../erdos_879.pdf).

`G n` is the largest sum of a set of pairwise coprime positive integers not exceeding `n`,
`H n = ∑_{p<n} p + n·π(√n)`, `W n u` is the function `W_n(u)` of the paper, and
`I n = ∫_{√n}^{2√n} W_n(u) du/u`. The definitions are in `Erdos879/Defs.lean` (32 lines) and
`Erdos879/Results.lean` (`I`).

## Statements

All final statements are in `Erdos879/Paper.lean`, in the namespace `Erdos879.Paper`.

| Paper | Lean | Depends on |
| --- | --- | --- |
| Theorem 1.1 | `theorem_1_1` | standard axioms only |
| Lemma 2.1 | `lemma_2_1` | standard axioms only |
| Theorem 1.2 (i) | `theorem_1_2_i` | cited inputs 1, 3 |
| Theorem 1.2 (ii) | `theorem_1_2_ii` | cited inputs 1, 2, 3 |
| Theorem 1.2 (iii) | `theorem_1_2_iii` | cited inputs 1, 3 |
| Corollary 1.3 (a) | `corollary_1_3_a` | cited inputs 1, 3 |
| Corollary 1.3 (b) | `corollary_1_3_b` | cited inputs 1, 2, 3 |
| Corollary 1.3 (c) | `corollary_1_3_c`, `corollary_1_3_c'` | cited inputs 1, 3 |
| Theorem 1.4 | `theorem_1_4` (hypothesis `HypothesisLSAt θ`), `theorem_1_4_half` (the case `θ = 1/2`) | cited inputs 1, 2, 3 |
| Proposition 7.1 | `proposition_7_1` (hypothesis `HypothesisLSAt θ`) | standard axioms only |

"Standard axioms" are `propext`, `Classical.choice` and `Quot.sound`, on which Mathlib rests.
No file uses `sorry` or `native_decide`.

## Cited inputs

`Erdos879/Inputs.lean` declares three statements as axioms. They are the only axioms in the
project.

1. `riemannHypothesis : RiemannHypothesis`. The Riemann hypothesis, in Mathlib's formulation.
   It was proved by Alpöge (November 2026), and the proof is formalised in Lean in
   [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
   whose final theorem `riemannHypothesis` has this type. That development is cited here and
   is not imported; it uses the same Lean and Mathlib versions as this project, so the axiom
   can be replaced by an import of its module `Main`.
2. `vonKoch_of_riemannHypothesis : RiemannHypothesis → VonKoch`. Von Koch's theorem (1901):
   under RH, `|π(y) − ∫_2^y dt/log t| ≤ C·√y·log y` for `y ≥ 2`. An explicit form is
   Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
   (1976), Corollary 1.
3. `selberg_of_riemannHypothesis`. Selberg's mean value estimate (1943) in the explicit form of
   Cully-Hugill and Dudek, *An explicit mean-value estimate for the PNT in intervals*,
   [arXiv:2206.00433](https://arxiv.org/abs/2206.00433), Theorem 1: under RH, for `x ≥ 10^8`
   and `0 < δ ≤ 10^{-8}`,
   `∫_1^x (θ(y+δy) − θ(y) − δy)² dy < 202·δ·x²·log² x`.

Every theorem of the paper that uses RH is also available with these inputs as explicit
hypotheses (`VonKoch`, `SelbergMS`) in `Erdos879/Results.lean`.

## Building and checking

Lean `v4.33.1` and Mathlib `v4.33.1` (see `lean-toolchain`, `lake-manifest.json`).

    lake exe cache get
    lake build

To see what a statement depends on:

    echo 'import Erdos879
    #print axioms Erdos879.Paper.theorem_1_1
    #print axioms Erdos879.Paper.corollary_1_3_b' > Check.lean
    lake env lean Check.lean

The first prints `[propext, Classical.choice, Quot.sound]`; the second prints these together
with the three cited inputs.

## Files

| File | Content | Paper |
| --- | --- | --- |
| `Defs.lean` | `Admissible`, `G`, `H`, `A`, `W`, `Winf` | Section 1 |
| `UpperMatch.lean`, `Upper.lean` | greedy matching, `upper_bound` | Section 2, Proposition 2.2 |
| `UpperEq.lean` | `card_Q_eq` | Lemma 2.1 |
| `Doubling.lean`, `DoublingCheb.lean`, `DoublingSmall.lean` | `two_mul_primeCounting_le : 2·π(m) ≤ π(4m)` | Lemma 2.1 |
| `Lower.lean` | `lower_bound` | Section 3 |
| `Measurable.lean`, `TwoSided.lean` | measurability, `Winf_eq_W`, `lower_G`, `upper_G` | Theorem 1.1 |
| `Analytic/Defs.lean` | `li`, `E`, `F`, `VonKoch`, `SelbergMS`, the majorants `Bp`, `Bm` | Sections 4, 5 |
| `Analytic/Excess.lean` | `drift`, `excess` | Lemmas 4.1, 4.2 |
| `Analytic/Chain.lean` | `chain_plus`, `chain_minus` | Lemma 5.2 (a), (b) |
| `Analytic/MeanSquare.lean` | `selberg_mult`, `ms_Bp`, `ms_Bm` | Lemma 5.1, Corollary 5.3 |
| `Analytic/Block.lean` | `block` | Lemma 6.1 |
| `Analytic/Bounds.lean` | `outer_bound`, `inner_bound` | Theorem 1.2 (i), (ii) |
| `Analytic/Average.lean` | `average_bound` | Theorem 1.2 (iii) |
| `Analytic/Localised.lean` | `HypothesisLSAt`, `localised_bound_at` | Theorem 1.4 |
| `Analytic/Gaps.lean` | `gap_bound_of_LS` | Proposition 7.1 |
| `Results.lean` | Theorem 1.2 and Corollary 1.3 from `VonKoch`, `SelbergMS` | Section 6 |
| `Inputs.lean` | the three cited inputs | (VK), (MS) |
| `Paper.lean` | final statements | Section 1 |

## Third-party code

`Erdos879/DoublingCheb.lean` (Chebyshev-type bounds for `ψ` and `θ` used for `2·π(m) ≤ π(4m)`)
is adapted from `PrimeNumberTheoremAnd/IEANTN/Chebyshev.lean` of the
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project,
which is distributed under the Apache License 2.0 (`third_party/Apache-2.0.txt`). The
adaptation removes the dependence on `native_decide` and on packages other than Mathlib.
