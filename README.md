# Erdős problem 879: sums of pairwise coprime integers

Let $G(n)$ be the largest sum of a set of pairwise coprime positive integers not exceeding $n$,
and let $H(n)=\sum_{p<n}p+n\,\pi(\sqrt n)$. Erdős asked whether
$G(n)>H(n)-n^{1+o(1)}$ (first part of [Problem 879](https://www.erdosproblems.com/879)).

- Paper: [erdos_879.pdf](erdos_879.pdf) ([LaTeX source](erdos_879.tex))
- Lean 4 formalisation: [lean/](lean/README.md)
- Program for the numerical tables of Section 8: [tables_erdos_879.py](tables_erdos_879.py)

## Results

Let $W_n(u)$ be the largest surplus, over intervals $(u,v]$ with $v\le4u$, of the numbers $n/p$
with $p\le\sqrt n$ prime over the primes, and let $I(n)=\int_{\sqrt n}^{2\sqrt n}W_n(u)\,du/u$.

1. **Two-sided bound, with no hypothesis.** For every $n\ge2$,
   $$\frac n4\int_{\sqrt n}^{n^{2/3}/4}W_n(u)\frac{du}{u}-n-1\ \le\ H(n)-G(n)\ \le\ 2n\int_{\sqrt n}^{n/2}W_n(u)\frac{du}{u}+n\sum_{p\le\sqrt n}\frac1p+n .$$
2. **Every $n$.** $H(n)-G(n)\ll n^{9/8}(\log n)^{5/2}$.
3. **Almost all $n$.** $H(n)-G(n)\le n(\log n)^6$ for all but $O(N/\log N)$ integers $n\le N$,
   so the answer to the question is yes for almost all $n$.
4. **Reduction.** For every $n$ the question is equivalent to $I(n)\le n^{o(1)}$, a statement
   about the primes in $[\sqrt n/8,\,8\sqrt n]$.
5. **A sliding scale.** If Selberg's mean value estimate holds for averages over ranges of
   length $x^{1-\theta}$ with $0\le\theta\le\frac12$ (Hypothesis LS($\theta$) of the paper), then
   $H(n)-G(n)\ll n^{9/8-\theta/4+\varepsilon}$ for every $n$. The case $\theta=0$ is Selberg's
   theorem and gives the exponent $9/8$ of result 2; the case $\theta=\frac12$ answers the question.
   No $\theta>0$ is known to follow from the Riemann hypothesis: Hypothesis LS($\theta$) implies that
   gaps between consecutive primes are $\ll p^{(1-\theta)/2+\varepsilon}$ (Proposition 7.1), and the
   exponent $\frac12$ of Cramér's bound has not been improved under RH.

Results 2–4 use the Riemann hypothesis, proved by Alpöge in November 2026, through von Koch's
bound for $\pi(y)-\mathrm{li}(y)$ and Selberg's mean value estimate for primes in short
intervals. The question for every $n$ remains open.

## Formal verification

The proofs are formalised in Lean 4 with Mathlib (7,687 lines, no `sorry`). The two-sided
bound is checked from the definitions alone. The results which use the Riemann hypothesis are
checked with three statements taken as given: the Riemann hypothesis, von Koch's theorem, and
Selberg's estimate in the explicit form of Cully-Hugill and Dudek. Details, the list of formal
statements and build instructions are in [lean/README.md](lean/README.md).

## Preparation

The paper and the formalisation were prepared with AI systems; see the note at the end of the
paper.
