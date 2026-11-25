import Erdos879.Analytic.Defs

namespace Erdos879

axiom riemannHypothesis : RiemannHypothesis

axiom vonKoch_of_riemannHypothesis : RiemannHypothesis → VonKoch

axiom selberg_of_riemannHypothesis : RiemannHypothesis →
    ∀ x : ℝ, (10 : ℝ) ^ 8 ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / (10 : ℝ) ^ 8 →
      ∫ y in (1 : ℝ)..x, (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2
        < 202 * δ * x ^ 2 * (Real.log x) ^ 2

theorem vonKoch : VonKoch := vonKoch_of_riemannHypothesis riemannHypothesis

theorem selbergMS : SelbergMS :=
  ⟨202, (10 : ℝ) ^ 8, 1 / (10 : ℝ) ^ 8, by positivity, fun x hx δ hδ hδ' =>
    (selberg_of_riemannHypothesis riemannHypothesis x hx δ hδ hδ').le⟩

end Erdos879
