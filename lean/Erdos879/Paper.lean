import Erdos879.Results
import Erdos879.Doubling
import Erdos879.UpperEq
import Erdos879.Inputs
import Erdos879.Analytic.Localised
import Erdos879.Analytic.Gaps

open Finset MeasureTheory

namespace Erdos879.Paper

theorem theorem_1_1 (n : ℕ) :
    (n : ℝ) / 4 * (∫ u in Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4), (W n u : ℝ) / u)
          - n - 1 ≤ (H n : ℝ) - G n ∧
      (H n : ℝ) - G n ≤
        2 * (n : ℝ) * (∫ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u)
          + (n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) + n :=
  ⟨lower_G n, upper_G two_mul_primeCounting_le n⟩

theorem lemma_2_1 (n : ℕ) (u : ℝ) (hu : Real.sqrt n ≤ u) :
    (Q n u).card = Winf n u ∧ Winf n u = W n u :=
  ⟨card_Q_eq n u hu, Winf_eq_W two_mul_primeCounting_le n u hu⟩

theorem theorem_1_2_i :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      (∫ u in Set.Ico (2 * Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u) ≤ C * (Real.log n) ^ 5 :=
  _root_.Erdos879.theorem_1_2_i selbergMS

theorem theorem_1_2_ii :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      I n ≤ C * (n : ℝ) ^ (1 / 8 : ℝ) * (Real.log n) ^ (5 / 2 : ℝ) :=
  _root_.Erdos879.theorem_1_2_ii vonKoch selbergMS

theorem theorem_1_2_iii :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Ioc N (2 * N), I n) ≤ C * (N : ℝ) * (Real.log N) ^ 5 :=
  _root_.Erdos879.theorem_1_2_iii selbergMS

theorem corollary_1_3_a :
    ∃ C : ℝ, ∀ n : ℕ, 2 ^ 18 ≤ n →
      (n : ℝ) / 4 * I n - n - 1 ≤ (H n : ℝ) - G n ∧
        (H n : ℝ) - G n ≤ 2 * (n : ℝ) * I n + C * (n : ℝ) * (Real.log n) ^ 5 :=
  _root_.Erdos879.corollary_1_3_a two_mul_primeCounting_le selbergMS

theorem corollary_1_3_b :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      (H n : ℝ) - G n ≤ C * (n : ℝ) ^ (9 / 8 : ℝ) * (Real.log n) ^ (5 / 2 : ℝ) :=
  _root_.Erdos879.corollary_1_3_b two_mul_primeCounting_le vonKoch selbergMS

theorem corollary_1_3_c :
    ∃ C : ℝ, ∀ N : ℕ, ∀ lam : ℝ, 1 ≤ lam →
      (((Finset.Icc 3 N).filter
        (fun n : ℕ => lam * (n : ℝ) * (Real.log n) ^ 5 < (H n : ℝ) - G n)).card : ℝ)
        ≤ C * (N : ℝ) / lam :=
  _root_.Erdos879.corollary_1_3_c two_mul_primeCounting_le selbergMS

theorem corollary_1_3_c' :
    ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
      (((Finset.Icc 3 N).filter
        (fun n : ℕ => (n : ℝ) * (Real.log n) ^ 6 < (H n : ℝ) - G n)).card : ℝ)
        ≤ C * (N : ℝ) / Real.log N :=
  _root_.Erdos879.corollary_1_3_c' two_mul_primeCounting_le selbergMS

lemma ls_consequence (e : ℝ) (he : 0 < e) (C₁ : ℝ)
    (h₁ : ∀ n : ℕ, 3 ≤ n →
      (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ e)) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      I n ≤ C * (n : ℝ) ^ e ∧ (H n : ℝ) - G n ≤ C * (n : ℝ) ^ (1 + e) := by
  obtain ⟨C₂, hC₂, h₂⟩ := upper_I two_mul_primeCounting_le selbergMS
  have hD : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
  have hK : (0 : ℝ) ≤ C₂ * (5 / e) ^ 5 := by positivity
  refine ⟨3 * max C₁ 0 + C₂ * (5 / e) ^ 5, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : 0 ≤ (n : ℝ) ^ e := Real.rpow_nonneg hn0.le _
  have hI : I n ≤ max C₁ 0 * (n : ℝ) ^ e := by
    refine integral_le_of_lintegral n (Real.sqrt_pos.mpr hn0) (mul_nonneg hD hpow)
      ((h₁ n hn).trans ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog : Real.log n ^ 5 ≤ (5 / e) ^ 5 * (n : ℝ) ^ e := by
    have h := Real.log_le_rpow_div hn0.le (by positivity : (0 : ℝ) < e / 5)
    have e1 : (n : ℝ) ^ (e / 5) / (e / 5) = 5 / e * (n : ℝ) ^ (e / 5) := by field_simp
    rw [e1] at h
    have e2 : ((n : ℝ) ^ (e / 5)) ^ 5 = (n : ℝ) ^ e := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      push_cast
      ring
    calc Real.log n ^ 5 ≤ (5 / e * (n : ℝ) ^ (e / 5)) ^ 5 := pow_le_pow_left₀ hlog0 h 5
      _ = (5 / e) ^ 5 * (n : ℝ) ^ e := by rw [mul_pow, e2]
  have hadd : (n : ℝ) ^ (1 + e) = n * (n : ℝ) ^ e := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  refine ⟨hI.trans (mul_le_mul_of_nonneg_right (by linarith) hpow), ?_⟩
  have hH := h₂ n hn
  have s1 : 2 * (n : ℝ) * I n ≤ 2 * (n : ℝ) * (max C₁ 0 * (n : ℝ) ^ e) :=
    mul_le_mul_of_nonneg_left hI (by linarith)
  have s2 : C₂ * (n : ℝ) * Real.log n ^ 5 ≤ C₂ * (n : ℝ) * ((5 / e) ^ 5 * (n : ℝ) ^ e) :=
    mul_le_mul_of_nonneg_left hlog (mul_nonneg hC₂ hn0.le)
  have s3 : 0 ≤ max C₁ 0 * ((n : ℝ) * (n : ℝ) ^ e) := mul_nonneg hD (mul_nonneg hn0.le hpow)
  rw [hadd]
  nlinarith [s1, s2, s3]

theorem theorem_1_4 (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hLS : HypothesisLSAt θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      I n ≤ C * (n : ℝ) ^ ((1 - 2 * θ) / 8 + ε) ∧
        (H n : ℝ) - G n ≤ C * (n : ℝ) ^ (9 / 8 - θ / 4 + ε) := by
  intro ε hε
  obtain ⟨C₁, h₁⟩ := localised_bound_at vonKoch θ hθ0 hθ hLS ε hε
  have he : 0 < (1 - 2 * θ) / 8 + ε := by linarith
  obtain ⟨C, hC⟩ := ls_consequence ((1 - 2 * θ) / 8 + ε) he C₁ h₁
  refine ⟨C, fun n hn => ?_⟩
  have h := hC n hn
  have e : 1 + ((1 - 2 * θ) / 8 + ε) = 9 / 8 - θ / 4 + ε := by ring
  rw [e] at h
  exact h

theorem theorem_1_4_half (hLS : HypothesisLS) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      I n ≤ C * (n : ℝ) ^ ε ∧ (H n : ℝ) - G n ≤ C * (n : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨C₁, h₁⟩ := localised_bound vonKoch hLS ε hε
  exact ls_consequence ε hε C₁ h₁

theorem proposition_7_1 (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hLS : HypothesisLSAt θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (∀ m : ℕ, p < m → m < q → ¬ m.Prime) →
      (q : ℝ) - p ≤ C * (p : ℝ) ^ ((1 - θ) / 2 + ε) :=
  gap_bound_of_LS θ hθ0 hθ hLS

end Erdos879.Paper
