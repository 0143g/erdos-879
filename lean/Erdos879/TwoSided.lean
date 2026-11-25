import Erdos879.Upper
import Erdos879.Lower
import Erdos879.Measurable

open Finset MeasureTheory

namespace Erdos879

theorem G_spec (n : ℕ) :
    (∃ S : Finset ℕ, Admissible n S ∧ ∑ a ∈ S, a = G n) ∧
      ∀ S : Finset ℕ, Admissible n S → ∑ a ∈ S, a ≤ G n := by
  have hbdd : BddAbove {s : ℕ | ∃ S : Finset ℕ, Admissible n S ∧ ∑ a ∈ S, a = s} := by
    refine ⟨∑ a ∈ Finset.Icc 1 n, a, ?_⟩
    rintro s ⟨S, hS, rfl⟩
    apply Finset.sum_le_sum_of_subset
    intro a ha
    rw [Finset.mem_Icc]
    exact hS.1 a ha
  have hne : {s : ℕ | ∃ S : Finset ℕ, Admissible n S ∧ ∑ a ∈ S, a = s}.Nonempty :=
    ⟨0, ∅, ⟨by simp, by simp⟩, by simp⟩
  exact ⟨Nat.sSup_mem hne hbdd, fun S hS => le_csSup hbdd ⟨S, hS, rfl⟩⟩

theorem integrableOn_W (n : ℕ) (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => (W n u : ℝ) / u) (Set.Ico a b) := by
  have hm : Measurable (fun u : ℝ => (W n u : ℝ) / u) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (measurable_W n)).div measurable_id
  refine Measure.integrableOn_of_bounded (M := ((smallPrimes n).card : ℝ) / a)
    (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top) hm.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu => ?_)
  have hu0 : 0 < u := ha.trans_le hu.1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hu0.le)]
  have hW : (W n u : ℝ) ≤ (smallPrimes n).card := by exact_mod_cast W_le_card n u
  calc (W n u : ℝ) / u ≤ ((smallPrimes n).card : ℝ) / u :=
        div_le_div_of_nonneg_right hW hu0.le
    _ ≤ ((smallPrimes n).card : ℝ) / a :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha hu.1

theorem ofReal_integral_W (n : ℕ) (a b : ℝ) (ha : 0 < a) :
    ENNReal.ofReal (∫ u in Set.Ico a b, (W n u : ℝ) / u) =
      (∫⁻ u in Set.Ico a b, ENNReal.ofReal ((W n u : ℝ) / u)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_W n a b ha)]
  refine ae_restrict_of_forall_mem measurableSet_Ico (fun u hu => ?_)
  exact div_nonneg (Nat.cast_nonneg _) (ha.le.trans hu.1)

theorem lower_G (n : ℕ) :
    (n : ℝ) / 4 * (∫ u in Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4), (W n u : ℝ) / u)
        - n - 1 ≤ (H n : ℝ) - G n := by
  obtain ⟨⟨S, hS, hSG⟩, -⟩ := G_spec n
  have hG : (G n : ℝ) = ∑ a ∈ S, (a : ℝ) := by
    rw [← hSG, Nat.cast_sum]
  have hR : 0 ≤ (H n : ℝ) - ∑ a ∈ S, (a : ℝ) + n + 1 := by
    refine le_trans ?_ (LowerAux.sum_bound hS)
    refine Finset.sum_nonneg (fun p _ => ?_)
    have := LowerAux.mv_le hS p
    rw [sub_nonneg]
    exact_mod_cast this
  rw [hG]
  suffices h : (n : ℝ) / 4 *
      (∫ u in Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4), (W n u : ℝ) / u) ≤
        (H n : ℝ) - ∑ a ∈ S, (a : ℝ) + n + 1 by linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hR
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h := lower_bound n S hS
  rw [← ofReal_integral_W n _ _ hs, ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp h

theorem upper_G (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m)) (n : ℕ) :
    (H n : ℝ) - G n ≤
      2 * (n : ℝ) * (∫ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u)
        + (n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) + n := by
  obtain ⟨S, hS, h⟩ := upper_bound n
  have hSG : (∑ a ∈ S, (a : ℝ)) ≤ G n := by
    rw [← Nat.cast_sum]
    exact_mod_cast (G_spec n).2 S hS
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hH : H 0 = 0 := by simp [H]
    simp [hH]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hcongr : (∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), ENNReal.ofReal ((Winf n u : ℝ) / u)) =
      ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), ENNReal.ofReal ((W n u : ℝ) / u) := by
    refine setLIntegral_congr_fun measurableSet_Ico (fun u hu => ?_)
    rw [Winf_eq_W hπ n u hu.1]
  have hX : 0 ≤ ∫ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u :=
    setIntegral_nonneg measurableSet_Ico
      (fun u hu => div_nonneg (Nat.cast_nonneg _) (hs.le.trans hu.1))
  have hc : 0 ≤ (n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) + n := by
    have : 0 ≤ ∑ p ∈ smallPrimes n, (1 : ℝ) / p :=
      Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    positivity
  rw [hcongr, ← ofReal_integral_W n _ _ hs, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) hc, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith

end Erdos879
