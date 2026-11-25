import Erdos879.TwoSided
import Erdos879.Analytic.Bounds
import Erdos879.Analytic.Average

open Finset MeasureTheory

namespace Erdos879

noncomputable def I (n : ℕ) : ℝ :=
  ∫ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), (W n u : ℝ) / u

lemma W_div_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ (W n u : ℝ) / u :=
  div_nonneg (Nat.cast_nonneg _) hu

lemma I_nonneg (n : ℕ) : 0 ≤ I n :=
  setIntegral_nonneg measurableSet_Ico
    (fun _ hu => W_div_nonneg n ((Real.sqrt_nonneg _).trans hu.1))

lemma sqrt_pos_of_three {n : ℕ} (hn : 3 ≤ n) : 0 < Real.sqrt n :=
  Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))

lemma one_le_log_of_three {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  linarith

lemma integral_le_of_lintegral (n : ℕ) {a b R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (h : (∫⁻ u in Set.Ico a b, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal R) :
    (∫ u in Set.Ico a b, (W n u : ℝ) / u) ≤ R := by
  rw [← ofReal_integral_W n a b ha] at h
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp h

lemma integral_mono_Ico (n : ℕ) {a b c : ℝ} (ha : 0 < a) (hbc : b ≤ c) :
    (∫ u in Set.Ico a b, (W n u : ℝ) / u) ≤ ∫ u in Set.Ico a c, (W n u : ℝ) / u := by
  apply setIntegral_mono_set (integrableOn_W n _ _ ha)
  · exact (ae_restrict_iff' measurableSet_Ico).mpr
      (Filter.Eventually.of_forall (fun u hu => W_div_nonneg n (by linarith [hu.1])))
  · exact (Set.Ico_subset_Ico_right hbc).eventuallyLE

lemma outer_I (hS : SelbergMS) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      (∫ u in Set.Ico (2 * Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u)
        ≤ C * (Real.log n) ^ 5 := by
  obtain ⟨C, hC, h⟩ := outer_bound hS
  refine ⟨C, hC, fun n hn => ?_⟩
  exact integral_le_of_lintegral n (by linarith [sqrt_pos_of_three hn])
    (mul_nonneg hC.le (pow_nonneg (Real.log_natCast_nonneg n) _)) (h n hn)

theorem theorem_1_2_i (hS : SelbergMS) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      (∫ u in Set.Ico (2 * Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u) ≤ C * (Real.log n) ^ 5 := by
  obtain ⟨C, -, h⟩ := outer_I hS
  exact ⟨C, h⟩

lemma inner_I (hV : VonKoch) (hS : SelbergMS) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      I n ≤ C * (n : ℝ) ^ (1 / 8 : ℝ) * (Real.log n) ^ (5 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := inner_bound hV hS
  refine ⟨C, hC, fun n hn => ?_⟩
  exact integral_le_of_lintegral n (sqrt_pos_of_three hn)
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Real.log_natCast_nonneg n) _)) (h n hn)

theorem theorem_1_2_ii (hV : VonKoch) (hS : SelbergMS) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      I n ≤ C * (n : ℝ) ^ (1 / 8 : ℝ) * (Real.log n) ^ (5 / 2 : ℝ) := by
  obtain ⟨C, -, h⟩ := inner_I hV hS
  exact ⟨C, h⟩

lemma average_I (hS : SelbergMS) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Ioc N (2 * N), I n) ≤ C * (N : ℝ) * (Real.log N) ^ 5 := by
  obtain ⟨C, hC, h⟩ := average_bound hS
  refine ⟨C, hC, fun N hN => ?_⟩
  have hR : 0 ≤ C * (N : ℝ) * (Real.log N) ^ 5 :=
    mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _)) (pow_nonneg (Real.log_natCast_nonneg N) _)
  have h1 := h N hN
  have h2 : (∑ n ∈ Finset.Ioc N (2 * N),
      ∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u)) =
      ENNReal.ofReal (∑ n ∈ Finset.Ioc N (2 * N), I n) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => I_nonneg n)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [mem_Ioc] at hn
    rw [I, ofReal_integral_W n _ _ (sqrt_pos_of_three (by omega))]
  rw [h2] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp h1

theorem theorem_1_2_iii (hS : SelbergMS) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Ioc N (2 * N), I n) ≤ C * (N : ℝ) * (Real.log N) ^ 5 := by
  obtain ⟨C, -, h⟩ := average_I hS
  exact ⟨C, h⟩

lemma sum_inv_smallPrimes_le (n : ℕ) :
    (∑ p ∈ smallPrimes n, (1 : ℝ) / p) ≤ 1 + Real.log n := by
  have h1 : (∑ p ∈ smallPrimes n, (1 : ℝ) / p) ≤ ∑ i ∈ Finset.Icc 1 n, (i : ℝ)⁻¹ := by
    have hsub : smallPrimes n ⊆ Finset.Icc 1 n := by
      intro p hp
      simp only [smallPrimes, mem_filter, mem_range] at hp
      rw [mem_Icc]
      exact ⟨hp.2.1.one_lt.le, by omega⟩
    simp_rw [one_div]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have h2 := harmonic_le_one_add_log n
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h2
  linarith

lemma split_le (n : ℕ) (hn : 3 ≤ n) :
    (∫ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u) ≤
      I n + ∫ u in Set.Ico (2 * Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u := by
  have hX := sqrt_pos_of_three hn
  have hO : 0 ≤ ∫ u in Set.Ico (2 * Real.sqrt n) ((n : ℝ) / 2), (W n u : ℝ) / u :=
    setIntegral_nonneg measurableSet_Ico (fun u hu => W_div_nonneg n (by linarith [hu.1]))
  rcases le_or_gt (2 * Real.sqrt n) ((n : ℝ) / 2) with h | h
  · rw [I, ← Set.Ico_union_Ico_eq_Ico (show Real.sqrt n ≤ 2 * Real.sqrt n by linarith) h,
      setIntegral_union Set.Ico_disjoint_Ico_same measurableSet_Ico (integrableOn_W n _ _ hX)
        (integrableOn_W n _ _ (by linarith))]
  · have := integral_mono_Ico n hX h.le
    rw [I]
    linarith

lemma upper_I (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m))
    (hS : SelbergMS) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
      (H n : ℝ) - G n ≤ 2 * (n : ℝ) * I n + C * (n : ℝ) * (Real.log n) ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := outer_I hS
  refine ⟨2 * C₁ + 3, by linarith, fun n hn => ?_⟩
  have hU := upper_G hπ n
  have hsplit := split_le n hn
  have hO := h₁ n hn
  have hP := sum_inv_smallPrimes_le n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL := one_le_log_of_three hn
  have hL5 : Real.log n ≤ Real.log n ^ 5 := by
    calc Real.log n = Real.log n ^ 1 := (pow_one _).symm
      _ ≤ Real.log n ^ 5 := pow_le_pow_right₀ hL (by norm_num)
  have hL1 : 1 ≤ Real.log n ^ 5 := one_le_pow₀ hL
  have ha := mul_le_mul_of_nonneg_left (hsplit.trans (add_le_add (le_refl _) hO))
    (by positivity : (0 : ℝ) ≤ 2 * n)
  have hb := mul_le_mul_of_nonneg_left hP hn0
  have hc := mul_le_mul_of_nonneg_left hL5 hn0
  have hd := mul_le_mul_of_nonneg_left hL1 hn0
  linarith

theorem corollary_1_3_a (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m))
    (hS : SelbergMS) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ^ 18 ≤ n →
      (n : ℝ) / 4 * I n - n - 1 ≤ (H n : ℝ) - G n ∧
        (H n : ℝ) - G n ≤ 2 * (n : ℝ) * I n + C * (n : ℝ) * (Real.log n) ^ 5 := by
  obtain ⟨C, -, hU⟩ := upper_I hπ hS
  refine ⟨C, fun n hn => ⟨?_, hU n (by omega)⟩⟩
  have hX := sqrt_pos_of_three (show 3 ≤ n by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h16 : (8 : ℝ) ≤ (n : ℝ) ^ (1 / 6 : ℝ) := by
    have h8 : (8 : ℝ) = ((8 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h8]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have : ((2 ^ 18 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    norm_num at this ⊢
    linarith
  have hsp : (n : ℝ) ^ (2 / 3 : ℝ) = Real.sqrt n * (n : ℝ) ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn']
    norm_num
  have hle : 2 * Real.sqrt n ≤ (n : ℝ) ^ (2 / 3 : ℝ) / 4 := by
    rw [hsp]
    nlinarith [mul_le_mul_of_nonneg_left h16 (Real.sqrt_nonneg (n : ℝ))]
  have hmono := integral_mono_Ico n hX hle
  have hlow := lower_G n
  have h4 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ n / 4)
  rw [← I] at h4
  linarith

lemma log_rpow_le (n : ℕ) :
    Real.log n ^ (5 / 2 : ℝ) ≤ (20 : ℝ) ^ (5 / 2 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
  have h := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 20)
  have h' : Real.log n ≤ 20 * (n : ℝ) ^ (1 / 20 : ℝ) := by
    have e : (n : ℝ) ^ (1 / 20 : ℝ) / (1 / 20) = 20 * (n : ℝ) ^ (1 / 20 : ℝ) := by ring
    linarith
  calc Real.log n ^ (5 / 2 : ℝ) ≤ (20 * (n : ℝ) ^ (1 / 20 : ℝ)) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (Real.log_natCast_nonneg n) h' (by norm_num)
    _ = (20 : ℝ) ^ (5 / 2 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg _),
          show (1 / 20 : ℝ) * (5 / 2) = 1 / 8 by norm_num]

theorem corollary_1_3_b (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m))
    (hV : VonKoch) (hS : SelbergMS) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      (H n : ℝ) - G n ≤ C * (n : ℝ) ^ (9 / 8 : ℝ) * (Real.log n) ^ (5 / 2 : ℝ) := by
  obtain ⟨C₁, hC₁, hU⟩ := upper_I hπ hS
  obtain ⟨C₂, hC₂, hI⟩ := inner_I hV hS
  set K : ℝ := (20 : ℝ) ^ (5 / 2 : ℝ)
  refine ⟨2 * C₂ + C₁ * K, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLpos : 0 < Real.log n := lt_of_lt_of_le one_pos (one_le_log_of_three hn)
  have e1 : Real.log n ^ (5 : ℕ) = Real.log n ^ (5 / 2 : ℝ) * Real.log n ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_natCast]
    norm_num
  have e2 : (n : ℝ) ^ (9 / 8 : ℝ) = n * (n : ℝ) ^ (1 / 8 : ℝ) := by
    rw [show (9 / 8 : ℝ) = 1 + 1 / 8 by norm_num, Real.rpow_add hn', Real.rpow_one]
  have hB : 0 ≤ Real.log n ^ (5 / 2 : ℝ) := Real.rpow_nonneg hLpos.le _
  have h1 := hU n hn
  have h2 := mul_le_mul_of_nonneg_left (hI n hn) (by positivity : (0 : ℝ) ≤ 2 * n)
  have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (log_rpow_le n) hB)
    (mul_nonneg hC₁ hn'.le)
  rw [e2]
  rw [e1] at h1
  linarith

lemma dyadic_mem (N n : ℕ) (hn3 : 3 ≤ n) (hnN : n ≤ N) :
    ∃ k ∈ Finset.range (Nat.log 2 N), n ∈ Finset.Ioc (2 ^ (k + 1)) (2 * 2 ^ (k + 1)) := by
  have hj1 : 1 ≤ Nat.log 2 (n - 1) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hj2 : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
  have hj3 : n - 1 < 2 ^ (Nat.log 2 (n - 1)).succ := Nat.lt_pow_succ_log_self (by norm_num) _
  have hjK : Nat.log 2 (n - 1) ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
  refine ⟨Nat.log 2 (n - 1) - 1, ?_, ?_⟩
  · rw [mem_range]
    omega
  · have e : Nat.log 2 (n - 1) - 1 + 1 = Nat.log 2 (n - 1) := by omega
    rw [e, mem_Ioc, ← pow_succ']
    omega

lemma geom_two (K : ℕ) : (∑ k ∈ Finset.range K, (2 : ℝ) ^ (k + 1)) = 2 ^ (K + 1) - 2 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ, ih]
    ring

lemma geom_le (N : ℕ) : (∑ k ∈ Finset.range (Nat.log 2 N), (2 : ℝ) ^ (k + 1)) ≤ 2 * N := by
  rw [geom_two]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp
  · have h1 := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h2 : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
    push_cast at h2
    rw [pow_succ]
    linarith

lemma block_count (C₃ : ℝ)
    (h : ∀ N : ℕ, 2 ≤ N → (∑ n ∈ Finset.Ioc N (2 * N), I n) ≤ C₃ * (N : ℝ) * (Real.log N) ^ 5)
    (M : ℕ) (hM : 2 ≤ M) (t : ℝ) (ht : 0 < t) :
    (((Finset.Ioc M (2 * M)).filter (fun n : ℕ => t * (Real.log n) ^ 5 < I n)).card : ℝ)
      ≤ C₃ * M / t := by
  set S := (Finset.Ioc M (2 * M)).filter (fun n : ℕ => t * (Real.log n) ^ 5 < I n)
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have h1 : (S.card : ℝ) * (t * (Real.log M) ^ 5) ≤ ∑ n ∈ S, I n := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro n hn
    simp only [S, mem_filter, mem_Ioc] at hn
    have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn.1.1.le
    have h5 : Real.log M ≤ Real.log n := Real.log_le_log (by linarith) hMn
    have h6 : Real.log M ^ 5 ≤ Real.log n ^ 5 := pow_le_pow_left₀ hlogM.le h5 5
    have h7 := mul_le_mul_of_nonneg_left h6 ht.le
    linarith [hn.2]
  have h2 : (∑ n ∈ S, I n) ≤ ∑ n ∈ Finset.Ioc M (2 * M), I n :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => I_nonneg n)
  have h3 := h M hM
  have hL5 : 0 < Real.log M ^ 5 := pow_pos hlogM 5
  rw [le_div_iff₀ ht]
  have h4 : (S.card : ℝ) * t * (Real.log M) ^ 5 ≤ C₃ * M * Real.log M ^ 5 := by
    rw [mul_assoc]
    linarith
  exact le_of_mul_le_mul_right h4 hL5

lemma count_le (hS : SelbergMS) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ t : ℝ, 0 < t →
      (((Finset.Icc 3 N).filter (fun n : ℕ => t * (Real.log n) ^ 5 < I n)).card : ℝ)
        ≤ C * N / t := by
  obtain ⟨C₃, hC₃, h⟩ := average_I hS
  refine ⟨2 * C₃, by linarith, fun N t ht => ?_⟩
  classical
  set F : ℕ → Finset ℕ := fun k =>
    (Finset.Ioc (2 ^ (k + 1)) (2 * 2 ^ (k + 1))).filter (fun n : ℕ => t * (Real.log n) ^ 5 < I n)
  have hsub : (Finset.Icc 3 N).filter (fun n : ℕ => t * (Real.log n) ^ 5 < I n) ⊆
      (Finset.range (Nat.log 2 N)).biUnion F := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    obtain ⟨k, hk, hnk⟩ := dyadic_mem N n hn.1.1 hn.1.2
    rw [mem_biUnion]
    exact ⟨k, hk, mem_filter.mpr ⟨hnk, hn.2⟩⟩
  have hc1 : (((Finset.Icc 3 N).filter (fun n : ℕ => t * (Real.log n) ^ 5 < I n)).card : ℝ) ≤
      ∑ k ∈ Finset.range (Nat.log 2 N), ((F k).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have hc2 : ∀ k ∈ Finset.range (Nat.log 2 N), ((F k).card : ℝ) ≤ C₃ * (2 : ℝ) ^ (k + 1) / t := by
    intro k _
    have hk : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := block_count C₃ h (2 ^ (k + 1)) hk t ht
    push_cast at this
    exact this
  calc _ ≤ ∑ k ∈ Finset.range (Nat.log 2 N), ((F k).card : ℝ) := hc1
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 N), C₃ * (2 : ℝ) ^ (k + 1) / t := sum_le_sum hc2
    _ = C₃ * (∑ k ∈ Finset.range (Nat.log 2 N), (2 : ℝ) ^ (k + 1)) / t := by
        rw [← sum_div, ← mul_sum]
    _ ≤ C₃ * (2 * N) / t := by
        gcongr
        exact geom_le N
    _ = 2 * C₃ * N / t := by ring

theorem corollary_1_3_c (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m))
    (hS : SelbergMS) :
    ∃ C : ℝ, ∀ N : ℕ, ∀ lam : ℝ, 1 ≤ lam →
      (((Finset.Icc 3 N).filter
        (fun n : ℕ => lam * (n : ℝ) * (Real.log n) ^ 5 < (H n : ℝ) - G n)).card : ℝ)
        ≤ C * (N : ℝ) / lam := by
  obtain ⟨C₁, hC₁, hU⟩ := upper_I hπ hS
  obtain ⟨C₃, hC₃, hD⟩ := count_le hS
  refine ⟨2 * C₁ + 4 * C₃, fun N lam hlam => ?_⟩
  have hlam0 : 0 < lam := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [le_div_iff₀ hlam0]
  rcases le_or_gt lam (2 * C₁) with hl | hl
  · have hc : ((Finset.Icc 3 N).filter
        (fun n : ℕ => lam * (n : ℝ) * (Real.log n) ^ 5 < (H n : ℝ) - G n)).card ≤ N := by
      refine (card_filter_le _ _).trans ?_
      rw [Nat.card_Icc]
      omega
    have hc' : (((Finset.Icc 3 N).filter
        (fun n : ℕ => lam * (n : ℝ) * (Real.log n) ^ 5 < (H n : ℝ) - G n)).card : ℝ) ≤ N := by
      exact_mod_cast hc
    have h1 := mul_le_mul_of_nonneg_right hc' hlam0.le
    have h2 := mul_le_mul_of_nonneg_left hl hN0
    have h3 : 0 ≤ C₃ * N := mul_nonneg hC₃.le hN0
    linarith
  · have hsub : (Finset.Icc 3 N).filter
        (fun n : ℕ => lam * (n : ℝ) * (Real.log n) ^ 5 < (H n : ℝ) - G n) ⊆
        (Finset.Icc 3 N).filter (fun n : ℕ => lam / 4 * (Real.log n) ^ 5 < I n) := by
      intro n hn
      rw [mem_filter, mem_Icc] at hn ⊢
      refine ⟨hn.1, ?_⟩
      have h1 := hU n hn.1.1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hL : 0 ≤ (n : ℝ) * Real.log n ^ 5 :=
        mul_nonneg hn0.le (pow_nonneg (Real.log_natCast_nonneg n) _)
      have h2 := mul_le_mul_of_nonneg_right hl.le hL
      have h3 : (n : ℝ) * (lam / 4 * Real.log n ^ 5) < (n : ℝ) * I n := by
        linarith [hn.2]
      exact lt_of_mul_lt_mul_left h3 hn0.le
    have hc : (((Finset.Icc 3 N).filter
        (fun n : ℕ => lam * (n : ℝ) * (Real.log n) ^ 5 < (H n : ℝ) - G n)).card : ℝ) ≤
        (((Finset.Icc 3 N).filter (fun n : ℕ => lam / 4 * (Real.log n) ^ 5 < I n)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have h4 := hD N (lam / 4) (by linarith)
    rw [le_div_iff₀ (by linarith)] at h4
    have h5 : 0 ≤ C₁ * N := mul_nonneg hC₁ hN0
    have h6 := mul_le_mul_of_nonneg_right hc hlam0.le
    linarith

theorem corollary_1_3_c' (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m))
    (hS : SelbergMS) :
    ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N →
      (((Finset.Icc 3 N).filter
        (fun n : ℕ => (n : ℝ) * (Real.log n) ^ 6 < (H n : ℝ) - G n)).card : ℝ)
        ≤ C * (N : ℝ) / Real.log N := by
  obtain ⟨C₁, hC₁, hU⟩ := upper_I hπ hS
  obtain ⟨C₃, hC₃, hD⟩ := count_le hS
  set B : ℕ := ⌊Real.exp (2 * C₁)⌋₊ + 1
  refine ⟨3 + B + 8 * C₃, fun N hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogle : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  rw [le_div_iff₀ hlogN]
  have hsub : (Finset.Icc 3 N).filter
      (fun n : ℕ => (n : ℝ) * (Real.log n) ^ 6 < (H n : ℝ) - G n) ⊆
      (Finset.range (Nat.sqrt N + 1) ∪ Finset.range B) ∪
        (Finset.Icc 3 N).filter (fun n : ℕ => Real.log N / 8 * (Real.log n) ^ 5 < I n) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    rw [mem_union, mem_union, mem_range, mem_range, mem_filter, mem_Icc]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    by_cases h1 : n ≤ Nat.sqrt N
    · left; left; omega
    by_cases h2 : Real.log n < 2 * C₁
    · left; right
      have h3 : (n : ℝ) < Real.exp (2 * C₁) := (Real.log_lt_iff_lt_exp hn0).mp h2
      have h4 : n ≤ ⌊Real.exp (2 * C₁)⌋₊ := Nat.le_floor h3.le
      omega
    right
    refine ⟨hn.1, ?_⟩
    rw [not_le] at h1
    rw [not_lt] at h2
    have hNn : N < n * n := Nat.sqrt_lt.mp h1
    have hNn' : (N : ℝ) < (n : ℝ) * n := by exact_mod_cast hNn
    have hlog2 : Real.log N < 2 * Real.log n := by
      have := Real.log_lt_log (by linarith) hNn'
      rw [Real.log_mul hn0.ne' hn0.ne'] at this
      linarith
    have hL5 : 0 ≤ Real.log n ^ 5 := pow_nonneg (Real.log_natCast_nonneg n) _
    have h3 : (n : ℝ) * (Real.log n ^ 6) < (n : ℝ) * (2 * I n + C₁ * Real.log n ^ 5) := by
      have := hU n hn.1.1
      linarith [hn.2]
    have h4 := lt_of_mul_lt_mul_left h3 hn0.le
    have h5 := mul_le_mul_of_nonneg_right (show C₁ ≤ Real.log n / 2 by linarith) hL5
    have h6 := mul_le_mul_of_nonneg_right (show Real.log N / 4 ≤ Real.log n / 2 by linarith) hL5
    have e : Real.log n ^ 6 = Real.log n * Real.log n ^ 5 := by ring
    linarith
  have hc : (((Finset.Icc 3 N).filter
      (fun n : ℕ => (n : ℝ) * (Real.log n) ^ 6 < (H n : ℝ) - G n)).card : ℝ) ≤
      (Nat.sqrt N + 1 : ℝ) + B +
        (((Finset.Icc 3 N).filter (fun n : ℕ => Real.log N / 8 * (Real.log n) ^ 5 < I n)).card : ℝ) := by
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 := card_union_le (Finset.range (Nat.sqrt N + 1)) (Finset.range B)
    rw [card_range, card_range] at h2
    have h3 : ((Finset.Icc 3 N).filter
        (fun n : ℕ => (n : ℝ) * (Real.log n) ^ 6 < (H n : ℝ) - G n)).card ≤
        Nat.sqrt N + 1 + B +
          ((Finset.Icc 3 N).filter (fun n : ℕ => Real.log N / 8 * (Real.log n) ^ 5 < I n)).card := by
      omega
    exact_mod_cast h3
  have hQ := hD N (Real.log N / 8) (by linarith)
  rw [le_div_iff₀ (by linarith)] at hQ
  have hsq : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hlogsq : Real.log N ≤ 2 * Real.sqrt N := by
    have h := Real.log_le_rpow_div (Nat.cast_nonneg N) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    have e : Real.sqrt N / (1 / 2) = 2 * Real.sqrt N := by ring
    linarith
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have h1 := mul_le_mul_of_nonneg_right hc hlogN.le
  have h2 := mul_le_mul_of_nonneg_right hsq hlogN.le
  have h3 := mul_le_mul_of_nonneg_left hlogsq (Real.sqrt_nonneg (N : ℝ))
  have h4 := mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  linarith

end Erdos879
