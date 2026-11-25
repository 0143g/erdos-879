import Erdos879.Analytic.Excess
import Erdos879.Analytic.Chain
import Erdos879.Analytic.MeanSquare
import Erdos879.Measurable

open Finset MeasureTheory

namespace Erdos879

lemma avg_card_le (n : ℕ) : ((smallPrimes n).card : ℝ) ≤ Real.sqrt n := by
  have h : smallPrimes n ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro p hp
    simp only [smallPrimes, Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_Icc]
    exact ⟨hp.2.1.one_lt.le, Nat.le_sqrt.mpr hp.2.2⟩
  have := Finset.card_le_card h
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
  calc ((smallPrimes n).card : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast this
    _ ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt

lemma avg_W_div_le_one (n : ℕ) (u : ℝ) (hu : Real.sqrt n ≤ u) : (W n u : ℝ) / u ≤ 1 := by
  have h1 : (W n u : ℝ) ≤ (smallPrimes n).card := by exact_mod_cast W_le_card n u
  exact div_le_one_of_le₀ (h1.trans ((avg_card_le n).trans hu)) ((Real.sqrt_nonneg _).trans hu)

lemma avg_scale (c : ℝ) (hc : 0 < c) (s : Set ℝ) (hs : MeasurableSet s) (g : ℝ → ENNReal) :
    ∫⁻ x in (fun x => c * x) '' s, g x = ENNReal.ofReal c * ∫⁻ z in s, g (c * z) := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hs (f' := fun _ => c)]
  · rw [abs_of_pos hc, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · intro x _
    simpa using ((hasDerivAt_id x).const_mul c).hasDerivWithinAt
  · intro x _ y _ h
    exact mul_left_cancel₀ hc.ne' h

lemma avg_lint_inv (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∫⁻ z in Set.Ico (1 + η) 2, ENNReal.ofReal (1 / (z - 1)) ≤ ENNReal.ofReal (Real.log (1 / η)) := by
  have hcont : ContinuousOn (fun z : ℝ => 1 / (z - 1)) (Set.Icc (1 + η) 2) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro x hx
    have := hx.1
    show x - 1 ≠ 0
    linarith
  have hint : IntegrableOn (fun z : ℝ => 1 / (z - 1)) (Set.Ioc (1 + η) 2) :=
    (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  calc ∫⁻ z in Set.Ico (1 + η) 2, ENNReal.ofReal (1 / (z - 1))
      ≤ ∫⁻ z in Set.Icc (1 + η) 2, ENNReal.ofReal (1 / (z - 1)) :=
        lintegral_mono_set Set.Ico_subset_Icc_self
    _ = ∫⁻ z in Set.Ioc (1 + η) 2, ENNReal.ofReal (1 / (z - 1)) :=
        setLIntegral_congr Ioc_ae_eq_Icc.symm
    _ = ENNReal.ofReal (∫ z in Set.Ioc (1 + η) 2, 1 / (z - 1)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
        have := hz.1
        apply div_nonneg zero_le_one
        linarith
    _ = ENNReal.ofReal (Real.log (1 / η)) := by
        rw [← intervalIntegral.integral_of_le (by linarith)]
        have h := intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x) (a := 1 + η) (b := 2) 1
        rw [h, integral_one_div_of_pos (by linarith) (by linarith)]
        congr 2
        ring

lemma avg_exp_two_lt : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

lemma avg_rr_pos (i : ℕ) : 0 < rr i := by unfold rr; positivity

lemma avg_rr_le (i : ℕ) : rr i ≤ 2 := by
  unfold rr
  have : (1:ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

noncomputable def avgM (N : ℕ) : ℕ := ⌈Real.logb 2 (Real.sqrt N)⌉₊ + 3

lemma avg_pow_M (N : ℕ) (hN : 1 ≤ N) :
    8 * Real.sqrt N ≤ (2:ℝ) ^ avgM N ∧ (2:ℝ) ^ avgM N < 16 * Real.sqrt N := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN'
  have hs : 0 < Real.sqrt N := by linarith
  have hl : 0 ≤ Real.logb 2 (Real.sqrt N) := Real.logb_nonneg (by norm_num) hs1
  have h1 : Real.sqrt N ≤ (2:ℝ) ^ ⌈Real.logb 2 (Real.sqrt N)⌉₊ := by
    have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
      (Nat.le_ceil (Real.logb 2 (Real.sqrt N)))
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hs, Real.rpow_natCast] at this
  have h2 : (2:ℝ) ^ ⌈Real.logb 2 (Real.sqrt N)⌉₊ < 2 * Real.sqrt N := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (Nat.ceil_lt_add_one hl)
    rwa [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hs,
      Real.rpow_natCast, Real.rpow_one, mul_comm] at this
  unfold avgM
  rw [pow_add]
  constructor <;> nlinarith

lemma avg_M_le (N : ℕ) (hN : 1 ≤ N) (hL : 12 ≤ Real.log N) : ((avgM N : ℕ) : ℝ) + 1 ≤ 2 * Real.log N := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN'
  have hl : 0 ≤ Real.logb 2 (Real.sqrt N) := Real.logb_nonneg (by norm_num) hs1
  have h1 := Nat.ceil_lt_add_one hl
  have h2 : Real.logb 2 (Real.sqrt N) = Real.log N / 2 / Real.log 2 := by
    rw [Real.logb, Real.log_sqrt (by positivity)]
  have hl2 := Real.log_two_gt_d9
  have h3 : Real.log N / 2 / Real.log 2 ≤ Real.log N := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  unfold avgM
  push_cast
  linarith


lemma avg_exp_neg_ge (s : ℝ) (hs : s ≤ 2) : 1 / 8 ≤ Real.exp (-s) := by
  have h := avg_exp_two_lt
  have h2 : Real.exp (-2) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-2) = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
  have h4 : 1 / 8 ≤ 1 / Real.exp 2 := one_div_le_one_div_of_le (Real.exp_pos 2) h.le
  linarith

lemma avg_shift (a b c : ℝ) (hab0 : 0 ≤ b - a) (hab : b - a ≤ 1 / 60) (hc0 : 0 < c)
    (hc : c ≤ 8) : |a * c - b * c| ≤ 1 := by
  rw [← sub_mul, abs_mul, abs_of_pos hc0, abs_sub_comm, abs_of_nonneg hab0]
  nlinarith

lemma avg_tri (a b c d M : ℝ) (h1 : |E a - E b| ≤ 3) (h2 : |E b - E c| ≤ M)
    (h3 : |E c - E d| ≤ 3) : |E a - E d| ≤ M + 6 := by
  have := abs_sub_le (E a) (E b) (E d)
  have := abs_sub_le (E b) (E c) (E d)
  linarith

lemma avg_Mp (r : ℝ) (k : ℕ) (hr : r ≤ 2) (u y s : ℝ) (hu : 2 ≤ u) (hyu0 : 0 ≤ y - u)
    (hyu1 : y - u ≤ 1 / 60) (hs0 : 0 ≤ s) (hs : s ≤ r) :
    |E (u * Real.exp s) - E u| ≤ Bp r k y / Real.log y + 6 := by
  have hes1 : 1 ≤ Real.exp s := Real.one_le_exp hs0
  have hes8 : Real.exp s ≤ 8 :=
    (Real.exp_le_exp.mpr (hs.trans hr)).trans avg_exp_two_lt.le
  have hy : 2 ≤ y := by linarith
  have h1 : |E (u * Real.exp s) - E (y * Real.exp s)| ≤ 3 :=
    abs_E_sub_le_three _ _ (by nlinarith) (by nlinarith)
      (avg_shift u y _ hyu0 hyu1 (Real.exp_pos s) hes8)
  have h2 : |E (y * Real.exp s) - E y| ≤ Bp r k y / Real.log y :=
    abs_E_exp_sub_le _ _ _ _ hy hs0 hs
  have h3 : |E y - E u| ≤ 3 :=
    abs_E_sub_le_three _ _ hy hu (by rw [abs_le]; constructor <;> linarith)
  exact avg_tri _ _ _ _ _ h1 h2 h3

lemma avg_Mm (r : ℝ) (k : ℕ) (hr : r ≤ 2) (a y s : ℝ) (ha : 30 ≤ a) (h0 : 0 ≤ y - a)
    (h1 : y - a ≤ 1 / 60) (hs0 : 0 ≤ s) (hs : s ≤ r) :
    |E (a * Real.exp (-s)) - E a| ≤ 2 * Bm r k y / Real.log (y * Real.exp (-r)) + 6 := by
  have hes1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hes8 : 1 / 8 ≤ Real.exp (-s) := avg_exp_neg_ge s (hs.trans hr)
  have hr8 : 1 / 8 ≤ Real.exp (-r) := avg_exp_neg_ge _ hr
  have hy : 30 ≤ y := by linarith
  have h1' : |E (a * Real.exp (-s)) - E (y * Real.exp (-s))| ≤ 3 :=
    abs_E_sub_le_three _ _ (by nlinarith) (by nlinarith)
      (avg_shift a y _ h0 h1 (Real.exp_pos _) (by linarith))
  have h2 : |E (y * Real.exp (-s)) - E y| ≤ 2 * Bm r k y / Real.log (y * Real.exp (-r)) :=
    abs_E_exp_neg_sub_le _ _ _ _ (by nlinarith) hs0 hs
  have h3 : |E y - E a| ≤ 3 :=
    abs_E_sub_le_three _ _ (by linarith) (by linarith)
      (by rw [abs_le]; constructor <;> linarith)
  exact avg_tri _ _ _ _ _ h1' h2 h3

lemma avg_term (P Q ly lm L b r z sN : ℝ) (hL : 0 < L) (hly : L / 2 ≤ ly) (hlm : L / 4 ≤ lm)
    (hr : 0 < r) (hz : 1 < z) (hsN : 0 < sN) (hb : r * (z - 1) * sN / (4 * L) ≤ b) :
    (P / ly + 6 + (2 * Q / lm + 6)) ^ 2 / (4 * b) ≤
      2 * L / (r * (z - 1) * sN) * (8 * P ^ 2 / L ^ 2 + 128 * Q ^ 2 / L ^ 2 + 144) := by
  have hly0 : 0 < ly := by linarith
  have hlm0 : 0 < lm := by linarith
  have hA : (P / ly) ^ 2 ≤ 4 * P ^ 2 / L ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : L ^ 2 ≤ 4 * ly ^ 2 := by nlinarith
    nlinarith [sq_nonneg P]
  have hB : (2 * Q / lm) ^ 2 ≤ 64 * Q ^ 2 / L ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : L ^ 2 ≤ 16 * lm ^ 2 := by nlinarith
    nlinarith [sq_nonneg Q]
  have hX : (P / ly + 6 + (2 * Q / lm + 6)) ^ 2 ≤
      2 * (8 * P ^ 2 / L ^ 2 + 128 * Q ^ 2 / L ^ 2 + 144) := by
    generalize P / ly = a at hA ⊢
    generalize 2 * Q / lm = c at hB ⊢
    have h1 : (a + 6 + (c + 6)) ^ 2 ≤ 4 * a ^ 2 + 4 * c ^ 2 + 288 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (a - 6), sq_nonneg (c - 6)]
    have e : 2 * (8 * P ^ 2 / L ^ 2 + 128 * Q ^ 2 / L ^ 2 + 144) =
        4 * (4 * P ^ 2 / L ^ 2) + 4 * (64 * Q ^ 2 / L ^ 2) + 288 := by ring
    rw [e]
    linarith
  have hz10 : 0 < z - 1 := by linarith
  have hb0 : 0 < r * (z - 1) * sN / (4 * L) :=
    div_pos (mul_pos (mul_pos hr hz10) hsN) (by linarith)
  calc (P / ly + 6 + (2 * Q / lm + 6)) ^ 2 / (4 * b)
      ≤ 2 * (8 * P ^ 2 / L ^ 2 + 128 * Q ^ 2 / L ^ 2 + 144) /
        (4 * (r * (z - 1) * sN / (4 * L))) :=
        div_le_div₀ (by positivity) hX (by linarith) (by linarith)
    _ = 2 * L / (r * (z - 1) * sN) * (8 * P ^ 2 / L ^ 2 + 128 * Q ^ 2 / L ^ 2 + 144) := by
        field_simp

lemma avg_bfun (N n : ℕ) (hN : 3600 ≤ N) (hn1 : N < n)
    (hn2 : n ≤ 2 * N) (z : ℝ) (hz1 : 1 < z) (r : ℝ) (hr : 0 < r) :
    r * (z - 1) * Real.sqrt N / (4 * Real.log N) ≤ bfun n r (Real.sqrt n * z) := by
  have hN0 : (3600 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) < n := by exact_mod_cast hn1
  have hn20 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn2
  have hsNn : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt hn0.le
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hlogn : Real.log n ≤ 2 * Real.log N := by
    have h : Real.log ((N : ℝ) ^ 2) = 2 * Real.log N := by rw [Real.log_pow]; norm_num
    rw [← h]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hlogn0 : 0 < Real.log n := Real.log_pos (by linarith)
  unfold bfun
  have h1 : r / (4 * Real.log N) ≤ r / (2 * Real.log n) :=
    div_le_div_of_nonneg_left hr.le (by positivity) (by linarith)
  have h2 : (z - 1) * Real.sqrt N ≤ Real.sqrt n * z - Real.sqrt n + Real.sqrt n * r / 4 := by
    have : 0 ≤ Real.sqrt n * r / 4 := by positivity
    nlinarith
  calc r * (z - 1) * Real.sqrt N / (4 * Real.log N)
      = r / (4 * Real.log N) * ((z - 1) * Real.sqrt N) := by ring
    _ ≤ r / (2 * Real.log n) * (Real.sqrt n * z - Real.sqrt n + Real.sqrt n * r / 4) :=
        mul_le_mul h1 h2 (mul_nonneg (by linarith) hsN0) (by positivity)

noncomputable def avgβ (N : ℕ) (z : ℝ) (i : ℕ) : ℝ :=
  2 * Real.log N / (rr i * (z - 1) * Real.sqrt N)

lemma avg_pointwise (N n : ℕ) (hN : 3600 ≤ N) (hL : 12 ≤ Real.log N) (hn1 : N < n)
    (hn2 : n ≤ 2 * N) (z : ℝ) (hz1 : 1 < z) (hz2 : z ≤ 2) (y : ℝ) (hy1 : Real.sqrt n * z ≤ y)
    (hy2 : y ≤ Real.sqrt n * z + 1 / Real.sqrt N) :
    (W n (Real.sqrt n * z) : ℝ) - 2 ≤
      ∑ i ∈ range (avgM N + 1), avgβ N z i *
        (8 * (Bp (rr i) (kOf (Real.sqrt N * z) (rr i)) y) ^ 2 / (Real.log N) ^ 2
        + 128 * (Bm (rr i) (kOf (Real.sqrt N / z) (rr i)) (y / z ^ 2)) ^ 2 / (Real.log N) ^ 2
        + 144) := by
  have hN0 : (3600 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) < n := by exact_mod_cast hn1
  have hn20 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn2
  have hsqn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsn0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsN : 60 ≤ Real.sqrt N := by nlinarith
  have hsNpos : 0 < Real.sqrt N := by linarith
  have hsNn : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt hn0.le
  have hn1' : 1 ≤ n := by omega
  have hz0 : 0 < z := by linarith
  have hu1 : Real.sqrt n ≤ Real.sqrt n * z := le_mul_of_one_le_right hsn0 hz1.le
  have hu2 : Real.sqrt n * z ≤ 2 * Real.sqrt n := by nlinarith
  have hun : 30 * (Real.sqrt n * z) ≤ n := by nlinarith
  have hinvN : 1 / Real.sqrt N ≤ 1 / 60 := one_div_le_one_div_of_le (by norm_num) hsN
  have hyu0 : 0 ≤ y - Real.sqrt n * z := by linarith
  have hyu1 : y - Real.sqrt n * z ≤ 1 / 60 := by linarith
  have hnu : (n : ℝ) / (Real.sqrt n * z) = Real.sqrt n / z := by
    rw [div_eq_div_iff (by positivity) hz0.ne']
    linear_combination (-z) * hsqn
  have hy'a : y / z ^ 2 - Real.sqrt n / z = (y - Real.sqrt n * z) / z ^ 2 := by
    field_simp
  have hz2' : 1 ≤ z ^ 2 := by nlinarith
  have hy'0 : 0 ≤ y / z ^ 2 - Real.sqrt n / z := by rw [hy'a]; positivity
  have hy'1 : y / z ^ 2 - Real.sqrt n / z ≤ 1 / 60 := by
    rw [hy'a, div_le_iff₀ (by positivity)]
    nlinarith
  have hnz : Real.sqrt n / 2 ≤ Real.sqrt n / z :=
    div_le_div_of_nonneg_left hsn0 hz0 hz2
  have hlogsN : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt (Nat.cast_nonneg N)
  have hly : Real.log N / 2 ≤ Real.log y := by
    rw [← hlogsN]
    exact Real.log_le_log hsNpos (by linarith)
  have hlog2 := Real.log_two_lt_d9
  have hly' : ∀ r : ℝ, r ≤ 2 → Real.log N / 4 ≤ Real.log (y / z ^ 2 * Real.exp (-r)) := by
    intro r hr
    have hy'pos : 0 < y / z ^ 2 := by linarith
    rw [Real.log_mul hy'pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have : Real.log (Real.sqrt N / 2) ≤ Real.log (y / z ^ 2) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num), hlogsN] at this
    linarith
  have hM : 2 * (Real.sqrt n * z) ≤ 2 ^ avgM N := by
    have h := (avg_pow_M N (by omega)).1
    have : Real.sqrt n ≤ 2 * Real.sqrt N := by nlinarith
    linarith
  have hexcess := excess n hn1' (Real.sqrt n * z) hu1 hun (avgM N) hM
    (fun i => Bp (rr i) (kOf (Real.sqrt N * z) (rr i)) y / Real.log y + 6)
    (fun i => 2 * Bm (rr i) (kOf (Real.sqrt N / z) (rr i)) (y / z ^ 2) /
      Real.log (y / z ^ 2 * Real.exp (-(rr i))) + 6)
    (fun i _ s hs0 hs => avg_Mp (rr i) _ (avg_rr_le i) _ y s (by linarith) hyu0 hyu1 hs0 hs)
    (fun i _ s hs0 hs => by
      rw [hnu]
      exact avg_Mm (rr i) _ (avg_rr_le i) _ _ s (by linarith) hy'0 hy'1 hs0 hs)
  have hL0 : 0 < Real.log N := by linarith
  have hterm : ∀ i ∈ range (avgM N + 1),
      (Bp (rr i) (kOf (Real.sqrt N * z) (rr i)) y / Real.log y + 6 +
        (2 * Bm (rr i) (kOf (Real.sqrt N / z) (rr i)) (y / z ^ 2) /
          Real.log (y / z ^ 2 * Real.exp (-(rr i))) + 6)) ^ 2 /
        (4 * bfun n (rr i) (Real.sqrt n * z)) ≤
      avgβ N z i * (8 * (Bp (rr i) (kOf (Real.sqrt N * z) (rr i)) y) ^ 2 / (Real.log N) ^ 2
        + 128 * (Bm (rr i) (kOf (Real.sqrt N / z) (rr i)) (y / z ^ 2)) ^ 2 / (Real.log N) ^ 2
        + 144) := fun i _ =>
    avg_term _ _ _ _ _ _ _ _ _ hL0 hly (hly' _ (avg_rr_le i)) (avg_rr_pos i) hz1 hsNpos
      (avg_bfun N n hN hn1 hn2 z hz1 _ (avg_rr_pos i))
  have hsum := Finset.sum_le_sum hterm
  linarith [hexcess, hsum]

lemma avg_ofReal3 (a b c x y w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hw : 0 ≤ w) :
    ENNReal.ofReal (a * x + b * y + c * w) =
      ENNReal.ofReal a * ENNReal.ofReal x + ENNReal.ofReal b * ENNReal.ofReal y +
        ENNReal.ofReal c * ENNReal.ofReal w := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb, ENNReal.ofReal_mul hc]

lemma avg_G_int (Cp Zp₀ Cm Zm₀ : ℝ)
    (hp : ∀ Z : ℝ, Zp₀ ≤ Z → ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bp r (kOf Z r) y) ^ 2)
        ≤ ENNReal.ofReal (Cp * Z * (1 + Z * r) * (Real.log Z) ^ 4))
    (hm : ∀ Z : ℝ, Zm₀ ≤ Z → ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bm r (kOf Z r) y) ^ 2)
        ≤ ENNReal.ofReal (Cm * Z * (1 + Z * r) * (Real.log Z) ^ 4))
    (hCp : 0 < Cp) (hCm : 0 < Cm)
    (M : ℕ) (β : ℕ → ℝ) (hβ : ∀ i, 0 ≤ β i) (L z Zp Zm : ℝ) (hz : 0 < z) (hZm0 : 0 < Zm)
    (hzZ : z ^ 2 * Zm = Zp) (hZp₀ : Zp₀ ≤ Zp) (hZm₀ : Zm₀ ≤ Zm) :
    ∫⁻ y in Set.Icc Zp (2 * Zp), ENNReal.ofReal (∑ i ∈ range (M + 1), β i *
        (8 * (Bp (rr i) (kOf Zp (rr i)) y) ^ 2 / L ^ 2
        + 128 * (Bm (rr i) (kOf Zm (rr i)) (y / z ^ 2)) ^ 2 / L ^ 2 + 144))
      ≤ ENNReal.ofReal (∑ i ∈ range (M + 1), β i *
        (8 * (Cp * Zp * (1 + Zp * rr i) * (Real.log Zp) ^ 4) / L ^ 2
        + 128 * (z ^ 2 * (Cm * Zm * (1 + Zm * rr i) * (Real.log Zm) ^ 4)) / L ^ 2
        + 144 * Zp)) := by
  have hZp0 : 0 < Zp := by rw [← hzZ]; positivity
  have hz2 : 0 < z ^ 2 := by positivity
  have ha : ∀ i, 0 ≤ β i * 8 / L ^ 2 := fun i =>
    div_nonneg (mul_nonneg (hβ i) (by norm_num)) (sq_nonneg L)
  have hb : ∀ i, 0 ≤ β i * 128 / L ^ 2 := fun i =>
    div_nonneg (mul_nonneg (hβ i) (by norm_num)) (sq_nonneg L)
  have hc : ∀ i, 0 ≤ β i * 144 := fun i => mul_nonneg (hβ i) (by norm_num)
  have hrw : ∀ y, ENNReal.ofReal (∑ i ∈ range (M + 1), β i *
        (8 * (Bp (rr i) (kOf Zp (rr i)) y) ^ 2 / L ^ 2
        + 128 * (Bm (rr i) (kOf Zm (rr i)) (y / z ^ 2)) ^ 2 / L ^ 2 + 144)) =
      ∑ i ∈ range (M + 1), (ENNReal.ofReal (β i * 8 / L ^ 2) *
          ENNReal.ofReal ((Bp (rr i) (kOf Zp (rr i)) y) ^ 2)
        + ENNReal.ofReal (β i * 128 / L ^ 2) *
          ENNReal.ofReal ((Bm (rr i) (kOf Zm (rr i)) (y / z ^ 2)) ^ 2)
        + ENNReal.ofReal (β i * 144) * ENNReal.ofReal 1) := by
    intro y
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hβ i) (by positivity))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← avg_ofReal3 _ _ _ _ _ _ (ha i) (hb i) (hc i) (sq_nonneg _) (sq_nonneg _) zero_le_one]
    congr 1
    ring
  have hRpos : ∀ i, 0 ≤ Cp * Zp * (1 + Zp * rr i) * (Real.log Zp) ^ 4 := fun i => by
    have := avg_rr_pos i
    positivity
  have hRpos' : ∀ i, 0 ≤ z ^ 2 * (Cm * Zm * (1 + Zm * rr i) * (Real.log Zm) ^ 4) := fun i => by
    have := avg_rr_pos i
    positivity
  have hrw2 : ENNReal.ofReal (∑ i ∈ range (M + 1), β i *
        (8 * (Cp * Zp * (1 + Zp * rr i) * (Real.log Zp) ^ 4) / L ^ 2
        + 128 * (z ^ 2 * (Cm * Zm * (1 + Zm * rr i) * (Real.log Zm) ^ 4)) / L ^ 2
        + 144 * Zp)) =
      ∑ i ∈ range (M + 1), (ENNReal.ofReal (β i * 8 / L ^ 2) *
          ENNReal.ofReal (Cp * Zp * (1 + Zp * rr i) * (Real.log Zp) ^ 4)
        + ENNReal.ofReal (β i * 128 / L ^ 2) *
          (ENNReal.ofReal (z ^ 2) * ENNReal.ofReal (Cm * Zm * (1 + Zm * rr i) * (Real.log Zm) ^ 4))
        + ENNReal.ofReal (β i * 144) * ENNReal.ofReal Zp) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hβ i) (by
      have := hRpos i
      have := hRpos' i
      positivity))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← ENNReal.ofReal_mul hz2.le,
      ← avg_ofReal3 _ _ _ _ _ _ (ha i) (hb i) (hc i) (hRpos i) (hRpos' i) hZp0.le]
    congr 1
    ring
  have h1 : ∀ i, Measurable (fun y : ℝ => ENNReal.ofReal (β i * 8 / L ^ 2) *
      ENNReal.ofReal ((Bp (rr i) (kOf Zp (rr i)) y) ^ 2)) := fun i =>
    (((measurable_Bp _ _).pow_const 2).ennreal_ofReal).const_mul _
  have h2 : ∀ i, Measurable (fun y : ℝ => ENNReal.ofReal (β i * 128 / L ^ 2) *
      ENNReal.ofReal ((Bm (rr i) (kOf Zm (rr i)) (y / z ^ 2)) ^ 2)) := fun i =>
    ((((measurable_Bm _ _).comp (measurable_id.div_const _)).pow_const 2).ennreal_ofReal).const_mul _
  have hmeas : ∀ i ∈ range (M + 1), Measurable (fun y : ℝ =>
      ENNReal.ofReal (β i * 8 / L ^ 2) * ENNReal.ofReal ((Bp (rr i) (kOf Zp (rr i)) y) ^ 2)
        + ENNReal.ofReal (β i * 128 / L ^ 2) *
          ENNReal.ofReal ((Bm (rr i) (kOf Zm (rr i)) (y / z ^ 2)) ^ 2)
        + ENNReal.ofReal (β i * 144) * ENNReal.ofReal 1) := fun i _ =>
    ((h1 i).add (h2 i)).add measurable_const
  rw [lintegral_congr hrw, hrw2, lintegral_finsetSum _ hmeas]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [lintegral_add_right _ measurable_const, lintegral_add_left (h1 i),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_one, mul_one]
  have hQ : ∫⁻ y in Set.Icc Zp (2 * Zp),
      ENNReal.ofReal ((Bm (rr i) (kOf Zm (rr i)) (y / z ^ 2)) ^ 2) =
      ENNReal.ofReal (z ^ 2) *
        ∫⁻ w in Set.Icc Zm (2 * Zm), ENNReal.ofReal ((Bm (rr i) (kOf Zm (rr i)) w) ^ 2) := by
    have himg : (fun x => z ^ 2 * x) '' Set.Icc Zm (2 * Zm) = Set.Icc Zp (2 * Zp) := by
      rw [Set.image_mul_left_Icc hz2.le (by linarith), ← hzZ]
      congr 1
      ring
    rw [← himg, avg_scale _ hz2 _ measurableSet_Icc]
    congr 1
    refine lintegral_congr (fun w => ?_)
    rw [mul_div_cancel_left₀ _ hz2.ne']
  rw [hQ]
  have h2Zp : 2 * Zp - Zp = Zp := by ring
  rw [h2Zp]
  gcongr
  · exact hp Zp hZp₀ (rr i) (avg_rr_pos i) (avg_rr_le i)
  · exact hm Zm hZm₀ (rr i) (avg_rr_pos i) (avg_rr_le i)

lemma avg_X_bound (Cp Cm s z r L : ℝ) (hCp : 0 < Cp) (hCm : 0 < Cm) (hs : 2 ≤ s) (hz1 : 1 < z)
    (hz2 : z ≤ 2) (hr : 0 < r) (hL : 1 ≤ L) (hlZp0 : 0 ≤ Real.log (s * z))
    (hlZp : Real.log (s * z) ≤ L) (hlZm0 : 0 ≤ Real.log (s / z)) (hlZm : Real.log (s / z) ≤ L) :
    8 * (Cp * (s * z) * (1 + s * z * r) * Real.log (s * z) ^ 4) / L ^ 2
      + 128 * (z ^ 2 * (Cm * (s / z) * (1 + s / z * r) * Real.log (s / z) ^ 4)) / L ^ 2
      + 144 * (s * z) ≤ (16 * Cp + 256 * Cm + 288) * (s * (1 + 2 * s * r) * L ^ 2) := by
  have hz0 : 0 < z := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hL0 : 0 < L := by linarith
  have hL4 : Real.log (s * z) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hlZp0 hlZp 4
  have hL4' : Real.log (s / z) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hlZm0 hlZm 4
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have h1 : s * z ≤ 2 * s := by
    have := mul_le_mul_of_nonneg_left hz2 hs0
    linarith
  have hsz0 : 0 ≤ s * z := mul_nonneg hs0 hz0.le
  have h2 : 1 + s * z * r ≤ 1 + 2 * s * r := by
    have := mul_le_mul_of_nonneg_right h1 hr.le
    linarith
  have hsz' : s / z ≤ 2 * s := (div_le_self hs0 hz1.le).trans (by linarith)
  have hsz'0 : 0 ≤ s / z := div_nonneg hs0 hz0.le
  have h3 : 1 + s / z * r ≤ 1 + 2 * s * r := by
    have := mul_le_mul_of_nonneg_right hsz' hr.le
    linarith
  have hT1 : 8 * (Cp * (s * z) * (1 + s * z * r) * Real.log (s * z) ^ 4) / L ^ 2 ≤
      16 * Cp * (s * (1 + 2 * s * r) * L ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    calc 8 * (Cp * (s * z) * (1 + s * z * r) * Real.log (s * z) ^ 4)
        ≤ 8 * (Cp * (2 * s) * (1 + 2 * s * r) * L ^ 4) := by gcongr
      _ = _ := by ring
  have hT2 : 128 * (z ^ 2 * (Cm * (s / z) * (1 + s / z * r) * Real.log (s / z) ^ 4)) / L ^ 2 ≤
      256 * Cm * (s * (1 + 2 * s * r) * L ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have h0 : z ^ 2 * (Cm * (s / z) * (1 + s / z * r) * Real.log (s / z) ^ 4) =
        Cm * (s * z) * (1 + s / z * r) * Real.log (s / z) ^ 4 := by
      field_simp
    rw [h0]
    calc 128 * (Cm * (s * z) * (1 + s / z * r) * Real.log (s / z) ^ 4)
        ≤ 128 * (Cm * (2 * s) * (1 + 2 * s * r) * L ^ 4) := by gcongr
      _ = _ := by ring
  have hT3 : 144 * (s * z) ≤ 288 * (s * (1 + 2 * s * r) * L ^ 2) := by
    have h4 : 1 ≤ (1 + 2 * s * r) * L ^ 2 := by
      have : 1 ≤ 1 + 2 * s * r := by have := mul_nonneg hs0 hr.le; linarith
      nlinarith
    have h5 : s ≤ s * ((1 + 2 * s * r) * L ^ 2) := le_mul_of_one_le_right hs0 h4
    have e : s * (1 + 2 * s * r) * L ^ 2 = s * ((1 + 2 * s * r) * L ^ 2) := by ring
    rw [e]
    linarith
  have e : (16 * Cp + 256 * Cm + 288) * (s * (1 + 2 * s * r) * L ^ 2) =
      16 * Cp * (s * (1 + 2 * s * r) * L ^ 2) + 256 * Cm * (s * (1 + 2 * s * r) * L ^ 2)
        + 288 * (s * (1 + 2 * s * r) * L ^ 2) := by ring
  rw [e]
  linarith

lemma avg_term_R (K₁ X s N L z r : ℝ) (hK : 0 < K₁) (hs : 0 < s) (hsN : s ^ 2 = N)
    (hL : 0 < L) (hz1 : 1 < z) (hr : 0 < r) (hsr : s ≤ 8 * N * r)
    (hX : X ≤ K₁ * (s * (1 + 2 * s * r) * L ^ 2)) :
    4 * s * (2 * L / (r * (z - 1) * s) * X) ≤ 80 * K₁ * N * L ^ 3 / (z - 1) := by
  have hz10 : 0 < z - 1 := by linarith
  have hβ' : 4 * s * (2 * L / (r * (z - 1) * s)) = 8 * L / (r * (z - 1)) := by
    field_simp
    ring
  have hβ0 : 0 ≤ 8 * L / (r * (z - 1)) := by positivity
  have h10 : s + 2 * s ^ 2 * r ≤ 10 * N * r := by
    rw [hsN]
    linarith
  calc 4 * s * (2 * L / (r * (z - 1) * s) * X) = 8 * L / (r * (z - 1)) * X := by
        rw [← hβ']; ring
    _ ≤ 8 * L / (r * (z - 1)) * (K₁ * (s * (1 + 2 * s * r) * L ^ 2)) :=
        mul_le_mul_of_nonneg_left hX hβ0
    _ = 8 * K₁ * L ^ 3 * (s + 2 * s ^ 2 * r) / (r * (z - 1)) := by ring
    _ ≤ 8 * K₁ * L ^ 3 * (10 * N * r) / (r * (z - 1)) := by gcongr
    _ = 80 * K₁ * N * L ^ 3 / (z - 1) := by field_simp; ring

lemma avg_R_bound (Cp Cm : ℝ) (hCp : 0 < Cp) (hCm : 0 < Cm) (N : ℕ) (hN : 3600 ≤ N)
    (hL : 12 ≤ Real.log N) (z : ℝ) (hz1 : 1 < z) (hz2 : z ≤ 2) :
    4 * Real.sqrt N * ∑ i ∈ range (avgM N + 1), avgβ N z i *
        (8 * (Cp * (Real.sqrt N * z) * (1 + Real.sqrt N * z * rr i) *
          (Real.log (Real.sqrt N * z)) ^ 4) / (Real.log N) ^ 2
        + 128 * (z ^ 2 * (Cm * (Real.sqrt N / z) * (1 + Real.sqrt N / z * rr i) *
          (Real.log (Real.sqrt N / z)) ^ 4)) / (Real.log N) ^ 2
        + 144 * (Real.sqrt N * z))
      ≤ 160 * (16 * Cp + 256 * Cm + 288) * N * (Real.log N) ^ 4 / (z - 1) := by
  have hN0 : (3600 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsN : 60 ≤ Real.sqrt N := by nlinarith
  have hz0 : 0 < z := by linarith
  have hz10 : 0 < z - 1 := by linarith
  have hpow := (avg_pow_M N (by omega)).2
  have hMle := avg_M_le N (by omega) hL
  have hlogs : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt (Nat.cast_nonneg N)
  have hK : 0 < 16 * Cp + 256 * Cm + 288 := by linarith
  have hsz : 0 < Real.sqrt N * z := mul_pos (by linarith) hz0
  have hsz2 : Real.sqrt N * z ≤ N := by
    have := mul_le_mul_of_nonneg_left hz2 hsN0
    nlinarith
  have hlZp0 : 0 ≤ Real.log (Real.sqrt N * z) := Real.log_nonneg (by nlinarith)
  have hlZp : Real.log (Real.sqrt N * z) ≤ Real.log N := Real.log_le_log hsz hsz2
  have hsz' : 0 < Real.sqrt N / z := div_pos (by linarith) hz0
  have hlZm0 : 0 ≤ Real.log (Real.sqrt N / z) :=
    Real.log_nonneg (by rw [le_div_iff₀ hz0]; linarith)
  have hlZm : Real.log (Real.sqrt N / z) ≤ Real.log N := by
    have : Real.log (Real.sqrt N / z) ≤ Real.log (Real.sqrt N) :=
      Real.log_le_log hsz' (div_le_self hsN0 hz1.le)
    linarith
  rw [Finset.mul_sum]
  calc _ ≤ ∑ i ∈ range (avgM N + 1),
        80 * (16 * Cp + 256 * Cm + 288) * N * Real.log N ^ 3 / (z - 1) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hiM : i ≤ avgM N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hpi : (2:ℝ) ^ i ≤ 2 ^ avgM N := pow_le_pow_right₀ (by norm_num) hiM
        have hsr : Real.sqrt N ≤ 8 * N * rr i := by
          rw [rr, show 8 * (N:ℝ) * (2 / 2 ^ i) = 16 * N / 2 ^ i by ring,
            le_div_iff₀ (by positivity)]
          have h1 := mul_le_mul_of_nonneg_left hpi hsN0
          have h2 := mul_lt_mul_of_pos_left hpow (by linarith : 0 < Real.sqrt N)
          nlinarith
        exact avg_term_R _ _ _ _ _ _ _ hK (by linarith) hsqN (by linarith) hz1 (avg_rr_pos i) hsr
          (avg_X_bound Cp Cm _ z (rr i) _ hCp hCm (by linarith) hz1 hz2 (avg_rr_pos i)
            (by linarith) hlZp0 hlZp hlZm0 hlZm)
    _ = ((avgM N : ℝ) + 1) * (80 * (16 * Cp + 256 * Cm + 288) * N * Real.log N ^ 3 / (z - 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (2 * Real.log N) * (80 * (16 * Cp + 256 * Cm + 288) * N * Real.log N ^ 3 / (z - 1)) :=
        mul_le_mul_of_nonneg_right hMle (by positivity)
    _ = 160 * (16 * Cp + 256 * Cm + 288) * N * Real.log N ^ 4 / (z - 1) := by ring

lemma avg_star (Cp Zp₀ Cm Zm₀ : ℝ) (hCp : 0 < Cp) (hCm : 0 < Cm)
    (hp : ∀ Z : ℝ, Zp₀ ≤ Z → ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bp r (kOf Z r) y) ^ 2)
        ≤ ENNReal.ofReal (Cp * Z * (1 + Z * r) * (Real.log Z) ^ 4))
    (hm : ∀ Z : ℝ, Zm₀ ≤ Z → ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bm r (kOf Z r) y) ^ 2)
        ≤ ENNReal.ofReal (Cm * Z * (1 + Z * r) * (Real.log Z) ^ 4))
    (N : ℕ) (hN : 3600 ≤ N) (hL : 12 ≤ Real.log N) (hZp : Zp₀ ≤ Real.sqrt N)
    (hZm : Zm₀ ≤ Real.sqrt N / 2) (z : ℝ) (hz1 : 1 < z) (hz2 : z ≤ 2) :
    ∑ n ∈ Ioc N (2 * N), ENNReal.ofReal (W n (Real.sqrt n * z) : ℝ)
      ≤ ENNReal.ofReal (2 * N + 160 * (16 * Cp + 256 * Cm + 288) * N * (Real.log N) ^ 4 / (z - 1)) := by
  have hN0 : (3600 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsN : 60 ≤ Real.sqrt N := by nlinarith
  have hz0 : 0 < z := by linarith
  have hβ : ∀ i, 0 ≤ avgβ N z i := fun i => by
    unfold avgβ
    exact div_nonneg (by linarith) (mul_nonneg (mul_nonneg (avg_rr_pos i).le (by linarith)) hsN0)
  have hint := avg_G_int Cp Zp₀ Cm Zm₀ hp hm hCp hCm (avgM N) (avgβ N z) hβ (Real.log N) z
    (Real.sqrt N * z) (Real.sqrt N / z) hz0 (div_pos (by linarith) hz0)
    (by field_simp) (le_trans hZp (le_mul_of_one_le_right hsN0 hz1.le))
    (le_trans hZm (div_le_div_of_nonneg_left hsN0 hz0 hz2))
  have hRb := avg_R_bound Cp Cm hCp hCm N hN hL z hz1 hz2
  set G : ℝ → ℝ := fun y => ∑ i ∈ range (avgM N + 1), avgβ N z i *
        (8 * (Bp (rr i) (kOf (Real.sqrt N * z) (rr i)) y) ^ 2 / (Real.log N) ^ 2
        + 128 * (Bm (rr i) (kOf (Real.sqrt N / z) (rr i)) (y / z ^ 2)) ^ 2 / (Real.log N) ^ 2
        + 144) with hG
  set R : ℝ := ∑ i ∈ range (avgM N + 1), avgβ N z i *
        (8 * (Cp * (Real.sqrt N * z) * (1 + Real.sqrt N * z * rr i) *
          (Real.log (Real.sqrt N * z)) ^ 4) / (Real.log N) ^ 2
        + 128 * (z ^ 2 * (Cm * (Real.sqrt N / z) * (1 + Real.sqrt N / z * rr i) *
          (Real.log (Real.sqrt N / z)) ^ 4)) / (Real.log N) ^ 2
        + 144 * (Real.sqrt N * z)) with hR
  set B : ℝ := 160 * (16 * Cp + 256 * Cm + 288) * N * (Real.log N) ^ 4 / (z - 1) with hB
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    (by positivity)) (by linarith)
  set I : ℕ → Set ℝ := fun n => Set.Ico (Real.sqrt n * z) (Real.sqrt ((n + 1 : ℕ) : ℝ) * z)
    with hI
  have hper : ∀ n ∈ Ioc N (2 * N), ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2) ≤
      ENNReal.ofReal (4 * Real.sqrt N) * ∫⁻ y in I n, ENNReal.ofReal (G y) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (N : ℝ) < n := by exact_mod_cast hn.1
    have hn20 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.2
    have hsqn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsn1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = n + 1 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring
    have hsn0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hsNn : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt hn0.le
    have hlt : Real.sqrt n ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    have hprod : (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) *
        (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt n) = 1 := by
      linear_combination hsn1 - hsqn
    have hd1 : 2 * Real.sqrt N * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (by linarith : 2 * Real.sqrt N ≤
        Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt n) (by linarith : (0:ℝ) ≤
          Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)
      linarith
    have hs1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt N := by
      nlinarith
    have hd2 : 1 ≤ 4 * Real.sqrt N * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) := by
      have h := mul_le_mul_of_nonneg_left (by linarith : Real.sqrt ((n + 1 : ℕ) : ℝ) +
        Real.sqrt n ≤ 4 * Real.sqrt N) (by linarith : (0:ℝ) ≤
          Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)
      linarith
    have hpt : ∀ y ∈ I n, ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2) ≤
        ENNReal.ofReal (G y) := by
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      apply avg_pointwise N n hN hL hn.1 hn.2 z hz1 hz2 y hy.1
      have h1 : (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n) * z ≤ 1 / Real.sqrt N := by
        rw [le_div_iff₀ (by linarith)]
        have := mul_le_mul_of_nonneg_left hz2 (by linarith : (0:ℝ) ≤
          Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)
        nlinarith
      have h2 := hy.2
      linarith
    have hvol : ENNReal.ofReal (1 / (4 * Real.sqrt N)) ≤ volume (I n) := by
      rw [hI, Real.volume_Ico]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hz1.le (by linarith : (0:ℝ) ≤
          Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt n)
      nlinarith
    calc ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2)
        = ENNReal.ofReal (4 * Real.sqrt N) * (ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2) *
            ENNReal.ofReal (1 / (4 * Real.sqrt N))) := by
          rw [mul_comm (ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2)), ← mul_assoc,
            ← ENNReal.ofReal_mul (by linarith), mul_one_div_cancel (by linarith),
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (4 * Real.sqrt N) * (ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2) *
            volume (I n)) := by gcongr
      _ = ENNReal.ofReal (4 * Real.sqrt N) *
            ∫⁻ y in I n, ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2) := by
          rw [setLIntegral_const]
      _ ≤ _ := mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ico hpt) (by positivity)
  have hmono : Monotone (fun m : ℕ => Real.sqrt (m : ℝ) * z) := fun a b h =>
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (Nat.cast_le.mpr h)) hz0.le
  have hdisj : (↑(Ioc N (2 * N)) : Set ℕ).PairwiseDisjoint I := by
    have := hmono.pairwise_disjoint_on_Ico_succ
    simp only [Order.succ_eq_add_one] at this
    exact this.set_pairwise _
  have hsub : (⋃ n ∈ Ioc N (2 * N), I n) ⊆
      Set.Icc (Real.sqrt N * z) (2 * (Real.sqrt N * z)) := by
    intro y hy
    simp only [Set.mem_iUnion, Finset.mem_Ioc, hI, Set.mem_Ico] at hy
    obtain ⟨n, hn, hy1, hy2⟩ := hy
    have hn0 : (N : ℝ) < n := by exact_mod_cast hn.1
    have hn20 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.2
    have hsNn : Real.sqrt N ≤ Real.sqrt n := Real.sqrt_le_sqrt hn0.le
    have hsn1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = n + 1 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring
    have hs1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt N := by
      have := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ)
      nlinarith
    constructor
    · have := mul_le_mul_of_nonneg_right hsNn hz0.le
      linarith
    · have := mul_le_mul_of_nonneg_right hs1 hz0.le
      linarith
  have hcard : ((Ioc N (2 * N)).card : ENNReal) * ENNReal.ofReal 2 = ENNReal.ofReal (2 * N) := by
    rw [Nat.card_Ioc, show 2 * N - N = N by omega, show (2 : ℝ) * N = N * 2 by ring,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc ∑ n ∈ Ioc N (2 * N), ENNReal.ofReal (W n (Real.sqrt n * z) : ℝ)
      ≤ ∑ n ∈ Ioc N (2 * N), (ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2) +
          ENNReal.ofReal 2) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        calc ENNReal.ofReal (W n (Real.sqrt n * z) : ℝ)
            = ENNReal.ofReal (((W n (Real.sqrt n * z) : ℝ) - 2) + 2) := by ring_nf
          _ ≤ _ := ENNReal.ofReal_add_le
    _ = ∑ n ∈ Ioc N (2 * N), ENNReal.ofReal ((W n (Real.sqrt n * z) : ℝ) - 2) +
          ENNReal.ofReal (2 * N) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (∑ n ∈ Ioc N (2 * N), ENNReal.ofReal (4 * Real.sqrt N) *
          ∫⁻ y in I n, ENNReal.ofReal (G y)) + ENNReal.ofReal (2 * N) := by
        exact add_le_add (Finset.sum_le_sum hper) le_rfl
    _ = ENNReal.ofReal (4 * Real.sqrt N) *
          (∫⁻ y in ⋃ n ∈ Ioc N (2 * N), I n, ENNReal.ofReal (G y)) + ENNReal.ofReal (2 * N) := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Ico)]
    _ ≤ ENNReal.ofReal (4 * Real.sqrt N) *
          (∫⁻ y in Set.Icc (Real.sqrt N * z) (2 * (Real.sqrt N * z)), ENNReal.ofReal (G y))
          + ENNReal.ofReal (2 * N) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) (by positivity)) le_rfl
    _ ≤ ENNReal.ofReal (4 * Real.sqrt N) * ENNReal.ofReal R + ENNReal.ofReal (2 * N) :=
        add_le_add (mul_le_mul_of_nonneg_left hint (by positivity)) le_rfl
    _ = ENNReal.ofReal (4 * Real.sqrt N * R) + ENNReal.ofReal (2 * N) := by
        rw [← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 4 * Real.sqrt N)]
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal (2 * N) := by
        gcongr
    _ = ENNReal.ofReal (2 * N + B) := by
        rw [← ENNReal.ofReal_add hB0 (by positivity), add_comm]

theorem average_bound (hS : SelbergMS) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Ioc N (2 * N),
          ∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (C * (N : ℝ) * (Real.log N) ^ 5) := by
  obtain ⟨Cp, Zp₀, hCp, hp⟩ := ms_Bp hS
  obtain ⟨Cm, Zm₀, hCm, hm⟩ := ms_Bm hS
  have hK0 : 0 < 160 * (16 * Cp + 256 * Cm + 288) := by linarith
  set K : ℝ := 160 * (16 * Cp + 256 * Cm + 288) with hK
  set N₀ : ℝ := max (max (Real.exp 12) 3600) (max (Zp₀ ^ 2) (4 * Zm₀ ^ 2)) with hN₀
  have hN₀0 : 0 < N₀ :=
    lt_of_lt_of_le (Real.exp_pos 12) (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨64 * N₀ + 4 + K, by linarith, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 := Real.log_two_gt_d9
  have hLN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hL0 : 0 < Real.log N := by linarith
  have hcard : ((Ioc N (2 * N)).card : ENNReal) * ENNReal.ofReal 2 =
      ENNReal.ofReal (2 * N) := by
    rw [Nat.card_Ioc, show 2 * N - N = N by omega, show (2 : ℝ) * N = N * 2 by ring,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  by_cases hlarge : N₀ ≤ N
  · have hN0' : Real.exp 12 ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlarge
    have hN3600 : (3600:ℝ) ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlarge
    have hNp : Zp₀ ^ 2 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlarge
    have hNm : 4 * Zm₀ ^ 2 ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlarge
    have hNnat : 3600 ≤ N := by exact_mod_cast hN3600
    have hL : 12 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact hN0'
    have hZp : Zp₀ ≤ Real.sqrt N := le_trans (le_abs_self _) (Real.abs_le_sqrt hNp)
    have hZm : Zm₀ ≤ Real.sqrt N / 2 := by
      have h1 : |2 * Zm₀| ≤ Real.sqrt N := Real.abs_le_sqrt (by nlinarith)
      have h2 := le_abs_self (2 * Zm₀)
      linarith
    have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
    have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hs60 : 60 ≤ Real.sqrt N := by nlinarith
    have hη0 : 0 < 1 / Real.sqrt N := one_div_pos.mpr (by linarith)
    have hη1 : 1 / Real.sqrt N ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hstar := avg_star Cp Zp₀ Cm Zm₀ hCp hCm hp hm N hNnat hL hZp hZm
    have hsplit : ∀ n ∈ Ioc N (2 * N),
        ∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u) ≤
          ENNReal.ofReal 2 + ∫⁻ z in Set.Ico (1 + 1 / Real.sqrt N) 2,
            ENNReal.ofReal (W n (Real.sqrt n * z) : ℝ) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (N:ℝ) < n := by exact_mod_cast hn.1
      have hn20 : (n:ℝ) ≤ 2 * N := by exact_mod_cast hn.2
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
      have hsqn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
      have hsn2 : Real.sqrt n ≤ 2 * Real.sqrt N := by nlinarith
      have hunion : Set.Ico (Real.sqrt n) (2 * Real.sqrt n) =
          Set.Ico (Real.sqrt n) (Real.sqrt n * (1 + 1 / Real.sqrt N)) ∪
            Set.Ico (Real.sqrt n * (1 + 1 / Real.sqrt N)) (Real.sqrt n * 2) := by
        have h1 : Real.sqrt n ≤ Real.sqrt n * (1 + 1 / Real.sqrt N) :=
          le_mul_of_one_le_right hsn.le (by linarith)
        have h2 : Real.sqrt n * (1 + 1 / Real.sqrt N) ≤ Real.sqrt n * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hsn.le
        rw [Set.Ico_union_Ico_eq_Ico h1 h2, mul_comm (Real.sqrt n) 2]
      rw [hunion]
      refine (lintegral_union_le _ _ _).trans (add_le_add ?_ ?_)
      · calc ∫⁻ u in Set.Ico (Real.sqrt n) (Real.sqrt n * (1 + 1 / Real.sqrt N)),
              ENNReal.ofReal ((W n u : ℝ) / u)
            ≤ ∫⁻ u in Set.Ico (Real.sqrt n) (Real.sqrt n * (1 + 1 / Real.sqrt N)), 1 :=
              setLIntegral_mono' measurableSet_Ico
                (fun u hu => ENNReal.ofReal_le_one.mpr (avg_W_div_le_one n u hu.1))
          _ = ENNReal.ofReal (Real.sqrt n * (1 + 1 / Real.sqrt N) - Real.sqrt n) := by
              rw [setLIntegral_const, Real.volume_Ico, one_mul]
          _ ≤ ENNReal.ofReal 2 := by
              apply ENNReal.ofReal_le_ofReal
              rw [show Real.sqrt n * (1 + 1 / Real.sqrt N) - Real.sqrt n =
                Real.sqrt n / Real.sqrt N by ring, div_le_iff₀ (by linarith)]
              linarith
      · rw [← Set.image_mul_left_Ico hsn, avg_scale _ hsn _ measurableSet_Ico,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply setLIntegral_mono' measurableSet_Ico
        intro z hz
        have hz1 : 1 ≤ z := by
          have := hz.1
          linarith
        rw [← ENNReal.ofReal_mul hsn.le]
        apply ENNReal.ofReal_le_ofReal
        have hW0 : (0:ℝ) ≤ W n (Real.sqrt n * z) := Nat.cast_nonneg _
        calc Real.sqrt n * ((W n (Real.sqrt n * z) : ℝ) / (Real.sqrt n * z))
            = (W n (Real.sqrt n * z) : ℝ) / z := by
              field_simp
          _ ≤ W n (Real.sqrt n * z) := div_le_self hW0 hz1
    have hmeas : ∀ n ∈ Ioc N (2 * N),
        Measurable (fun z : ℝ => ENNReal.ofReal (W n (Real.sqrt n * z) : ℝ)) := fun n _ =>
      (measurable_from_nat.comp ((measurable_W n).comp (measurable_const_mul _))).ennreal_ofReal
    have hint := avg_lint_inv (1 / Real.sqrt N) hη0 hη1
    have hlog : Real.log (1 / (1 / Real.sqrt N)) = Real.log N / 2 := by
      rw [one_div_one_div, Real.log_sqrt (Nat.cast_nonneg N)]
    have hKN : 0 ≤ K * N * Real.log N ^ 4 :=
      mul_nonneg (mul_nonneg hK0.le (Nat.cast_nonneg _)) (by positivity)
    calc ∑ n ∈ Ioc N (2 * N), ∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n),
          ENNReal.ofReal ((W n u : ℝ) / u)
        ≤ ∑ n ∈ Ioc N (2 * N), (ENNReal.ofReal 2 + ∫⁻ z in Set.Ico (1 + 1 / Real.sqrt N) 2,
            ENNReal.ofReal (W n (Real.sqrt n * z) : ℝ)) := Finset.sum_le_sum hsplit
      _ = ENNReal.ofReal (2 * N) + ∫⁻ z in Set.Ico (1 + 1 / Real.sqrt N) 2,
            ∑ n ∈ Ioc N (2 * N), ENNReal.ofReal (W n (Real.sqrt n * z) : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
            lintegral_finsetSum _ hmeas]
      _ ≤ ENNReal.ofReal (2 * N) + ∫⁻ z in Set.Ico (1 + 1 / Real.sqrt N) 2,
            (ENNReal.ofReal (2 * N) +
              ENNReal.ofReal (K * N * Real.log N ^ 4) * ENNReal.ofReal (1 / (z - 1))) := by
          refine add_le_add le_rfl (setLIntegral_mono' measurableSet_Ico (fun z hz => ?_))
          have hz1 : 1 < z := by
            have := hz.1
            linarith
          refine (hstar z hz1 hz.2.le).trans ?_
          calc ENNReal.ofReal (2 * N + K * N * Real.log N ^ 4 / (z - 1))
              = ENNReal.ofReal (2 * N + K * N * Real.log N ^ 4 * (1 / (z - 1))) := by
                congr 1
                ring
            _ ≤ ENNReal.ofReal (2 * N) +
                ENNReal.ofReal (K * N * Real.log N ^ 4 * (1 / (z - 1))) := ENNReal.ofReal_add_le
            _ = _ := by rw [ENNReal.ofReal_mul hKN]
      _ = ENNReal.ofReal (2 * N) + (ENNReal.ofReal (2 * N) *
            volume (Set.Ico (1 + 1 / Real.sqrt N) 2) + ENNReal.ofReal (K * N * Real.log N ^ 4) *
            ∫⁻ z in Set.Ico (1 + 1 / Real.sqrt N) 2, ENNReal.ofReal (1 / (z - 1))) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 * N) + (ENNReal.ofReal (2 * N) * 1 +
            ENNReal.ofReal (K * N * Real.log N ^ 4) * ENNReal.ofReal (Real.log N / 2)) := by
          gcongr
          · rw [Real.volume_Ico]
            exact ENNReal.ofReal_le_one.mpr (by linarith)
          · rw [← hlog]
            exact hint
      _ = ENNReal.ofReal (2 * N + (2 * N + K * N * Real.log N ^ 4 * (Real.log N / 2))) := by
          rw [mul_one, ← ENNReal.ofReal_mul hKN, ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg hKN (by positivity)), ← ENNReal.ofReal_add (by positivity)
            (add_nonneg (by positivity) (mul_nonneg hKN (by positivity)))]
      _ ≤ ENNReal.ofReal ((64 * N₀ + 4 + K) * N * (Real.log N) ^ 5) := by
          apply ENNReal.ofReal_le_ofReal
          have hL5 : 1 ≤ Real.log N ^ 5 := one_le_pow₀ (by linarith)
          have hNL : (N:ℝ) ≤ N * Real.log N ^ 5 := le_mul_of_one_le_right (Nat.cast_nonneg _) hL5
          have hNL0 : 0 ≤ (N:ℝ) * Real.log N ^ 5 := by positivity
          have h1 : 0 ≤ N₀ * (N * Real.log N ^ 5) := mul_nonneg hN₀0.le hNL0
          have h2 : 0 ≤ K * (N * Real.log N ^ 5) := mul_nonneg hK0.le hNL0
          have e1 : K * N * Real.log N ^ 4 * (Real.log N / 2) = K * (N * Real.log N ^ 5) / 2 := by
            ring
          have e2 : (64 * N₀ + 4 + K) * N * Real.log N ^ 5 =
              64 * (N₀ * (N * Real.log N ^ 5)) + 4 * (N * Real.log N ^ 5) +
                K * (N * Real.log N ^ 5) := by ring
          rw [e1, e2]
          linarith
  · replace hlarge : (N : ℝ) < N₀ := not_le.mp hlarge
    have hL5 : 1 / 32 ≤ Real.log N ^ 5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by linarith : (1:ℝ) / 2 ≤ Real.log N) 5
      have e : ((1:ℝ) / 2) ^ 5 = 1 / 32 := by norm_num
      linarith
    calc ∑ n ∈ Ioc N (2 * N), ∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n),
          ENNReal.ofReal ((W n u : ℝ) / u)
        ≤ ∑ n ∈ Ioc N (2 * N), ENNReal.ofReal 2 * ENNReal.ofReal N := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_Ioc] at hn
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          have hn20 : (n:ℝ) ≤ 2 * N := by exact_mod_cast hn.2
          have hsq := Real.sq_sqrt (by linarith : (0:ℝ) ≤ n)
          have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
          calc ∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u)
              ≤ ∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), 1 :=
                setLIntegral_mono' measurableSet_Ico
                  (fun u hu => ENNReal.ofReal_le_one.mpr (avg_W_div_le_one n u hu.1))
            _ = ENNReal.ofReal (Real.sqrt n) := by
                rw [setLIntegral_const, Real.volume_Ico, one_mul]
                congr 1
                ring
            _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal N := by
                rw [← ENNReal.ofReal_mul (by norm_num)]
                exact ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal (2 * N) * ENNReal.ofReal N := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hcard]
      _ = ENNReal.ofReal (2 * N * N) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((64 * N₀ + 4 + K) * N * (Real.log N) ^ 5) := by
          apply ENNReal.ofReal_le_ofReal
          have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
          have h1 : 2 * (N:ℝ) * N ≤ 2 * N₀ * N := by nlinarith
          have h2 : 2 * N₀ * N ≤ 64 * N₀ * N * Real.log N ^ 5 := by
            have := mul_le_mul_of_nonneg_left hL5
              (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) hN₀0.le) hN0)
            linarith
          have h3 : 0 ≤ (4 + K) * N * Real.log N ^ 5 :=
            mul_nonneg (mul_nonneg (by linarith) hN0) (by positivity)
          have e : (64 * N₀ + 4 + K) * N * Real.log N ^ 5 =
              64 * N₀ * N * Real.log N ^ 5 + (4 + K) * N * Real.log N ^ 5 := by ring
          rw [e]
          linarith

end Erdos879
