import Erdos879.Analytic.Excess
import Erdos879.Analytic.Chain
import Erdos879.Analytic.MeanSquare

open Finset MeasureTheory

namespace Erdos879

theorem block_exp_neg_two : 1 / 8 < Real.exp (-2) := by
  have h := Real.exp_neg_one_gt_d9
  have h2 : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [h2]; nlinarith

theorem block_mm (Cm x U Z r : ℝ) (k : ℕ) (hU : 0 < U) (hx : x = 2 * U * Z)
    (hZ : 60 ≤ Z) (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hms : ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bm r k y) ^ 2)
        ≤ ENNReal.ofReal (Cm * Z * (1 + Z * r) * (Real.log Z) ^ 4)) :
    ∫⁻ u in Set.Icc U (2 * U),
        ENNReal.ofReal ((2 * Bm r k (x / u) / Real.log (x / u * Real.exp (-r))) ^ 2)
      ≤ ENNReal.ofReal (32 * Cm * U * (1 + Z * r) * (Real.log Z) ^ 2) := by
  have hZpos : 0 < Z := by linarith
  have hxpos : 0 < x := by rw [hx]; positivity
  have hlogZ : 4 < Real.log Z := by
    rw [Real.lt_log_iff_exp_lt hZpos]
    have h1 := Real.exp_one_lt_d9
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have h0 : 0 < Real.exp 1 := Real.exp_pos 1
    calc Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
      _ < Z := by norm_num; linarith
  set g : ℝ → ENNReal := fun u =>
    ENNReal.ofReal ((2 * Bm r k (x / u) / Real.log (x / u * Real.exp (-r))) ^ 2) with hg
  set f : ℝ → ℝ := fun y => x * y⁻¹ with hf
  have hsub : Set.Icc U (2 * U) ⊆ f '' Set.Icc Z (2 * Z) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hU hu.1
    refine ⟨x / u, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hu0, hx]; nlinarith [hu.2]
    · rw [div_le_iff₀ hu0, hx]; nlinarith [hu.1]
    · simp only [hf]; field_simp
  have hderiv : ∀ y ∈ Set.Icc Z (2 * Z), HasDerivWithinAt f (x * -(y ^ 2)⁻¹) (Set.Icc Z (2 * Z)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    exact ((hasDerivAt_inv hy0).const_mul x).hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Icc Z (2 * Z)) := by
    intro a ha b hb hab
    simp only [hf] at hab
    have := mul_left_cancel₀ hxpos.ne' hab
    exact inv_injective this
  set c : ℝ := 16 * x / (Z ^ 2 * (Real.log Z) ^ 2) with hc
  have hpt : ∀ y ∈ Set.Icc Z (2 * Z),
      ENNReal.ofReal (|x * -(y ^ 2)⁻¹|) * g (f y) ≤ ENNReal.ofReal c * ENNReal.ofReal ((Bm r k y) ^ 2) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hfy : x / f y = y := by simp only [hf]; field_simp
    simp only [hg, hfy]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have habs : |x * -(y ^ 2)⁻¹| = x / y ^ 2 := by
      rw [abs_of_nonpos (by have : 0 < (y ^ 2)⁻¹ := by positivity
                            nlinarith)]
      ring
    rw [habs]
    have hlog : Real.log Z / 2 ≤ Real.log (y * Real.exp (-r)) := by
      rw [Real.log_mul hy0.ne' (Real.exp_pos _).ne', Real.log_exp]
      have := Real.log_le_log hZpos hy.1
      linarith
    have hlogpos : 0 < Real.log Z / 2 := by linarith
    have h1 : x / y ^ 2 ≤ x / Z ^ 2 := by
      apply div_le_div_of_nonneg_left hxpos.le (by positivity)
      exact pow_le_pow_left₀ hZpos.le hy.1 2
    have h2 : (2 * Bm r k y / Real.log (y * Real.exp (-r))) ^ 2 ≤
        16 / (Real.log Z) ^ 2 * (Bm r k y) ^ 2 := by
      rw [div_pow, mul_pow]
      have hl2 : (Real.log Z / 2) ^ 2 ≤ (Real.log (y * Real.exp (-r))) ^ 2 :=
        pow_le_pow_left₀ hlogpos.le hlog 2
      calc 2 ^ 2 * Bm r k y ^ 2 / Real.log (y * Real.exp (-r)) ^ 2
          ≤ 2 ^ 2 * Bm r k y ^ 2 / (Real.log Z / 2) ^ 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hl2
        _ = 16 / (Real.log Z) ^ 2 * (Bm r k y) ^ 2 := by
            field_simp; ring
    calc x / y ^ 2 * (2 * Bm r k y / Real.log (y * Real.exp (-r))) ^ 2
        ≤ x / Z ^ 2 * (16 / (Real.log Z) ^ 2 * (Bm r k y) ^ 2) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = c * Bm r k y ^ 2 := by rw [hc]; field_simp
  calc ∫⁻ u in Set.Icc U (2 * U), g u
      ≤ ∫⁻ u in f '' Set.Icc Z (2 * Z), g u := lintegral_mono_set hsub
    _ = ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal (|x * -(y ^ 2)⁻¹|) * g (f y) :=
        lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv hinj g
    _ ≤ ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal c * ENNReal.ofReal ((Bm r k y) ^ 2) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal c * ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bm r k y) ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Cm * Z * (1 + Z * r) * (Real.log Z) ^ 4) := by
        gcongr
    _ = ENNReal.ofReal (32 * Cm * U * (1 + Z * r) * (Real.log Z) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by rw [hc]; positivity)]
        congr 1
        rw [hc, hx]
        field_simp
        ring

theorem block_mp (Cp U r : ℝ) (k : ℕ) (hU : 3 ≤ U)
    (hms : ∫⁻ y in Set.Icc U (2 * U), ENNReal.ofReal ((Bp r k y) ^ 2)
        ≤ ENNReal.ofReal (Cp * U * (1 + U * r) * (Real.log U) ^ 4)) :
    ∫⁻ u in Set.Icc U (2 * U), ENNReal.ofReal ((Bp r k u / Real.log u) ^ 2)
      ≤ ENNReal.ofReal (Cp * U * (1 + U * r) * (Real.log U) ^ 2) := by
  have hUpos : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
  set c : ℝ := 1 / (Real.log U) ^ 2 with hc
  have hpt : ∀ u ∈ Set.Icc U (2 * U),
      ENNReal.ofReal ((Bp r k u / Real.log u) ^ 2) ≤ ENNReal.ofReal c * ENNReal.ofReal ((Bp r k u) ^ 2) := by
    intro u hu
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hl : Real.log U ≤ Real.log u := Real.log_le_log hUpos hu.1
    rw [div_pow, hc, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hlogU.le hl 2)
  calc ∫⁻ u in Set.Icc U (2 * U), ENNReal.ofReal ((Bp r k u / Real.log u) ^ 2)
      ≤ ∫⁻ u in Set.Icc U (2 * U), ENNReal.ofReal c * ENNReal.ofReal ((Bp r k u) ^ 2) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal c * ∫⁻ u in Set.Icc U (2 * U), ENNReal.ofReal ((Bp r k u) ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Cp * U * (1 + U * r) * (Real.log U) ^ 4) := by
        gcongr
    _ = ENNReal.ofReal (Cp * U * (1 + U * r) * (Real.log U) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by rw [hc]; positivity)]
        congr 1
        rw [hc]
        field_simp

theorem block_pt (n : ℕ) (U Z u β : ℝ) (N : ℕ) (hZ : (n : ℝ) = 2 * U * Z) (hZ60 : 60 ≤ Z)
    (hU : 2 ≤ U) (hUu : U ≤ u) (hu2 : u ≤ 2 * U) (hXu : Real.sqrt n + β * U ≤ u) (hβ : 0 < β)
    (hun : 30 * u ≤ n) (hN : 2 * u ≤ 2 ^ N) :
    (W n u : ℝ) / u ≤ 2 / U + ∑ i ∈ range (N + 1), Real.log n / (rr i * β * U ^ 2) *
      ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
        (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2) := by
  have hUpos : 0 < U := by linarith
  have hupos : 0 < u := by linarith
  have hZpos : 0 < Z := by linarith
  have hnR : (240 : ℝ) ≤ n := by rw [hZ]; nlinarith
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hX0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hXu' : Real.sqrt n ≤ u := by nlinarith [mul_pos hβ hUpos]
  have hrr : ∀ i : ℕ, 0 < rr i ∧ rr i ≤ 2 := by
    intro i
    have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    refine ⟨by unfold rr; positivity, ?_⟩
    unfold rr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hnu : Z ≤ n / u := by rw [le_div_iff₀ hupos, hZ]; nlinarith
  have hE := block_exp_neg_two
  have hexc := excess n hn1 u hXu' hun N hN
    (fun i => Bp (rr i) (kOf U (rr i)) u / Real.log u)
    (fun i => 2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i)))
    (fun i _ s hs0 hsr => abs_E_exp_sub_le _ _ _ _ (by linarith) hs0 hsr)
    (fun i _ s hs0 hsr => abs_E_exp_neg_sub_le _ _ _ _ (by
      have h1 : Real.exp (-2) ≤ Real.exp (-rr i) := Real.exp_le_exp.mpr (by linarith [(hrr i).2])
      nlinarith) hs0 hsr)
  set L := Real.log n with hLdef
  set X := Real.sqrt n with hXdef
  have hW0 : (0 : ℝ) ≤ W n u := Nat.cast_nonneg _
  have hterm : ∀ i ∈ range (N + 1),
      (Bp (rr i) (kOf U (rr i)) u / Real.log u +
          2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2 /
          (4 * bfun n (rr i) u) ≤
        U * (L / (rr i * β * U ^ 2) *
          ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
            (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2)) := by
    intro i _
    set p := Bp (rr i) (kOf U (rr i)) u / Real.log u
    set m := 2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))
    set r := rr i with hr
    have hr0 : 0 < r := (hrr i).1
    have hb : r * β * U / (2 * L) ≤ bfun n r u := by
      unfold bfun
      rw [← hLdef, ← hXdef]
      have : r * β * U / (2 * L) = r / (2 * L) * (β * U) := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 0 ≤ X * r / 4 := by positivity
      linarith
    have hbpos : 0 < r * β * U / (2 * L) := by positivity
    have h4b : 0 < 4 * bfun n r u := by linarith
    rw [div_le_iff₀ h4b]
    have hc0 : 0 ≤ U * (L / (r * β * U ^ 2) * (p ^ 2 + m ^ 2)) := by positivity
    calc (p + m) ^ 2 ≤ 2 * (p ^ 2 + m ^ 2) := by nlinarith [sq_nonneg (p - m)]
      _ = U * (L / (r * β * U ^ 2) * (p ^ 2 + m ^ 2)) * (4 * (r * β * U / (2 * L))) := by
          field_simp
          ring
      _ ≤ U * (L / (r * β * U ^ 2) * (p ^ 2 + m ^ 2)) * (4 * bfun n r u) := by
          gcongr
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  calc (W n u : ℝ) / u ≤ (W n u : ℝ) / U := div_le_div_of_nonneg_left hW0 hUpos hUu
    _ ≤ _ := by
      rw [div_le_iff₀ hUpos]
      have : (2 / U + ∑ i ∈ range (N + 1), L / (rr i * β * U ^ 2) *
          ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
            (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2)) * U
          = 2 + U * ∑ i ∈ range (N + 1), L / (rr i * β * U ^ 2) *
          ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
            (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2) := by
        rw [add_mul, div_mul_cancel₀ _ hUpos.ne', Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [this]
      linarith

theorem block_N (U : ℝ) (hU : 1 ≤ U) : ∃ N : ℕ, 4 * U ≤ 2 ^ N ∧ (2 : ℝ) ^ N < 8 * U := by
  refine ⟨⌈Real.logb 2 (4 * U)⌉₊, ?_, ?_⟩
  · have h1 := Nat.le_ceil (Real.logb 2 (4 * U))
    calc 4 * U = (2 : ℝ) ^ Real.logb 2 (4 * U) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 (4 * U)⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = _ := Real.rpow_natCast _ _
  · have h0 : 0 ≤ Real.logb 2 (4 * U) := Real.logb_nonneg (by norm_num) (by linarith)
    have h1 := Nat.ceil_lt_add_one (R := ℝ) h0
    calc (2 : ℝ) ^ ⌈Real.logb 2 (4 * U)⌉₊ = (2 : ℝ) ^ (⌈Real.logb 2 (4 * U)⌉₊ : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ < (2 : ℝ) ^ (Real.logb 2 (4 * U) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
      _ = 8 * U := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
            Real.rpow_one]
          ring

theorem block_Nbound (N : ℕ) (x U : ℝ) (hU : 0 < U) (hUx : U ≤ x) (hN : (2 : ℝ) ^ N < 8 * U)
    (hL : 1 ≤ Real.log x) : (N : ℝ) + 1 ≤ 8 * Real.log x := by
  have hx : 0 < x := by linarith
  have h1 : Real.log ((2 : ℝ) ^ N) < Real.log (8 * x) := Real.log_lt_log (by positivity) (by linarith)
  rw [Real.log_pow, Real.log_mul (by norm_num) hx.ne', show (8 : ℝ) = 2 ^ 3 by norm_num,
    Real.log_pow] at h1
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  push_cast at h1
  nlinarith

theorem block (hS : SelbergMS) :
    ∃ C Z₁ : ℝ, 0 < C ∧ 30 ≤ Z₁ ∧ ∀ (n : ℕ) (U a β : ℝ), Real.sqrt n ≤ U → 2 * U * Z₁ ≤ n →
      U ≤ a → Real.sqrt n + β * U ≤ a → 0 < β → β ≤ 1 →
      (∫⁻ u in Set.Icc a (2 * U), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (C * (Real.log n) ^ 4 / β) := by
  obtain ⟨Cp, Zp, hCp, hp⟩ := ms_Bp hS
  obtain ⟨Cm, Zm, hCm, hm⟩ := ms_Bm hS
  refine ⟨2 + 40 * (Cp + 32 * Cm), max 100 (max Zp Zm), by positivity,
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro n U a β hXU hUn hUa hXa hβ hβ1
  have hZ₁100 : (100 : ℝ) ≤ max 100 (max Zp Zm) := le_max_left _ _
  have hZpZ₁ : Zp ≤ max 100 (max Zp Zm) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hZmZ₁ : Zm ≤ max 100 (max Zp Zm) := le_trans (le_max_right _ _) (le_max_right _ _)
  set Z₁ := max 100 (max Zp Zm) with hZ₁
  rcases le_or_gt (2 * U) a with h2a | h2a
  · rw [setLIntegral_measure_zero _ _ (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_eq_zero.2 (by linarith))]
    exact zero_le
  have hX0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hU0 : 0 ≤ U := le_trans hX0 hXU
  have hnpos : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).eq_or_lt with h | h
    · exfalso
      have : U ≤ 0 := by nlinarith
      linarith
    · exact h
  have hXsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hXpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hX2 : 2 * Z₁ ≤ Real.sqrt n := by
    have : Real.sqrt n * (2 * Z₁) ≤ Real.sqrt n * Real.sqrt n := by nlinarith
    exact le_of_mul_le_mul_left this hXpos
  have hU200 : 200 ≤ U := by linarith
  have hUpos : 0 < U := by linarith
  have h200U : 200 * U ≤ n := by nlinarith
  have hUn' : U ≤ n := by linarith
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = (n : ℝ) / (2 * U) := ⟨_, rfl⟩
  have hZ : (n : ℝ) = 2 * U * Z := by rw [hZdef]; field_simp
  have hZZ₁ : Z₁ ≤ Z := by rw [hZdef, le_div_iff₀ (by positivity)]; linarith
  have hZU : Z ≤ U := by nlinarith [mul_le_mul hXU hXU hX0 hU0]
  have hL1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨N, hN4, hN8⟩ := block_N U (by linarith)
  have hNL := block_Nbound N n U hUpos hUn' hN8 hL1
  have hrr : ∀ i : ℕ, 0 < rr i ∧ rr i ≤ 2 := by
    intro i
    have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    refine ⟨by unfold rr; positivity, ?_⟩
    unfold rr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hpt : ∀ u ∈ Set.Icc a (2 * U), ENNReal.ofReal ((W n u : ℝ) / u) ≤
      ENNReal.ofReal (2 / U + ∑ i ∈ range (N + 1), Real.log n / (rr i * β * U ^ 2) *
        ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
          (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2)) := by
    intro u hu
    apply ENNReal.ofReal_le_ofReal
    exact block_pt n U Z u β N hZ (by linarith) (by linarith) (le_trans hUa hu.1) hu.2
      (le_trans hXa hu.1) hβ (by linarith [hu.2]) (by linarith [hu.2])
  have hc0 : ∀ i, 0 ≤ Real.log n / (rr i * β * U ^ 2) := by
    intro i
    have := (hrr i).1
    positivity
  have heq : ∀ u : ℝ, ENNReal.ofReal (2 / U + ∑ i ∈ range (N + 1), Real.log n / (rr i * β * U ^ 2) *
        ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
          (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2)) =
      ENNReal.ofReal (2 / U) + ∑ i ∈ range (N + 1),
        (ENNReal.ofReal (Real.log n / (rr i * β * U ^ 2)) *
            ENNReal.ofReal ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2) +
          ENNReal.ofReal (Real.log n / (rr i * β * U ^ 2)) *
            ENNReal.ofReal ((2 * Bm (rr i) (kOf Z (rr i)) (n / u) /
              Real.log (n / u * Real.exp (-rr i))) ^ 2)) := by
    intro u
    rw [ENNReal.ofReal_add (by positivity)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hc0 i) (by positivity))),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hc0 i) (by positivity))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (hc0 i), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), mul_add]
  have hmP : ∀ i, Measurable (fun u : ℝ => ENNReal.ofReal (Real.log n / (rr i * β * U ^ 2)) *
      ENNReal.ofReal ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2)) := by
    intro i
    exact measurable_const.mul
      ((((measurable_Bp _ _).div Real.measurable_log).pow_const 2).ennreal_ofReal)
  have hmM : ∀ i, Measurable (fun u : ℝ => ENNReal.ofReal (Real.log n / (rr i * β * U ^ 2)) *
      ENNReal.ofReal ((2 * Bm (rr i) (kOf Z (rr i)) (n / u) /
        Real.log (n / u * Real.exp (-rr i))) ^ 2)) := by
    intro i
    have h1 := measurable_Bm (rr i) (kOf Z (rr i))
    fun_prop
  have hPi : ∀ i, ∫⁻ u in Set.Icc U (2 * U),
      ENNReal.ofReal ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2) ≤
        ENNReal.ofReal (Cp * U * (1 + U * rr i) * (Real.log U) ^ 2) := fun i =>
    block_mp Cp U (rr i) _ (by linarith) (hp U (by linarith) (rr i) (hrr i).1 (hrr i).2)
  have hMi : ∀ i, ∫⁻ u in Set.Icc U (2 * U),
      ENNReal.ofReal ((2 * Bm (rr i) (kOf Z (rr i)) (n / u) /
        Real.log (n / u * Real.exp (-rr i))) ^ 2) ≤
        ENNReal.ofReal (32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2) := fun i =>
    block_mm Cm n U Z (rr i) _ hUpos hZ (by linarith) (hrr i).1.le (hrr i).2
      (hm Z (by linarith) (rr i) (hrr i).1 (hrr i).2)
  set L := Real.log n with hLdef
  have hterm : ∀ i ∈ range (N + 1),
      L / (rr i * β * U ^ 2) * (Cp * U * (1 + U * rr i) * (Real.log U) ^ 2) +
      L / (rr i * β * U ^ 2) * (32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2)
      ≤ 5 * (Cp + 32 * Cm) * L ^ 3 / β := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hr0 := (hrr i).1
    have h2i : (2 : ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hiN
    have h4 : 1 ≤ 4 * (rr i * U) := by
      unfold rr
      rw [show 4 * (2 / 2 ^ i * U) = 8 * U / 2 ^ i by ring, le_div_iff₀ (by positivity)]
      linarith
    have hlU0 : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
    have hlUL : Real.log U ≤ L := Real.log_le_log hUpos hUn'
    have hlZ0 : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
    have hlZL : Real.log Z ≤ L := Real.log_le_log (by linarith) (by linarith)
    have hA : Cp * U * (1 + U * rr i) * (Real.log U) ^ 2 ≤ Cp * U * (1 + U * rr i) * L ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlU0 hlUL 2) (by positivity)
    have hB : 32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2 ≤
        32 * Cm * U * (1 + U * rr i) * L ^ 2 := by
      have h1 : 1 + Z * rr i ≤ 1 + U * rr i := by nlinarith
      have h2 := pow_le_pow_left₀ hlZ0 hlZL 2
      have : 0 ≤ 32 * Cm * U := by positivity
      calc 32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2
          = (32 * Cm * U) * ((1 + Z * rr i) * (Real.log Z) ^ 2) := by ring
        _ ≤ (32 * Cm * U) * ((1 + U * rr i) * L ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ this
            exact mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
        _ = _ := by ring
    calc _ = L / (rr i * β * U ^ 2) * (Cp * U * (1 + U * rr i) * (Real.log U) ^ 2 +
            32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2) := by ring
      _ ≤ L / (rr i * β * U ^ 2) * ((Cp + 32 * Cm) * U * (1 + U * rr i) * L ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (hc0 i)
          rw [show (Cp + 32 * Cm) * U * (1 + U * rr i) * L ^ 2 =
            Cp * U * (1 + U * rr i) * L ^ 2 + 32 * Cm * U * (1 + U * rr i) * L ^ 2 by ring]
          exact add_le_add hA hB
      _ = (Cp + 32 * Cm) * L ^ 3 / β * ((1 + U * rr i) / (rr i * U)) := by
          field_simp
      _ ≤ (Cp + 32 * Cm) * L ^ 3 / β * 5 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by positivity)]
          linarith
      _ = _ := by ring
  have hreal : 2 / U * U + ∑ i ∈ range (N + 1),
      (L / (rr i * β * U ^ 2) * (Cp * U * (1 + U * rr i) * (Real.log U) ^ 2) +
        L / (rr i * β * U ^ 2) * (32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2))
      ≤ (2 + 40 * (Cp + 32 * Cm)) * L ^ 4 / β := by
    have hs := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    have hK : 0 ≤ 5 * (Cp + 32 * Cm) * L ^ 3 / β := by positivity
    have h1 : ((N + 1 : ℕ) : ℝ) * (5 * (Cp + 32 * Cm) * L ^ 3 / β) ≤
        8 * L * (5 * (Cp + 32 * Cm) * L ^ 3 / β) := by
      apply mul_le_mul_of_nonneg_right _ hK
      push_cast
      exact hNL
    have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
    have h2 : L ^ 4 ≤ L ^ 4 / β := le_div_self (by positivity) hβ hβ1
    have h3 : 2 / U * U = 2 := div_mul_cancel₀ _ hUpos.ne'
    have h4 : 8 * L * (5 * (Cp + 32 * Cm) * L ^ 3 / β) = 40 * (Cp + 32 * Cm) * L ^ 4 / β := by ring
    have h5 : (2 + 40 * (Cp + 32 * Cm)) * L ^ 4 / β = 2 * (L ^ 4 / β) + 40 * (Cp + 32 * Cm) * L ^ 4 / β := by ring
    linarith
  calc (∫⁻ u in Set.Icc a (2 * U), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ∫⁻ u in Set.Icc a (2 * U), ENNReal.ofReal (2 / U + ∑ i ∈ range (N + 1),
          L / (rr i * β * U ^ 2) *
          ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
            (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ ∫⁻ u in Set.Icc U (2 * U), ENNReal.ofReal (2 / U + ∑ i ∈ range (N + 1),
          L / (rr i * β * U ^ 2) *
          ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2 +
            (2 * Bm (rr i) (kOf Z (rr i)) (n / u) / Real.log (n / u * Real.exp (-rr i))) ^ 2)) :=
        lintegral_mono_set (Set.Icc_subset_Icc_left hUa)
    _ = ENNReal.ofReal (2 / U) * ENNReal.ofReal U + ∑ i ∈ range (N + 1),
        (ENNReal.ofReal (L / (rr i * β * U ^ 2)) *
            (∫⁻ u in Set.Icc U (2 * U), ENNReal.ofReal ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2)) +
          ENNReal.ofReal (L / (rr i * β * U ^ 2)) *
            (∫⁻ u in Set.Icc U (2 * U), ENNReal.ofReal ((2 * Bm (rr i) (kOf Z (rr i)) (n / u) /
              Real.log (n / u * Real.exp (-rr i))) ^ 2))) := by
        have hmPM : ∀ i, Measurable (fun u : ℝ =>
            ENNReal.ofReal (L / (rr i * β * U ^ 2)) *
              ENNReal.ofReal ((Bp (rr i) (kOf U (rr i)) u / Real.log u) ^ 2) +
            ENNReal.ofReal (L / (rr i * β * U ^ 2)) *
              ENNReal.ofReal ((2 * Bm (rr i) (kOf Z (rr i)) (n / u) /
                Real.log (n / u * Real.exp (-rr i))) ^ 2)) := fun i => (hmP i).add (hmM i)
        simp_rw [heq]
        rw [lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Icc,
          show 2 * U - U = U by ring, lintegral_finsetSum _ (fun i _ => hmPM i)]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_add_left (hmP i), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 / U) * ENNReal.ofReal U + ∑ i ∈ range (N + 1),
        (ENNReal.ofReal (L / (rr i * β * U ^ 2)) *
            ENNReal.ofReal (Cp * U * (1 + U * rr i) * (Real.log U) ^ 2) +
          ENNReal.ofReal (L / (rr i * β * U ^ 2)) *
            ENNReal.ofReal (32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2)) := by
        gcongr with i hi
        · exact hPi i
        · exact hMi i
    _ = ENNReal.ofReal (2 / U * U + ∑ i ∈ range (N + 1),
      (L / (rr i * β * U ^ 2) * (Cp * U * (1 + U * rr i) * (Real.log U) ^ 2) +
        L / (rr i * β * U ^ 2) * (32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2))) := by
        have hA0 : ∀ i, 0 ≤ Cp * U * (1 + U * rr i) * (Real.log U) ^ 2 := by
          intro i; have := (hrr i).1; positivity
        have hB0 : ∀ i, 0 ≤ 32 * Cm * U * (1 + Z * rr i) * (Real.log Z) ^ 2 := by
          intro i; have := (hrr i).1; have : 0 ≤ Z := by linarith
          positivity
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun i _ =>
            add_nonneg (mul_nonneg (hc0 i) (hA0 i)) (mul_nonneg (hc0 i) (hB0 i)))),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ =>
            add_nonneg (mul_nonneg (hc0 i) (hA0 i)) (mul_nonneg (hc0 i) (hB0 i)))]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.ofReal_add (mul_nonneg (hc0 i) (hA0 i)) (mul_nonneg (hc0 i) (hB0 i)),
          ENNReal.ofReal_mul (hc0 i), ENNReal.ofReal_mul (hc0 i)]
    _ ≤ ENNReal.ofReal ((2 + 40 * (Cp + 32 * Cm)) * L ^ 4 / β) := ENNReal.ofReal_le_ofReal hreal

end Erdos879
