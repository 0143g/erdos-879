import Erdos879.Analytic.Defs

open Finset MeasureTheory

namespace Erdos879

theorem measurable_F : Measurable F := by
  unfold F
  exact Chebyshev.theta_mono.measurable.sub measurable_id

theorem msq_measurable_Dp (r : ℝ) (j l : ℕ) : Measurable (Dp r j l) := by
  unfold Dp
  have := measurable_F
  fun_prop

theorem msq_measurable_Dm (r : ℝ) (j l : ℕ) : Measurable (Dm r j l) := by
  unfold Dm
  have := measurable_F
  fun_prop

theorem measurable_Bp (r : ℝ) (k : ℕ) : Measurable (Bp r k) := by
  unfold Bp
  have := msq_measurable_Dp r
  fun_prop

theorem measurable_Bm (r : ℝ) (k : ℕ) : Measurable (Bm r k) := by
  unfold Bm
  have := msq_measurable_Dm r
  fun_prop

theorem msq_lintegral_Icc_comp_mul (g : ℝ → ENNReal) {a : ℝ} (ha : 0 < a) (A B : ℝ) :
    ∫⁻ y in Set.Icc A B, g (a * y)
      = ENNReal.ofReal a⁻¹ * ∫⁻ y in Set.Icc (a * A) (a * B), g y := by
  have he : MeasurableEmbedding (fun x : ℝ => a * x) := measurableEmbedding_mulLeft₀ ha.ne'
  have h1 := Real.map_volume_mul_left ha.ne'
  have h2 : (fun x : ℝ => a * x) ⁻¹' Set.Icc (a * A) (a * B) = Set.Icc A B := by
    rw [Set.preimage_const_mul_Icc₀ _ _ ha, mul_div_cancel_left₀ _ ha.ne',
      mul_div_cancel_left₀ _ ha.ne']
  calc ∫⁻ y in Set.Icc A B, g (a * y)
      = ∫⁻ y, g y ∂((volume.restrict (Set.Icc A B)).map (fun x => a * x)) :=
        (he.lintegral_map g).symm
    _ = ∫⁻ y, g y ∂((volume.map (fun x => a * x)).restrict (Set.Icc (a * A) (a * B))) := by
        rw [he.restrict_map, h2]
    _ = _ := by
        rw [h1, Measure.restrict_smul, lintegral_smul_measure, abs_of_pos (inv_pos.2 ha)]
        rfl


theorem msq_selberg_lintegral (hS : SelbergMS) :
    ∃ C X δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ x : ℝ, X ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∫⁻ y in Set.Icc 1 x, ENNReal.ofReal ((F (y * (1 + δ)) - F y) ^ 2)
        ≤ ENNReal.ofReal (C * δ * x ^ 2 * (Real.log x) ^ 2) := by
  obtain ⟨C, x₀, δ₀, hδ₀, h⟩ := hS
  refine ⟨max C 1, max x₀ 1, δ₀, by positivity, hδ₀, fun x hx δ hδ hδle => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  set f : ℝ → ℝ := fun y =>
    (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2 with hf
  have key : ∀ y, (F (y * (1 + δ)) - F y) ^ 2 = f y := by
    intro y
    have : y * (1 + δ) = y + δ * y := by ring
    rw [hf]
    unfold F
    rw [this]
    ring
  have hθ : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
  have hmeas : Measurable f := by
    rw [hf]
    fun_prop
  have hint : IntegrableOn f (Set.Ioc 1 x) volume := by
    refine Measure.integrableOn_of_bounded (M := (Chebyshev.theta (x + δ * x)
      + Chebyshev.theta x + δ * x) ^ 2) measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun y hy => ?_
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have h1 : Chebyshev.theta (y + δ * y) ≤ Chebyshev.theta (x + δ * x) :=
      Chebyshev.theta_mono (by nlinarith [hy.2])
    have h2 : Chebyshev.theta y ≤ Chebyshev.theta x := Chebyshev.theta_mono hy.2
    have h3 := Chebyshev.theta_nonneg (y + δ * y)
    have h4 := Chebyshev.theta_nonneg y
    have h5 : δ * y ≤ δ * x := by nlinarith [hy.2]
    have h6 : 0 ≤ δ * y := by positivity
    rw [Real.norm_eq_abs, hf]
    simp only
    rw [abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 1 x)] f :=
    Filter.Eventually.of_forall fun y => by rw [hf]; positivity
  calc ∫⁻ y in Set.Icc 1 x, ENNReal.ofReal ((F (y * (1 + δ)) - F y) ^ 2)
      = ∫⁻ y in Set.Ioc 1 x, ENNReal.ofReal (f y) := by
        rw [setLIntegral_congr Ioc_ae_eq_Icc.symm]
        simp only [key]
    _ = ENNReal.ofReal (∫ y in (1 : ℝ)..x, f y) := by
        rw [intervalIntegral.integral_of_le hx1, ofReal_integral_eq_lintegral_ofReal hint hnn]
    _ ≤ ENNReal.ofReal (C * δ * x ^ 2 * (Real.log x) ^ 2) := ENNReal.ofReal_le_ofReal (h x hx0 δ hδ hδle)
    _ ≤ ENNReal.ofReal (max C 1 * δ * x ^ 2 * (Real.log x) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ δ * x ^ 2 * (Real.log x) ^ 2 := by positivity
        have := le_max_left C 1
        nlinarith

theorem msq_exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

theorem msq_selberg_small (C X δ₀ : ℝ) (hC : 0 < C)
    (h : ∀ x : ℝ, X ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∫⁻ y in Set.Icc 1 x, ENNReal.ofReal ((F (y * (1 + δ)) - F y) ^ 2)
        ≤ ENNReal.ofReal (C * δ * x ^ 2 * (Real.log x) ^ 2)) :
    ∀ x : ℝ, X ≤ x → ∀ w : ℝ, 0 < w → w ≤ min 1 (δ₀ / 2) →
      ∫⁻ y in Set.Icc 1 x, ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
        ≤ ENNReal.ofReal (2 * C * w * x ^ 2 * (Real.log x) ^ 2) := by
  intro x hx w hw hwle
  have hw1 : w ≤ 1 := le_trans hwle (min_le_left _ _)
  have hw2 : w ≤ δ₀ / 2 := le_trans hwle (min_le_right _ _)
  have hlt := Real.add_one_lt_exp hw.ne'
  have hb : |Real.exp w - 1| ≤ 2 * |w| :=
    Real.abs_exp_sub_one_le (by rw [abs_of_pos hw]; exact hw1)
  have hpos : 0 < Real.exp w - 1 := by linarith
  rw [abs_of_pos hw, abs_of_pos hpos] at hb
  have h' := h x hx (Real.exp w - 1) hpos (by linarith)
  have he : ∀ y : ℝ, y * (1 + (Real.exp w - 1)) = y * Real.exp w := fun y => by ring
  simp only [he] at h'
  refine h'.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ x ^ 2 * (Real.log x) ^ 2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg hC.le (by linarith : 0 ≤ 2 * w - (Real.exp w - 1))) h0]

theorem selberg_mult (hS : SelbergMS) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ w : ℝ, 0 < w → w ≤ 2 →
      ∫⁻ y in Set.Icc (Z / 8) (16 * Z), ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
        ≤ ENNReal.ofReal (C * Z ^ 2 * w * (Real.log Z) ^ 2) := by
  obtain ⟨C₀, X, δ₀, hC₀, hδ₀, h₀⟩ := msq_selberg_lintegral hS
  have h := msq_selberg_small C₀ X δ₀ hC₀ h₀
  set w₁ : ℝ := min 1 (δ₀ / 2) with hw₁def
  have hw₁ : 0 < w₁ := by positivity
  set m : ℕ := ⌈2 / w₁⌉₊ + 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by
    rw [hm]; push_cast; linarith [(Nat.cast_nonneg ⌈2 / w₁⌉₊ : (0 : ℝ) ≤ _)]
  have hm0 : (0 : ℝ) < m := by linarith
  have hmw : 2 / w₁ ≤ m := by
    rw [hm]; push_cast; linarith [Nat.le_ceil (2 / w₁)]
  refine ⟨4 * 128 ^ 2 * m * (2 * C₀), max X 128, by positivity, fun Z hZ w hw hw2 => ?_⟩
  have hZ128 : 128 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZX : X ≤ 128 * Z := by linarith [le_max_left X 128]
  set w' : ℝ := w / m with hw'def
  have hw'pos : 0 < w' := by positivity
  have hmw' : (m : ℝ) * w' = w := by rw [hw'def]; field_simp
  have hw'le : w' ≤ w₁ := by
    rw [hw'def, div_le_iff₀ hm0]
    rw [div_le_iff₀ hw₁] at hmw
    linarith
  set g : ℝ → ENNReal := fun y => ENNReal.ofReal ((F (y * Real.exp w') - F y) ^ 2) with hg
  set B : ℝ := 2 * C₀ * w' * (128 * Z) ^ 2 * (Real.log (128 * Z)) ^ 2 with hB
  have hbase : ∫⁻ y in Set.Icc 1 (128 * Z), g y ≤ ENNReal.ofReal B := h _ hZX w' hw'pos hw'le
  have hterm : ∀ l ∈ range m, ∫⁻ y in Set.Icc (Z / 8) (16 * Z),
      ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w')) - F (y * Real.exp ((l : ℝ) * w'))) ^ 2)
        ≤ ENNReal.ofReal B := by
    intro l hl
    have hl' : (l : ℝ) + 1 ≤ m := by
      have := Finset.mem_range.1 hl
      exact_mod_cast this
    set a : ℝ := Real.exp ((l : ℝ) * w') with ha
    have ha0 : 0 < a := Real.exp_pos _
    have ha1 : 1 ≤ a := Real.one_le_exp (by positivity)
    have ha8 : a ≤ 8 := by
      have : (l : ℝ) * w' ≤ 2 := by nlinarith
      exact le_trans (Real.exp_le_exp.2 this) msq_exp_two_lt_eight.le
    have hfun : ∀ y : ℝ, ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w'))
        - F (y * a)) ^ 2) = g (a * y) := by
      intro y
      have e1 : y * Real.exp (((l : ℝ) + 1) * w') = a * y * Real.exp w' := by
        rw [ha, add_mul, one_mul, Real.exp_add]; ring
      have e2 : y * a = a * y := by ring
      rw [e1, e2]
    simp only [hfun]
    rw [msq_lintegral_Icc_comp_mul g ha0]
    calc ENNReal.ofReal a⁻¹ * ∫⁻ y in Set.Icc (a * (Z / 8)) (a * (16 * Z)), g y
        ≤ 1 * ∫⁻ y in Set.Icc 1 (128 * Z), g y := by
          refine mul_le_mul' ?_ (lintegral_mono_set (Set.Icc_subset_Icc ?_ ?_))
          · rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ha1)
          · nlinarith
          · nlinarith
      _ ≤ ENNReal.ofReal B := by rw [one_mul]; exact hbase
  have hpt : ∀ y : ℝ, ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
      ≤ ∑ l ∈ range m, ENNReal.ofReal (m : ℝ) * ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w'))
        - F (y * Real.exp ((l : ℝ) * w'))) ^ 2) := by
    intro y
    have htel := Finset.sum_range_sub (fun l : ℕ => F (y * Real.exp ((l : ℝ) * w'))) m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one,
      hmw'] at htel
    rw [← htel, ← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have := sq_sum_le_card_mul_sum_sq (s := range m)
      (f := fun l : ℕ => F (y * Real.exp (((l : ℝ) + 1) * w')) - F (y * Real.exp ((l : ℝ) * w')))
    simpa using this
  have hmeasl : ∀ l ∈ range m, Measurable (fun y : ℝ => ENNReal.ofReal (m : ℝ) *
      ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w')) - F (y * Real.exp ((l : ℝ) * w'))) ^ 2)) := by
    intro l _
    have := measurable_F
    fun_prop
  have hL : 0 ≤ Real.log (128 * Z) := Real.log_nonneg (by linarith)
  have hL2 : Real.log (128 * Z) ≤ 2 * Real.log Z := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 128 ≤ Real.log Z := Real.log_le_log (by norm_num) hZ128
    linarith
  have hLsq : (Real.log (128 * Z)) ^ 2 ≤ 4 * (Real.log Z) ^ 2 := by
    have := pow_le_pow_left₀ hL hL2 2
    nlinarith
  calc ∫⁻ y in Set.Icc (Z / 8) (16 * Z), ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
      ≤ ∫⁻ y in Set.Icc (Z / 8) (16 * Z), ∑ l ∈ range m, ENNReal.ofReal (m : ℝ) *
          ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w'))
            - F (y * Real.exp ((l : ℝ) * w'))) ^ 2) := lintegral_mono hpt
    _ = ∑ l ∈ range m, ENNReal.ofReal (m : ℝ) * ∫⁻ y in Set.Icc (Z / 8) (16 * Z),
          ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w'))
            - F (y * Real.exp ((l : ℝ) * w'))) ^ 2) := by
        rw [lintegral_finsetSum _ hmeasl]
        refine Finset.sum_congr rfl fun l _ => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑ l ∈ range m, ENNReal.ofReal (m : ℝ) * ENNReal.ofReal B :=
        Finset.sum_le_sum fun l hl => by gcongr; exact hterm l hl
    _ = ENNReal.ofReal ((m : ℝ) * m * B) := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ (m : ℝ) * m by positivity),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ (m : ℝ) by positivity), ENNReal.ofReal_natCast,
          mul_assoc]
    _ ≤ ENNReal.ofReal (4 * 128 ^ 2 * m * (2 * C₀) * Z ^ 2 * w * (Real.log Z) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have e : (m : ℝ) * m * B = (128 ^ 2 * m * (2 * C₀) * Z ^ 2 * w) * (Real.log (128 * Z)) ^ 2 := by
          rw [hB, ← hmw']; ring
        rw [e]
        have : 0 ≤ 128 ^ 2 * m * (2 * C₀) * Z ^ 2 * w := by positivity
        calc (128 ^ 2 * m * (2 * C₀) * Z ^ 2 * w) * (Real.log (128 * Z)) ^ 2
            ≤ (128 ^ 2 * m * (2 * C₀) * Z ^ 2 * w) * (4 * (Real.log Z) ^ 2) :=
              mul_le_mul_of_nonneg_left hLsq this
          _ = _ := by ring

theorem msq_generic (K : ℕ) (Z A : ℝ) (hZ : 0 ≤ Z) (hA : 0 ≤ A)
    (D : ℕ → ℕ → ℝ → ℝ) (hD : ∀ j l, Measurable (D j l)) (c : ℝ → ℝ)
    (hc0 : ∀ y ∈ Set.Icc Z (2 * Z), 0 ≤ c y ∧ c y ≤ 32)
    (hint : ∀ j ∈ range K, ∀ l ∈ range (2 ^ j),
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((D j l y) ^ 2) ≤ ENNReal.ofReal (A / 2 ^ j)) :
    ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((2 * ∑ j ∈ range K,
        Real.sqrt (∑ l ∈ range (2 ^ j), (D j l y) ^ 2) + c y) ^ 2)
      ≤ ENNReal.ofReal (8 * K ^ 2 * A + 2048 * Z) := by
  have hpt : ∀ y ∈ Set.Icc Z (2 * Z), ENNReal.ofReal ((2 * ∑ j ∈ range K,
        Real.sqrt (∑ l ∈ range (2 ^ j), (D j l y) ^ 2) + c y) ^ 2)
      ≤ ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          ENNReal.ofReal ((D j l y) ^ 2) + ENNReal.ofReal 2048 := by
    intro y hy
    obtain ⟨hc1, hc2⟩ := hc0 y hy
    have hT : ∀ j, 0 ≤ ∑ l ∈ range (2 ^ j), (D j l y) ^ 2 :=
      fun j => Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have hsq : ∀ j, Real.sqrt (∑ l ∈ range (2 ^ j), (D j l y) ^ 2) ^ 2
        = ∑ l ∈ range (2 ^ j), (D j l y) ^ 2 := fun j => Real.sq_sqrt (hT j)
    have hCS := sq_sum_le_card_mul_sum_sq (s := range K)
      (f := fun j => Real.sqrt (∑ l ∈ range (2 ^ j), (D j l y) ^ 2))
    simp only [card_range, hsq] at hCS
    have hS0 : 0 ≤ ∑ j ∈ range K, Real.sqrt (∑ l ∈ range (2 ^ j), (D j l y) ^ 2) :=
      Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
    have hT0 : 0 ≤ ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), (D j l y) ^ 2 :=
      Finset.sum_nonneg (fun j _ => hT j)
    have e : ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          ENNReal.ofReal ((D j l y) ^ 2) + ENNReal.ofReal 2048
        = ENNReal.ofReal (8 * K * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), (D j l y) ^ 2 + 2048) := by
      rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hT0) (by norm_num),
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * (K : ℝ) by positivity),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => hT j)]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _)]
    rw [e]
    apply ENNReal.ofReal_le_ofReal
    set S := ∑ j ∈ range K, Real.sqrt (∑ l ∈ range (2 ^ j), (D j l y) ^ 2)
    set T := ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), (D j l y) ^ 2
    nlinarith [sq_nonneg (2 * S - c y)]
  have hmeas : ∀ j l, Measurable (fun y => ENNReal.ofReal ((D j l y) ^ 2)) := by
    intro j l
    have := hD j l
    fun_prop
  calc ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((2 * ∑ j ∈ range K,
        Real.sqrt (∑ l ∈ range (2 ^ j), (D j l y) ^ 2) + c y) ^ 2)
      ≤ ∫⁻ y in Set.Icc Z (2 * Z), (ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          ENNReal.ofReal ((D j l y) ^ 2) + ENNReal.ofReal 2048) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          (∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((D j l y) ^ 2))
          + ENNReal.ofReal 2048 * volume (Set.Icc Z (2 * Z)) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const]
        congr 2
        rw [lintegral_finsetSum _ (fun j _ => Finset.measurable_sum _ (fun l _ => hmeas j l))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ (fun l _ => hmeas j l)]
    _ ≤ ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), ENNReal.ofReal (A / 2 ^ j)
          + ENNReal.ofReal 2048 * ENNReal.ofReal Z := by
        rw [Real.volume_Icc, show 2 * Z - Z = Z by ring]
        gcongr with j hj l hl
        exact hint j hj l hl
    _ = ENNReal.ofReal (8 * K ^ 2 * A + 2048 * Z) := by
        have e1 : ∀ j : ℕ, ∑ l ∈ range (2 ^ j), ENNReal.ofReal (A / 2 ^ j) = ENNReal.ofReal A := by
          intro j
          rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity), Finset.sum_const,
            card_range, nsmul_eq_mul]
          congr 1
          push_cast
          field_simp
        simp only [e1, Finset.sum_const, card_range, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem msq_kOf_facts (Z r : ℝ) (hZ : 3 ≤ Z) (hr : 0 < r) (hr2 : r ≤ 2) :
    Z * r ≤ 2 ^ kOf Z r ∧ (kOf Z r : ℝ) + 1 ≤ 6 * Real.log Z := by
  have hZr : 0 < Z * r := by positivity
  have hb : (1 : ℝ) < 2 := by norm_num
  constructor
  · have h1 : Real.logb 2 (Z * r) ≤ (kOf Z r : ℝ) := Nat.le_ceil _
    rw [Real.logb_le_iff_le_rpow hb hZr, Real.rpow_natCast] at h1
    exact h1
  · have hlogZ : 1 ≤ Real.log Z := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_three]
    have h1 : (kOf Z r : ℝ) ≤ ⌈max (Real.logb 2 (Z * r)) 0⌉₊ := by
      unfold kOf
      exact_mod_cast Nat.ceil_mono (le_max_left _ _)
    have h2 : (⌈max (Real.logb 2 (Z * r)) 0⌉₊ : ℝ) < max (Real.logb 2 (Z * r)) 0 + 1 :=
      Nat.ceil_lt_add_one (le_max_right _ _)
    have h3 : max (Real.logb 2 (Z * r)) 0 ≤ Real.logb 2 (2 * Z) := by
      apply max_le
      · exact Real.logb_le_logb_of_le hb hZr (by nlinarith)
      · exact Real.logb_nonneg hb (by linarith)
    have h4 : Real.logb 2 (2 * Z) = 1 + Real.log Z / Real.log 2 := by
      rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one hb]
      rfl
    have hl2 := Real.log_two_gt_d9
    have hl2' : 0 < Real.log 2 := by linarith
    have h5 : Real.log Z / Real.log 2 ≤ 2 * Real.log Z := by
      rw [div_le_iff₀ hl2']
      nlinarith
    linarith

theorem msq_scaled_bound (g : ℝ → ENNReal) {a Z : ℝ} (ha : 0 < a) (h1 : Z / 8 ≤ a * Z)
    (h2 : a * (2 * Z) ≤ 16 * Z) :
    ∫⁻ y in Set.Icc Z (2 * Z), g (a * y)
      ≤ ENNReal.ofReal a⁻¹ * ∫⁻ y in Set.Icc (Z / 8) (16 * Z), g y := by
  rw [msq_lintegral_Icc_comp_mul g ha]
  exact mul_le_mul' le_rfl (lintegral_mono_set (Set.Icc_subset_Icc h1 h2))

theorem msq_final_ineq (Z r L C₁ : ℝ) (k : ℕ) (hZ : 0 ≤ Z) (hr : 0 ≤ r) (hC : 0 ≤ C₁)
    (hL : 1 ≤ L) (hk : (k : ℝ) + 1 ≤ 6 * L) :
    8 * (((k + 1 : ℕ) : ℝ)) ^ 2 * (C₁ * Z ^ 2 * r * L ^ 2) + 2048 * Z
      ≤ (288 * C₁ + 2048) * Z * (1 + Z * r) * L ^ 4 := by
  push_cast
  have hk2 : ((k : ℝ) + 1) ^ 2 ≤ 36 * L ^ 2 := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    nlinarith
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hZr : 0 ≤ Z * r := by positivity
  have e1 : 8 * ((k : ℝ) + 1) ^ 2 * (C₁ * Z ^ 2 * r * L ^ 2)
      ≤ 8 * (36 * L ^ 2) * (C₁ * Z ^ 2 * r * L ^ 2) := by
    gcongr
  have e2 : 8 * (36 * L ^ 2) * (C₁ * Z ^ 2 * r * L ^ 2) = 288 * C₁ * Z * (Z * r) * L ^ 4 := by
    ring
  have e3 : 288 * C₁ * Z * (Z * r) * L ^ 4 ≤ 288 * C₁ * Z * (1 + Z * r) * L ^ 4 := by
    gcongr
    linarith
  have e4 : 2048 * Z ≤ 2048 * Z * (1 + Z * r) * L ^ 4 := by
    have : 1 ≤ (1 + Z * r) * L ^ 4 := by nlinarith
    nlinarith
  nlinarith

theorem ms_Bp (hS : SelbergMS) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bp r (kOf Z r) y) ^ 2)
        ≤ ENNReal.ofReal (C * Z * (1 + Z * r) * (Real.log Z) ^ 4) := by
  obtain ⟨C₁, Z₁, hC₁, h₁⟩ := selberg_mult hS
  refine ⟨288 * C₁ + 2048, max Z₁ 3, by positivity, fun Z hZ r hr hr2 => ?_⟩
  have hZ3 : 3 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZ1 : Z₁ ≤ Z := le_trans (le_max_left _ _) hZ
  obtain ⟨hk1, hk2⟩ := msq_kOf_facts Z r hZ3 hr hr2
  have hlog : 1 ≤ Real.log Z := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have he2 := msq_exp_two_lt_eight
  have hint : ∀ j ∈ range (kOf Z r + 1), ∀ l ∈ range (2 ^ j),
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Dp r j l y) ^ 2)
        ≤ ENNReal.ofReal (C₁ * Z ^ 2 * r * (Real.log Z) ^ 2 / 2 ^ j) := by
    intro j _ l hl
    have hl' : (l : ℝ) + 1 ≤ 2 ^ j := by
      have := Finset.mem_range.1 hl
      exact_mod_cast this
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have hw : 0 < r / 2 ^ j := by positivity
    have hw2 : r / 2 ^ j ≤ 2 := by
      have : r / 2 ^ j ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num))
      linarith
    have ht : (l : ℝ) * r / 2 ^ j ≤ 2 := by
      rw [div_le_iff₀ h2j]; nlinarith
    have ha0 : 0 < Real.exp ((l : ℝ) * r / 2 ^ j) := Real.exp_pos _
    have ha1 : 1 ≤ Real.exp ((l : ℝ) * r / 2 ^ j) := Real.one_le_exp (by positivity)
    have ha8 : Real.exp ((l : ℝ) * r / 2 ^ j) ≤ 8 := le_trans (Real.exp_le_exp.2 ht) he2.le
    have hfun : ∀ y : ℝ, ENNReal.ofReal ((Dp r j l y) ^ 2)
        = (fun y' => ENNReal.ofReal ((F (y' * Real.exp (r / 2 ^ j)) - F y') ^ 2))
          (Real.exp ((l : ℝ) * r / 2 ^ j) * y) := by
      intro y
      unfold Dp
      have e1 : y * Real.exp (((l : ℝ) + 1) * r / 2 ^ j)
          = Real.exp ((l : ℝ) * r / 2 ^ j) * y * Real.exp (r / 2 ^ j) := by
        rw [show ((l : ℝ) + 1) * r / 2 ^ j = (l : ℝ) * r / 2 ^ j + r / 2 ^ j by ring,
          Real.exp_add]
        ring
      rw [e1, mul_comm y]
    simp only [hfun]
    refine (msq_scaled_bound (fun y' => ENNReal.ofReal ((F (y' * Real.exp (r / 2 ^ j)) - F y') ^ 2))
      ha0 (by nlinarith) (by nlinarith)).trans ?_
    calc ENNReal.ofReal (Real.exp ((l : ℝ) * r / 2 ^ j))⁻¹ * ∫⁻ y in Set.Icc (Z / 8) (16 * Z),
          ENNReal.ofReal ((F (y * Real.exp (r / 2 ^ j)) - F y) ^ 2)
        ≤ 1 * ENNReal.ofReal (C₁ * Z ^ 2 * (r / 2 ^ j) * (Real.log Z) ^ 2) := by
          refine mul_le_mul' ?_ (h₁ Z hZ1 _ hw hw2)
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ha1)
      _ = ENNReal.ofReal (C₁ * Z ^ 2 * r * (Real.log Z) ^ 2 / 2 ^ j) := by
          rw [one_mul]; congr 1; ring
  have hc : ∀ y ∈ Set.Icc Z (2 * Z), 0 ≤ y * Real.exp r * (Real.exp (r / 2 ^ kOf Z r) - 1)
      ∧ y * Real.exp r * (Real.exp (r / 2 ^ kOf Z r) - 1) ≤ 32 := by
    intro y hy
    have h2k : (0 : ℝ) < 2 ^ kOf Z r := by positivity
    have hμ : 0 < r / 2 ^ kOf Z r := by positivity
    have hZμ : Z * (r / 2 ^ kOf Z r) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one h2k]; exact hk1
    have hμ1 : r / 2 ^ kOf Z r ≤ 1 := by nlinarith
    have hb := Real.abs_exp_sub_one_le (x := r / 2 ^ kOf Z r) (by rw [abs_of_pos hμ]; exact hμ1)
    have hlt := Real.add_one_lt_exp hμ.ne'
    rw [abs_of_pos hμ, abs_of_pos (by linarith)] at hb
    have her : Real.exp r ≤ 8 := le_trans (Real.exp_le_exp.2 hr2) he2.le
    have her0 := Real.exp_pos r
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hpos : 0 ≤ Real.exp (r / 2 ^ kOf Z r) - 1 := by linarith
    constructor
    · positivity
    · calc y * Real.exp r * (Real.exp (r / 2 ^ kOf Z r) - 1)
          ≤ (2 * Z) * 8 * (2 * (r / 2 ^ kOf Z r)) := by
            apply mul_le_mul (mul_le_mul hy.2 her her0.le (by linarith)) hb hpos (by positivity)
        _ = 32 * (Z * (r / 2 ^ kOf Z r)) := by ring
        _ ≤ 32 := by linarith
  have key := msq_generic (kOf Z r + 1) Z (C₁ * Z ^ 2 * r * (Real.log Z) ^ 2) (by linarith)
    (by positivity) (Dp r) (msq_measurable_Dp r) _ hc hint
  refine le_trans (le_of_eq ?_) (key.trans (ENNReal.ofReal_le_ofReal
    (msq_final_ineq Z r (Real.log Z) C₁ (kOf Z r) (by linarith) hr.le hC₁.le hlog hk2)))
  rfl

theorem ms_Bm (hS : SelbergMS) :
    ∃ C Z₀ : ℝ, 0 < C ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Bm r (kOf Z r) y) ^ 2)
        ≤ ENNReal.ofReal (C * Z * (1 + Z * r) * (Real.log Z) ^ 4) := by
  obtain ⟨C₁, Z₁, hC₁, h₁⟩ := selberg_mult hS
  refine ⟨288 * (8 * C₁) + 2048, max Z₁ 3, by positivity, fun Z hZ r hr hr2 => ?_⟩
  have hZ3 : 3 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZ1 : Z₁ ≤ Z := le_trans (le_max_left _ _) hZ
  obtain ⟨hk1, hk2⟩ := msq_kOf_facts Z r hZ3 hr hr2
  have hlog : 1 ≤ Real.log Z := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have he2 := msq_exp_two_lt_eight
  have hint : ∀ j ∈ range (kOf Z r + 1), ∀ l ∈ range (2 ^ j),
      ∫⁻ y in Set.Icc Z (2 * Z), ENNReal.ofReal ((Dm r j l y) ^ 2)
        ≤ ENNReal.ofReal (8 * C₁ * Z ^ 2 * r * (Real.log Z) ^ 2 / 2 ^ j) := by
    intro j _ l hl
    have hl' : (l : ℝ) + 1 ≤ 2 ^ j := by
      have := Finset.mem_range.1 hl
      exact_mod_cast this
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have hw : 0 < r / 2 ^ j := by positivity
    have hw2 : r / 2 ^ j ≤ 2 := by
      have : r / 2 ^ j ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num))
      linarith
    have ht : ((l : ℝ) + 1) * r / 2 ^ j ≤ 2 := by
      rw [div_le_iff₀ h2j]; nlinarith
    have ht0 : 0 ≤ ((l : ℝ) + 1) * r / 2 ^ j := by positivity
    have ha0 : 0 < Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) := Real.exp_pos _
    have ha1 : Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have ha8 : (Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)))⁻¹ ≤ 8 := by
      rw [← Real.exp_neg, neg_neg]
      exact le_trans (Real.exp_le_exp.2 ht) he2.le
    have h18 : 1 ≤ 8 * Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) := by
      have := mul_inv_cancel₀ ha0.ne'
      nlinarith
    have hfun : ∀ y : ℝ, ENNReal.ofReal ((Dm r j l y) ^ 2)
        = (fun y' => ENNReal.ofReal ((F (y' * Real.exp (r / 2 ^ j)) - F y') ^ 2))
          (Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) * y) := by
      intro y
      unfold Dm
      have e1 : y * Real.exp (-((l : ℝ) * r / 2 ^ j))
          = Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) * y * Real.exp (r / 2 ^ j) := by
        rw [show -((l : ℝ) * r / 2 ^ j) = -(((l : ℝ) + 1) * r / 2 ^ j) + r / 2 ^ j by ring,
          Real.exp_add]
        ring
      rw [e1, mul_comm y]
    simp only [hfun]
    refine (msq_scaled_bound (fun y' => ENNReal.ofReal ((F (y' * Real.exp (r / 2 ^ j)) - F y') ^ 2))
      ha0 (by nlinarith) (by nlinarith)).trans ?_
    calc ENNReal.ofReal (Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)))⁻¹
          * ∫⁻ y in Set.Icc (Z / 8) (16 * Z),
            ENNReal.ofReal ((F (y * Real.exp (r / 2 ^ j)) - F y) ^ 2)
        ≤ ENNReal.ofReal 8 * ENNReal.ofReal (C₁ * Z ^ 2 * (r / 2 ^ j) * (Real.log Z) ^ 2) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal ha8) (h₁ Z hZ1 _ hw hw2)
      _ = ENNReal.ofReal (8 * C₁ * Z ^ 2 * r * (Real.log Z) ^ 2 / 2 ^ j) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have hc : ∀ y ∈ Set.Icc Z (2 * Z), 0 ≤ y * (Real.exp (r / 2 ^ kOf Z r) - 1)
      ∧ y * (Real.exp (r / 2 ^ kOf Z r) - 1) ≤ 32 := by
    intro y hy
    have h2k : (0 : ℝ) < 2 ^ kOf Z r := by positivity
    have hμ : 0 < r / 2 ^ kOf Z r := by positivity
    have hZμ : Z * (r / 2 ^ kOf Z r) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one h2k]; exact hk1
    have hμ1 : r / 2 ^ kOf Z r ≤ 1 := by nlinarith
    have hb := Real.abs_exp_sub_one_le (x := r / 2 ^ kOf Z r) (by rw [abs_of_pos hμ]; exact hμ1)
    have hlt := Real.add_one_lt_exp hμ.ne'
    rw [abs_of_pos hμ, abs_of_pos (by linarith)] at hb
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hpos : 0 ≤ Real.exp (r / 2 ^ kOf Z r) - 1 := by linarith
    constructor
    · positivity
    · calc y * (Real.exp (r / 2 ^ kOf Z r) - 1)
          ≤ (2 * Z) * (2 * (r / 2 ^ kOf Z r)) :=
            mul_le_mul hy.2 hb hpos (by positivity)
        _ = 4 * (Z * (r / 2 ^ kOf Z r)) := by ring
        _ ≤ 32 := by linarith
  have key := msq_generic (kOf Z r + 1) Z (8 * C₁ * Z ^ 2 * r * (Real.log Z) ^ 2) (by linarith)
    (by positivity) (Dm r) (msq_measurable_Dm r) _ hc hint
  refine le_trans (le_of_eq ?_) (key.trans (ENNReal.ofReal_le_ofReal
    (msq_final_ineq Z r (Real.log Z) (8 * C₁) (kOf Z r) (by linarith) hr.le (by positivity) hlog hk2)))
  rfl

end Erdos879
