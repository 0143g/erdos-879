import Erdos879.Analytic.Block
import Erdos879.Measurable

open Finset MeasureTheory

namespace Erdos879

def HypothesisLSAt (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ η : ℝ, x ^ (-θ) ≤ η → η ≤ 1 →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∫ y in x..(x * (1 + η)), (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2
        ≤ C * δ * η * x ^ (2 + ε)

def HypothesisLS : Prop := HypothesisLSAt (1 / 2)

def LocLS (θ C ε : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∀ η : ℝ, x ^ (-θ) ≤ η → η ≤ 1 →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∫ y in x..(x * (1 + η)), (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2
        ≤ C * δ * η * x ^ (2 + ε)

theorem loc_base (θ C ε : ℝ) (hC0 : 0 ≤ C) (hC : LocLS θ C ε) (x η : ℝ) (hx : 2 ≤ x)
    (hη : x ^ (-θ) ≤ η) (hη1 : η ≤ 1) (w : ℝ) (hw : 0 < w) (hw2 : w ≤ 1 / 2) :
    ∫⁻ y in Set.Icc x (x * (1 + η)), ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
      ≤ ENNReal.ofReal (C * (2 * w) * η * x ^ (2 + ε)) := by
  have hx0 : 0 < x := by linarith
  have hηpos : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hη
  set b := x * (1 + η) with hbdef
  have hxb : x ≤ b := by rw [hbdef]; nlinarith
  set δ := Real.exp w - 1 with hδdef
  have hlt := Real.add_one_lt_exp hw.ne'
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hb2 : |Real.exp w - 1| ≤ 2 * |w| :=
    Real.abs_exp_sub_one_le (by rw [abs_of_pos hw]; linarith)
  rw [abs_of_pos hw, abs_of_pos (by linarith)] at hb2
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  set f : ℝ → ℝ := fun y =>
    (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2 with hf
  have key : ∀ y, (F (y * Real.exp w) - F y) ^ 2 = f y := by
    intro y
    have : y * Real.exp w = y + δ * y := by rw [hδdef]; ring
    rw [hf]
    unfold F
    rw [this]
    ring
  have hθ : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
  have hmeas : Measurable f := by
    rw [hf]
    fun_prop
  have hint : IntegrableOn f (Set.Ioc x b) volume := by
    refine Measure.integrableOn_of_bounded (M := (Chebyshev.theta (b + δ * b)
      + Chebyshev.theta b + δ * b) ^ 2) measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun y hy => ?_
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have h1 : Chebyshev.theta (y + δ * y) ≤ Chebyshev.theta (b + δ * b) :=
      Chebyshev.theta_mono (by nlinarith [hy.2])
    have h2 : Chebyshev.theta y ≤ Chebyshev.theta b := Chebyshev.theta_mono hy.2
    have h3 := Chebyshev.theta_nonneg (y + δ * y)
    have h4 := Chebyshev.theta_nonneg y
    have h5 : δ * y ≤ δ * b := by nlinarith [hy.2]
    have h6 : 0 ≤ δ * y := by positivity
    rw [Real.norm_eq_abs, hf]
    simp only
    rw [abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc x b)] f :=
    Filter.Eventually.of_forall fun y => by rw [hf]; positivity
  have hxe : 0 ≤ x ^ (2 + ε) := Real.rpow_nonneg hx0.le _
  calc ∫⁻ y in Set.Icc x b, ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
      = ∫⁻ y in Set.Ioc x b, ENNReal.ofReal (f y) := by
        rw [setLIntegral_congr Ioc_ae_eq_Icc.symm]
        simp only [key]
    _ = ENNReal.ofReal (∫ y in x..b, f y) := by
        rw [intervalIntegral.integral_of_le hxb, ofReal_integral_eq_lintegral_ofReal hint hnn]
    _ ≤ ENNReal.ofReal (C * δ * η * x ^ (2 + ε)) :=
        ENNReal.ofReal_le_ofReal (hC x hx η hη hη1 δ hδ0 hδ1)
    _ ≤ ENNReal.ofReal (C * (2 * w) * η * x ^ (2 + ε)) := by
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ C * η * x ^ (2 + ε) := by positivity
        nlinarith

theorem loc_sig (θ X x : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hX : 32 ≤ X) (hx : X / 16 ≤ x) :
    x ^ (-θ) ≤ min 1 (16 * X ^ (-θ)) := by
  have hX0 : 0 < X := by linarith
  have h1 : x ^ (-θ) ≤ (X / 16) ^ (-θ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith)
  have h2 : (X / 16) ^ (-θ) = X ^ (-θ) * (16 : ℝ) ^ θ := by
    rw [Real.div_rpow hX0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16),
      div_inv_eq_mul]
  have h3 : (16 : ℝ) ^ θ ≤ 16 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) hθ1
    rwa [Real.rpow_one] at this
  have h4 : x ^ (-θ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h5 : 0 ≤ X ^ (-θ) := Real.rpow_nonneg hX0.le _
  refine le_min h4 ?_
  rw [h2] at h1
  nlinarith

theorem loc_K (θ C ε X A η σ : ℝ) (hC0 : 0 ≤ C) (hε : 0 < ε) (hC : LocLS θ C ε) (hX : 32 ≤ X)
    (hA1 : X / 2 ≤ A) (hA2 : A ≤ 2 * X) (hησ : η ≤ σ) (hσ1 : σ ≤ 1)
    (hσx : ∀ x : ℝ, X / 16 ≤ x → x ^ (-θ) ≤ σ) (a : ℝ) (ha1 : 1 / 8 ≤ a) (ha2 : a ≤ 8) (w : ℝ) (hw : 0 < w) (hw2 : w ≤ 2) :
    ∫⁻ y in Set.Icc (a * A) (a * (A * (1 + η))), ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
      ≤ ENNReal.ofReal (8 * C * w * σ * (128 * X) ^ (2 + ε)) := by
  have hX0 : 0 < X := by linarith
  have hσ0 : 0 < σ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < X / 16) _) (hσx _ le_rfl)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 4 := ⟨4, rfl⟩
  have hm' : (m : ℝ) = 4 := by rw [hm]; norm_num
  set w' : ℝ := w / m with hw'def
  have hw'pos : 0 < w' := by rw [hw'def, hm']; positivity
  have hmw' : (m : ℝ) * w' = w := by rw [hw'def, hm']; ring
  have hw'le : w' ≤ 1 / 2 := by rw [hw'def, hm']; linarith
  set g : ℝ → ENNReal := fun y => ENNReal.ofReal ((F (y * Real.exp w') - F y) ^ 2) with hg
  set B : ℝ := C * (2 * w') * σ * (128 * X) ^ (2 + ε) with hB
  have he2 := msq_exp_two_lt_eight
  have hterm : ∀ l ∈ range m, ∫⁻ y in Set.Icc (a * A) (a * (A * (1 + η))),
      ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w')) - F (y * Real.exp ((l : ℝ) * w'))) ^ 2)
        ≤ ENNReal.ofReal B := by
    intro l hl
    have hl' : (l : ℝ) + 1 ≤ m := by
      have := Finset.mem_range.1 hl
      exact_mod_cast this
    set b : ℝ := Real.exp ((l : ℝ) * w') with hb
    have hb0 : 0 < b := Real.exp_pos _
    have hb1 : 1 ≤ b := Real.one_le_exp (by positivity)
    have hb8 : b ≤ 8 := by
      have : (l : ℝ) * w' ≤ 2 := by nlinarith
      exact le_trans (Real.exp_le_exp.2 this) he2.le
    have hfun : ∀ y : ℝ, ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w'))
        - F (y * b)) ^ 2) = g (b * y) := by
      intro y
      have e1 : y * Real.exp (((l : ℝ) + 1) * w') = b * y * Real.exp w' := by
        rw [hb, add_mul, one_mul, Real.exp_add]; ring
      have e2 : y * b = b * y := by ring
      rw [e1, e2]
    simp only [hfun]
    rw [msq_lintegral_Icc_comp_mul g hb0]
    have hxe : b * (a * (A * (1 + η))) = b * (a * A) * (1 + η) := by ring
    rw [hxe]
    set x := b * (a * A) with hxdef
    have hA0 : 0 < A := by linarith
    have hx16 : X / 16 ≤ x := by
      have h1 : a * A ≤ b * (a * A) := le_mul_of_one_le_left (by positivity) hb1
      have h2 : A / 8 ≤ a * A := by nlinarith
      linarith
    have hx128 : x ≤ 128 * X := by
      have h1 : a * A ≤ 8 * A := by nlinarith
      have h2 : b * (a * A) ≤ 8 * (a * A) := by nlinarith
      linarith
    have hx2 : 2 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hmono : ∫⁻ y in Set.Icc x (x * (1 + η)), g y ≤ ∫⁻ y in Set.Icc x (x * (1 + σ)), g y :=
      lintegral_mono_set (Set.Icc_subset_Icc le_rfl (by nlinarith))
    have hbase := loc_base θ C ε hC0 hC x σ hx2 (hσx x hx16) hσ1 w' hw'pos hw'le
    calc ENNReal.ofReal b⁻¹ * ∫⁻ y in Set.Icc x (x * (1 + η)), g y
        ≤ 1 * ENNReal.ofReal (C * (2 * w') * σ * x ^ (2 + ε)) := by
          refine mul_le_mul' ?_ (hmono.trans hbase)
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ hb1)
      _ ≤ ENNReal.ofReal B := by
          rw [one_mul]
          apply ENNReal.ofReal_le_ofReal
          rw [hB]
          have h1 : x ^ (2 + ε) ≤ (128 * X) ^ (2 + ε) :=
            Real.rpow_le_rpow hx0.le hx128 (by linarith)
          have h3 : 0 ≤ C * (2 * w') * σ := by positivity
          exact mul_le_mul_of_nonneg_left h1 h3
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
  calc ∫⁻ y in Set.Icc (a * A) (a * (A * (1 + η))), ENNReal.ofReal ((F (y * Real.exp w) - F y) ^ 2)
      ≤ ∫⁻ y in Set.Icc (a * A) (a * (A * (1 + η))), ∑ l ∈ range m, ENNReal.ofReal (m : ℝ) *
          ENNReal.ofReal ((F (y * Real.exp (((l : ℝ) + 1) * w'))
            - F (y * Real.exp ((l : ℝ) * w'))) ^ 2) := lintegral_mono hpt
    _ = ∑ l ∈ range m, ENNReal.ofReal (m : ℝ) * ∫⁻ y in Set.Icc (a * A) (a * (A * (1 + η))),
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
    _ = ENNReal.ofReal (8 * C * w * σ * (128 * X) ^ (2 + ε)) := by
        congr 1
        rw [hB, ← hmw', hm']
        ring

theorem loc_gen (K : ℕ) (A B D : ℝ) (hAB : A ≤ B) (hD : 0 ≤ D)
    (Df : ℕ → ℕ → ℝ → ℝ) (hDf : ∀ j l, Measurable (Df j l)) (c : ℝ → ℝ)
    (hc0 : ∀ y ∈ Set.Icc A B, 0 ≤ c y ∧ c y ≤ 32)
    (hint : ∀ j ∈ range K, ∀ l ∈ range (2 ^ j),
      ∫⁻ y in Set.Icc A B, ENNReal.ofReal ((Df j l y) ^ 2) ≤ ENNReal.ofReal (D / 2 ^ j)) :
    ∫⁻ y in Set.Icc A B, ENNReal.ofReal ((2 * ∑ j ∈ range K,
        Real.sqrt (∑ l ∈ range (2 ^ j), (Df j l y) ^ 2) + c y) ^ 2)
      ≤ ENNReal.ofReal (8 * K ^ 2 * D + 2048 * (B - A)) := by
  have hpt : ∀ y ∈ Set.Icc A B, ENNReal.ofReal ((2 * ∑ j ∈ range K,
        Real.sqrt (∑ l ∈ range (2 ^ j), (Df j l y) ^ 2) + c y) ^ 2)
      ≤ ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          ENNReal.ofReal ((Df j l y) ^ 2) + ENNReal.ofReal 2048 := by
    intro y hy
    obtain ⟨hc1, hc2⟩ := hc0 y hy
    have hT : ∀ j, 0 ≤ ∑ l ∈ range (2 ^ j), (Df j l y) ^ 2 :=
      fun j => Finset.sum_nonneg (fun l _ => sq_nonneg _)
    have hsq : ∀ j, Real.sqrt (∑ l ∈ range (2 ^ j), (Df j l y) ^ 2) ^ 2
        = ∑ l ∈ range (2 ^ j), (Df j l y) ^ 2 := fun j => Real.sq_sqrt (hT j)
    have hCS := sq_sum_le_card_mul_sum_sq (s := range K)
      (f := fun j => Real.sqrt (∑ l ∈ range (2 ^ j), (Df j l y) ^ 2))
    simp only [card_range, hsq] at hCS
    have hS0 : 0 ≤ ∑ j ∈ range K, Real.sqrt (∑ l ∈ range (2 ^ j), (Df j l y) ^ 2) :=
      Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
    have hT0 : 0 ≤ ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), (Df j l y) ^ 2 :=
      Finset.sum_nonneg (fun j _ => hT j)
    have e : ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          ENNReal.ofReal ((Df j l y) ^ 2) + ENNReal.ofReal 2048
        = ENNReal.ofReal (8 * K * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), (Df j l y) ^ 2 + 2048) := by
      rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hT0) (by norm_num),
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * (K : ℝ) by positivity),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => hT j)]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _)]
    rw [e]
    apply ENNReal.ofReal_le_ofReal
    set S := ∑ j ∈ range K, Real.sqrt (∑ l ∈ range (2 ^ j), (Df j l y) ^ 2)
    set T := ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), (Df j l y) ^ 2
    nlinarith [sq_nonneg (2 * S - c y)]
  have hmeas : ∀ j l, Measurable (fun y => ENNReal.ofReal ((Df j l y) ^ 2)) := by
    intro j l
    have := hDf j l
    fun_prop
  calc ∫⁻ y in Set.Icc A B, ENNReal.ofReal ((2 * ∑ j ∈ range K,
        Real.sqrt (∑ l ∈ range (2 ^ j), (Df j l y) ^ 2) + c y) ^ 2)
      ≤ ∫⁻ y in Set.Icc A B, (ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          ENNReal.ofReal ((Df j l y) ^ 2) + ENNReal.ofReal 2048) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j),
          (∫⁻ y in Set.Icc A B, ENNReal.ofReal ((Df j l y) ^ 2))
          + ENNReal.ofReal 2048 * volume (Set.Icc A B) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const]
        congr 2
        rw [lintegral_finsetSum _ (fun j _ => Finset.measurable_sum _ (fun l _ => hmeas j l))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_finsetSum _ (fun l _ => hmeas j l)]
    _ ≤ ENNReal.ofReal (8 * K) * ∑ j ∈ range K, ∑ l ∈ range (2 ^ j), ENNReal.ofReal (D / 2 ^ j)
          + ENNReal.ofReal 2048 * ENNReal.ofReal (B - A) := by
        rw [Real.volume_Icc]
        gcongr with j hj l hl
        exact hint j hj l hl
    _ = ENNReal.ofReal (8 * K ^ 2 * D + 2048 * (B - A)) := by
        have e1 : ∀ j : ℕ, ∑ l ∈ range (2 ^ j), ENNReal.ofReal (D / 2 ^ j) = ENNReal.ofReal D := by
          intro j
          rw [← ENNReal.ofReal_sum_of_nonneg (fun l _ => by positivity), Finset.sum_const,
            card_range, nsmul_eq_mul]
          congr 1
          push_cast
          field_simp
        have hBA : 0 ≤ B - A := by linarith
        simp only [e1, Finset.sum_const, card_range, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem loc_fin (Z D r : ℝ) (k : ℕ) (hD : 0 ≤ D) (hr : 0 ≤ r) (hk : (k : ℝ) + 1 ≤ 6 * Real.log Z) :
    8 * (((k + 1 : ℕ) : ℝ)) ^ 2 * (D * r) ≤ 288 * (Real.log Z) ^ 2 * D * r := by
  push_cast
  have h0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hk2 : ((k : ℝ) + 1) ^ 2 ≤ 36 * (Real.log Z) ^ 2 := by nlinarith
  have : 0 ≤ D * r := mul_nonneg hD hr
  nlinarith

theorem loc_ms_Bp (θ C ε X A η σ Z r : ℝ) (hC0 : 0 ≤ C) (hε : 0 < ε) (hC : LocLS θ C ε)
    (hX : 32 ≤ X) (hA1 : X / 2 ≤ A) (hA2 : A ≤ 2 * X) (hη0 : 0 ≤ η) (hησ : η ≤ σ) (hσ1 : σ ≤ 1)
    (hσx : ∀ x : ℝ, X / 16 ≤ x → x ^ (-θ) ≤ σ) (hZ3 : 3 ≤ Z) (hAZ : A * (1 + η) ≤ 2 * Z) (hr : 0 < r) (hr2 : r ≤ 2) :
    ∫⁻ y in Set.Icc A (A * (1 + η)), ENNReal.ofReal ((Bp r (kOf Z r) y) ^ 2)
      ≤ ENNReal.ofReal (288 * (Real.log Z) ^ 2 * (8 * C * σ * (128 * X) ^ (2 + ε)) * r
          + 2048 * (A * η)) := by
  obtain ⟨hk1, hk2⟩ := msq_kOf_facts Z r hZ3 hr hr2
  have hX0 : 0 < X := by linarith
  have hσ0 : 0 ≤ σ := hη0.trans hησ
  have hA0 : 0 < A := by linarith
  have hY : 0 ≤ (128 * X) ^ (2 + ε) := Real.rpow_nonneg (by linarith) _
  set D : ℝ := 8 * C * σ * (128 * X) ^ (2 + ε) with hDdef
  have hD0 : 0 ≤ D := by positivity
  have he2 := msq_exp_two_lt_eight
  have hint : ∀ j ∈ range (kOf Z r + 1), ∀ l ∈ range (2 ^ j),
      ∫⁻ y in Set.Icc A (A * (1 + η)), ENNReal.ofReal ((Dp r j l y) ^ 2)
        ≤ ENNReal.ofReal (D * r / 2 ^ j) := by
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
    rw [msq_lintegral_Icc_comp_mul (fun y' => ENNReal.ofReal ((F (y' * Real.exp (r / 2 ^ j)) - F y') ^ 2)) ha0]
    calc ENNReal.ofReal (Real.exp ((l : ℝ) * r / 2 ^ j))⁻¹ *
          ∫⁻ y in Set.Icc (Real.exp ((l : ℝ) * r / 2 ^ j) * A)
            (Real.exp ((l : ℝ) * r / 2 ^ j) * (A * (1 + η))),
          ENNReal.ofReal ((F (y * Real.exp (r / 2 ^ j)) - F y) ^ 2)
        ≤ 1 * ENNReal.ofReal (8 * C * (r / 2 ^ j) * σ * (128 * X) ^ (2 + ε)) := by
          refine mul_le_mul' ?_ (loc_K θ C ε X A η σ hC0 hε hC hX hA1 hA2 hησ hσ1 hσx _
            (by linarith) ha8 _ hw hw2)
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ ha1)
      _ = ENNReal.ofReal (D * r / 2 ^ j) := by
          rw [one_mul, hDdef]; congr 1; ring
  have hc : ∀ y ∈ Set.Icc A (A * (1 + η)), 0 ≤ y * Real.exp r * (Real.exp (r / 2 ^ kOf Z r) - 1)
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
    have hy2 : y ≤ 2 * Z := le_trans hy.2 hAZ
    have hpos : 0 ≤ Real.exp (r / 2 ^ kOf Z r) - 1 := by linarith
    constructor
    · positivity
    · calc y * Real.exp r * (Real.exp (r / 2 ^ kOf Z r) - 1)
          ≤ (2 * Z) * 8 * (2 * (r / 2 ^ kOf Z r)) := by
            apply mul_le_mul (mul_le_mul hy2 her her0.le (by linarith)) hb hpos (by positivity)
        _ = 32 * (Z * (r / 2 ^ kOf Z r)) := by ring
        _ ≤ 32 := by linarith
  have hAB : A ≤ A * (1 + η) := by nlinarith
  have key := loc_gen (kOf Z r + 1) A (A * (1 + η)) (D * r) hAB (by positivity)
    (Dp r) (msq_measurable_Dp r) _ hc hint
  refine le_trans (le_of_eq ?_) (key.trans (ENNReal.ofReal_le_ofReal ?_))
  · rfl
  · have := loc_fin Z D r (kOf Z r) hD0 hr.le hk2
    have e : A * (1 + η) - A = A * η := by ring
    rw [e]
    linarith

theorem loc_ms_Bm (θ C ε X A η σ Z r : ℝ) (hC0 : 0 ≤ C) (hε : 0 < ε) (hC : LocLS θ C ε)
    (hX : 32 ≤ X) (hA1 : X / 2 ≤ A) (hA2 : A ≤ 2 * X) (hη0 : 0 ≤ η) (hησ : η ≤ σ) (hσ1 : σ ≤ 1)
    (hσx : ∀ x : ℝ, X / 16 ≤ x → x ^ (-θ) ≤ σ) (hZ3 : 3 ≤ Z) (hAZ : A * (1 + η) ≤ 2 * Z) (hr : 0 < r) (hr2 : r ≤ 2) :
    ∫⁻ y in Set.Icc A (A * (1 + η)), ENNReal.ofReal ((Bm r (kOf Z r) y) ^ 2)
      ≤ ENNReal.ofReal (288 * (Real.log Z) ^ 2 * (64 * C * σ * (128 * X) ^ (2 + ε)) * r
          + 2048 * (A * η)) := by
  obtain ⟨hk1, hk2⟩ := msq_kOf_facts Z r hZ3 hr hr2
  have hX0 : 0 < X := by linarith
  have hσ0 : 0 ≤ σ := hη0.trans hησ
  have hA0 : 0 < A := by linarith
  have hY : 0 ≤ (128 * X) ^ (2 + ε) := Real.rpow_nonneg (by linarith) _
  set D : ℝ := 64 * C * σ * (128 * X) ^ (2 + ε) with hDdef
  have hD0 : 0 ≤ D := by positivity
  have he2 := msq_exp_two_lt_eight
  have hint : ∀ j ∈ range (kOf Z r + 1), ∀ l ∈ range (2 ^ j),
      ∫⁻ y in Set.Icc A (A * (1 + η)), ENNReal.ofReal ((Dm r j l y) ^ 2)
        ≤ ENNReal.ofReal (D * r / 2 ^ j) := by
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
    have h18 : 1 / 8 ≤ Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) := by
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
    rw [msq_lintegral_Icc_comp_mul (fun y' => ENNReal.ofReal ((F (y' * Real.exp (r / 2 ^ j)) - F y') ^ 2)) ha0]
    calc ENNReal.ofReal (Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)))⁻¹ *
          ∫⁻ y in Set.Icc (Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) * A)
            (Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)) * (A * (1 + η))),
          ENNReal.ofReal ((F (y * Real.exp (r / 2 ^ j)) - F y) ^ 2)
        ≤ ENNReal.ofReal 8 * ENNReal.ofReal (8 * C * (r / 2 ^ j) * σ * (128 * X) ^ (2 + ε)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal ha8) (loc_K θ C ε X A η σ hC0 hε hC hX hA1 hA2
            hησ hσ1 hσx _ h18 (by linarith) _ hw hw2)
      _ = ENNReal.ofReal (D * r / 2 ^ j) := by
          rw [← ENNReal.ofReal_mul (by norm_num), hDdef]; congr 1; ring
  have hc : ∀ y ∈ Set.Icc A (A * (1 + η)), 0 ≤ y * (Real.exp (r / 2 ^ kOf Z r) - 1)
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
    have hy2 : y ≤ 2 * Z := le_trans hy.2 hAZ
    have hpos : 0 ≤ Real.exp (r / 2 ^ kOf Z r) - 1 := by linarith
    constructor
    · positivity
    · calc y * (Real.exp (r / 2 ^ kOf Z r) - 1)
          ≤ (2 * Z) * (2 * (r / 2 ^ kOf Z r)) :=
            mul_le_mul hy2 hb hpos (by positivity)
        _ = 4 * (Z * (r / 2 ^ kOf Z r)) := by ring
        _ ≤ 32 := by linarith
  have hAB : A ≤ A * (1 + η) := by nlinarith
  have key := loc_gen (kOf Z r + 1) A (A * (1 + η)) (D * r) hAB (by positivity)
    (Dm r) (msq_measurable_Dm r) _ hc hint
  refine le_trans (le_of_eq ?_) (key.trans (ENNReal.ofReal_le_ofReal ?_))
  · rfl
  · have := loc_fin Z D r (kOf Z r) hD0 hr.le hk2
    have e : A * (1 + η) - A = A * η := by ring
    rw [e]
    linarith

theorem loc_mp (M Z A B r : ℝ) (k : ℕ) (hZ : 3 ≤ Z) (hZA : Z ≤ A)
    (hms : ∫⁻ y in Set.Icc A B, ENNReal.ofReal ((Bp r k y) ^ 2) ≤ ENNReal.ofReal M) :
    ∫⁻ u in Set.Icc A B, ENNReal.ofReal ((Bp r k u / Real.log u) ^ 2)
      ≤ ENNReal.ofReal (M / (Real.log Z) ^ 2) := by
  have hZpos : 0 < Z := by linarith
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  set c : ℝ := 1 / (Real.log Z) ^ 2 with hc
  have hpt : ∀ u ∈ Set.Icc A B,
      ENNReal.ofReal ((Bp r k u / Real.log u) ^ 2) ≤ ENNReal.ofReal c * ENNReal.ofReal ((Bp r k u) ^ 2) := by
    intro u hu
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hl : Real.log Z ≤ Real.log u := Real.log_le_log hZpos (le_trans hZA hu.1)
    rw [div_pow, hc, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hlogZ.le hl 2)
  calc ∫⁻ u in Set.Icc A B, ENNReal.ofReal ((Bp r k u / Real.log u) ^ 2)
      ≤ ∫⁻ u in Set.Icc A B, ENNReal.ofReal c * ENNReal.ofReal ((Bp r k u) ^ 2) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal c * ∫⁻ u in Set.Icc A B, ENNReal.ofReal ((Bp r k u) ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (M / (Real.log Z) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by rw [hc]; positivity)]
        congr 1
        rw [hc]
        field_simp

theorem loc_mm (M x U Z r a b A' B' : ℝ) (k : ℕ) (hU : 0 < U) (hx : x = 2 * U * Z)
    (hZ : 60 ≤ Z) (hr2 : r ≤ 2) (ha : 0 < a)
    (hA' : A' ≤ x / b) (hB' : x / a ≤ B') (hZA' : Z ≤ A')
    (hms : ∫⁻ y in Set.Icc A' B', ENNReal.ofReal ((Bm r k y) ^ 2) ≤ ENNReal.ofReal M) :
    ∫⁻ u in Set.Icc a b,
        ENNReal.ofReal ((2 * Bm r k (x / u) / Real.log (x / u * Real.exp (-r))) ^ 2)
      ≤ ENNReal.ofReal (32 * U / (Z * (Real.log Z) ^ 2) * M) := by
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
  have hsub : Set.Icc a b ⊆ f '' Set.Icc A' B' := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    refine ⟨x / u, ⟨?_, ?_⟩, ?_⟩
    · exact le_trans hA' (div_le_div_of_nonneg_left hxpos.le hu0 hu.2)
    · exact le_trans (div_le_div_of_nonneg_left hxpos.le ha hu.1) hB'
    · simp only [hf]; field_simp
  have hderiv : ∀ y ∈ Set.Icc A' B', HasDerivWithinAt f (x * -(y ^ 2)⁻¹) (Set.Icc A' B') y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    exact ((hasDerivAt_inv hy0).const_mul x).hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Icc A' B') := by
    intro a ha b hb hab
    simp only [hf] at hab
    have := mul_left_cancel₀ hxpos.ne' hab
    exact inv_injective this
  set c : ℝ := 16 * x / (Z ^ 2 * (Real.log Z) ^ 2) with hc
  have hpt : ∀ y ∈ Set.Icc A' B',
      ENNReal.ofReal (|x * -(y ^ 2)⁻¹|) * g (f y) ≤ ENNReal.ofReal c * ENNReal.ofReal ((Bm r k y) ^ 2) := by
    intro y hy
    have hy1 : Z ≤ y := le_trans hZA' hy.1
    have hy0 : 0 < y := by linarith
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
      have := Real.log_le_log hZpos hy1
      linarith
    have hlogpos : 0 < Real.log Z / 2 := by linarith
    have h1 : x / y ^ 2 ≤ x / Z ^ 2 := by
      apply div_le_div_of_nonneg_left hxpos.le (by positivity)
      exact pow_le_pow_left₀ hZpos.le hy1 2
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
  calc ∫⁻ u in Set.Icc a b, g u
      ≤ ∫⁻ u in f '' Set.Icc A' B', g u := lintegral_mono_set hsub
    _ = ∫⁻ y in Set.Icc A' B', ENNReal.ofReal (|x * -(y ^ 2)⁻¹|) * g (f y) :=
        lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv hinj g
    _ ≤ ∫⁻ y in Set.Icc A' B', ENNReal.ofReal c * ENNReal.ofReal ((Bm r k y) ^ 2) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal c * ∫⁻ y in Set.Icc A' B', ENNReal.ofReal ((Bm r k y) ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (32 * U / (Z * (Real.log Z) ^ 2) * M) := by
        rw [← ENNReal.ofReal_mul (by rw [hc]; positivity)]
        congr 1
        rw [hc, hx]
        field_simp
        ring

theorem loc_eta (τ : ℝ) (hτ0 : 0 < τ) : 0 < τ / (1 + τ) ∧ τ / (1 + τ) ≤ τ :=
  ⟨by positivity, div_le_self hτ0.le (by linarith)⟩

theorem loc_Pi (θ C ε X τ σ r : ℝ) (hC1 : 1 ≤ C) (hε : 0 < ε) (hC : LocLS θ C ε)
    (hX : 4096 ≤ X) (hτ0 : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1)
    (hσx : ∀ x : ℝ, X / 16 ≤ x → x ^ (-θ) ≤ σ) (hr : 0 < r) (hr2 : r ≤ 2) :
    ∫⁻ u in Set.Icc (X * (1 + τ)) (X * (1 + 2 * τ)),
      ENNReal.ofReal ((Bp r (kOf X r) u / Real.log u) ^ 2)
        ≤ ENNReal.ofReal (2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * r + 2 ^ 18 * X * τ) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨hη0, hητ⟩ := loc_eta τ hτ0
  set η := τ / (1 + τ) with hηdef
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hY0 : 0 ≤ (128 * X) ^ (2 + ε) := Real.rpow_nonneg (by linarith) _
  have hab_eq : X * (1 + τ) * (1 + η) = X * (1 + 2 * τ) := by rw [hηdef]; field_simp; ring
  have h1 := loc_ms_Bp θ C ε X (X * (1 + τ)) η σ X r (by linarith) hε hC (by linarith)
    (by nlinarith) (by nlinarith) hη0.le (hητ.trans hτσ) hσ1 hσx (by linarith)
    (by rw [hab_eq]; nlinarith) hr hr2
  rw [hab_eq] at h1
  have h2 := loc_mp _ X (X * (1 + τ)) (X * (1 + 2 * τ)) r (kOf X r) (by linarith) (by nlinarith) h1
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hl2 : 1 ≤ (Real.log X) ^ 2 := one_le_pow₀ hlogX
  have haη : X * (1 + τ) * η = X * τ := by rw [hηdef]; field_simp
  have e : (288 * (Real.log X) ^ 2 * (8 * C * σ * (128 * X) ^ (2 + ε)) * r
      + 2048 * (X * (1 + τ) * η)) / (Real.log X) ^ 2
      = 2304 * C * σ * (128 * X) ^ (2 + ε) * r + 2048 * (X * τ) / (Real.log X) ^ 2 := by
    rw [haη]; field_simp; ring
  rw [e]
  have h3 : 2048 * (X * τ) / (Real.log X) ^ 2 ≤ 2048 * (X * τ) :=
    div_le_self (by positivity) hl2
  have h4 : 0 ≤ C * σ * (128 * X) ^ (2 + ε) * r := by
    have : 0 ≤ C := by linarith
    have : 0 ≤ σ := by linarith
    positivity
  nlinarith

theorem loc_Mi (θ C ε τ σ r : ℝ) (n : ℕ) (hC1 : 1 ≤ C) (hε : 0 < ε) (hC : LocLS θ C ε)
    (hX : 4096 ≤ Real.sqrt n) (hτ0 : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1)
    (hσx : ∀ x : ℝ, Real.sqrt n / 16 ≤ x → x ^ (-θ) ≤ σ) (hr : 0 < r) (hr2 : r ≤ 2) :
    ∫⁻ u in Set.Icc (Real.sqrt n * (1 + τ)) (Real.sqrt n * (1 + 2 * τ)),
      ENNReal.ofReal ((2 * Bm r (kOf (Real.sqrt n / 2) r) (n / u) /
        Real.log (n / u * Real.exp (-r))) ^ 2)
        ≤ ENNReal.ofReal (2 ^ 21 * C * σ * (128 * Real.sqrt n) ^ (2 + ε) * r
          + 2 ^ 18 * Real.sqrt n * τ) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hXX : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  set X := Real.sqrt n with hXdef
  have hX0 : 0 < X := by linarith
  obtain ⟨hη0, hητ⟩ := loc_eta τ hτ0
  set η := τ / (1 + τ) with hηdef
  have hlogZ : 1 ≤ Real.log (X / 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hY0 : 0 ≤ (128 * X) ^ (2 + ε) := Real.rpow_nonneg (by linarith) _
  set A' := X / (1 + 2 * τ) with hA'def
  have hA'eq : A' * (1 + η) = X / (1 + τ) := by rw [hA'def, hηdef]; field_simp; ring
  have hnb : (n : ℝ) / (X * (1 + 2 * τ)) = A' := by rw [← hXX, hA'def]; field_simp
  have hna : (n : ℝ) / (X * (1 + τ)) = X / (1 + τ) := by rw [← hXX]; field_simp
  have hnXZ : (n : ℝ) = 2 * X * (X / 2) := by rw [← hXX]; ring
  have hA'X2 : X / 2 ≤ A' := by rw [hA'def, le_div_iff₀ (by linarith)]; nlinarith
  have hA'X : A' ≤ X := by rw [hA'def, div_le_iff₀ (by linarith)]; nlinarith
  have h1 := loc_ms_Bm θ C ε X A' η σ (X / 2) r (by linarith) hε hC (by linarith)
    (by linarith) (by linarith) hη0.le (hητ.trans hτσ) hσ1 hσx (by linarith)
    (by rw [hA'eq, div_le_iff₀ (by linarith)]; nlinarith) hr hr2
  rw [hA'eq] at h1
  have h2 := loc_mm _ n X (X / 2) r (X * (1 + τ)) (X * (1 + 2 * τ)) A' (X / (1 + τ))
    (kOf (X / 2) r) hX0 hnXZ (by linarith) hr2 (by positivity) hnb.ge hna.le hA'X2 h1
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  set l := Real.log (X / 2) with hl
  have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hlogZ
  have hA'η : A' * η ≤ X * τ := mul_le_mul hA'X hητ hη0.le hX0.le
  have e : 32 * X / (X / 2 * l ^ 2) * (288 * l ^ 2 * (64 * C * σ * (128 * X) ^ (2 + ε)) * r
      + 2048 * (A' * η))
      = 1179648 * C * σ * (128 * X) ^ (2 + ε) * r + 131072 * (A' * η) / l ^ 2 := by
    field_simp; ring
  rw [e]
  have h3 : 131072 * (A' * η) / l ^ 2 ≤ 131072 * (A' * η) :=
    div_le_self (by positivity) hl2
  have h4 : 0 ≤ C * σ * (128 * X) ^ (2 + ε) * r := by
    have : 0 ≤ C := by linarith
    have : 0 ≤ σ := by linarith
    positivity
  nlinarith

theorem loc_rr (i : ℕ) : 0 < rr i ∧ rr i ≤ 2 := by
  have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  refine ⟨by unfold rr; positivity, ?_⟩
  unfold rr
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem loc_band_real (C ε X τ σ L : ℝ) (N : ℕ) (hC1 : 1 ≤ C) (hε : 0 < ε) (hX : 4096 ≤ X)
    (hτ0 : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hτσ : τ ≤ σ) (hL1 : 1 ≤ L) (hNL : (N : ℝ) + 1 ≤ 8 * L)
    (hN8 : (2 : ℝ) ^ N < 8 * X) :
    2 / X * (X * (1 + 2 * τ) - X * (1 + τ)) + ∑ i ∈ range (N + 1),
      (L / (rr i * τ * X ^ 2) * (2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * rr i + 2 ^ 18 * X * τ)
        + L / (rr i * τ * X ^ 2) * (2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * rr i + 2 ^ 18 * X * τ))
      ≤ 2 ^ 26 * C * 128 ^ (2 + ε) * X ^ ε * L ^ 2 * (σ / τ) := by
  have hX0 : 0 < X := by linarith
  have hσ0 : 0 < σ := by linarith
  have hρ1 : 1 ≤ σ / τ := by rw [le_div_iff₀ hτ0]; linarith
  have hY : (128 * X) ^ (2 + ε) = 128 ^ (2 + ε) * X ^ 2 * X ^ ε := by
    rw [Real.mul_rpow (by norm_num) hX0.le, Real.rpow_add hX0, Real.rpow_two]
    ring
  have hc1 : 1 ≤ (128 : ℝ) ^ (2 + ε) := Real.one_le_rpow (by norm_num) (by linarith)
  have hXe : 1 ≤ X ^ ε := Real.one_le_rpow (by linarith) hε.le
  set P := C * 128 ^ (2 + ε) * X ^ ε with hPdef
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC1 hc1) hXe
  have hterm : ∀ i ∈ range (N + 1),
      L / (rr i * τ * X ^ 2) * (2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * rr i + 2 ^ 18 * X * τ)
        + L / (rr i * τ * X ^ 2) * (2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * rr i + 2 ^ 18 * X * τ)
        ≤ 2 ^ 22 * P * L * (σ / τ) + 2 ^ 21 * L := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hr0 := (loc_rr i).1
    have h2i : (2 : ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hiN
    have h4 : 1 ≤ 4 * (rr i * X) := by
      unfold rr
      rw [show 4 * (2 / 2 ^ i * X) = 8 * X / 2 ^ i by ring, le_div_iff₀ (by positivity)]
      linarith
    have h5 : 1 / (rr i * X) ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have e : L / (rr i * τ * X ^ 2) * (2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * rr i + 2 ^ 18 * X * τ)
        + L / (rr i * τ * X ^ 2) * (2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * rr i + 2 ^ 18 * X * τ)
        = 2 ^ 22 * P * L * (σ / τ) + 2 ^ 19 * L * (1 / (rr i * X)) := by
      rw [hPdef, hY]
      field_simp
      ring
    rw [e]
    have : 2 ^ 19 * L * (1 / (rr i * X)) ≤ 2 ^ 19 * L * 4 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hK : 0 ≤ 2 ^ 22 * P * L * (σ / τ) + 2 ^ 21 * L := by positivity
  have h1 : ((N + 1 : ℕ) : ℝ) * (2 ^ 22 * P * L * (σ / τ) + 2 ^ 21 * L) ≤
      8 * L * (2 ^ 22 * P * L * (σ / τ) + 2 ^ 21 * L) := by
    apply mul_le_mul_of_nonneg_right _ hK
    push_cast
    exact hNL
  have h3 : 2 / X * (X * (1 + 2 * τ) - X * (1 + τ)) = 2 * τ := by field_simp; ring
  have h6 : 2 ^ 26 * C * 128 ^ (2 + ε) * X ^ ε * L ^ 2 * (σ / τ)
      = 2 ^ 26 * (P * (σ / τ)) * L ^ 2 := by
    rw [hPdef]; ring
  rw [h6, h3]
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hPρ : 1 ≤ P * (σ / τ) := one_le_mul_of_one_le_of_one_le hP1 hρ1
  have h7 : L ^ 2 ≤ P * (σ / τ) * L ^ 2 := le_mul_of_one_le_left (by positivity) hPρ
  have e8 : 8 * L * (2 ^ 22 * P * L * (σ / τ) + 2 ^ 21 * L)
      = 2 ^ 25 * (P * (σ / τ)) * L ^ 2 + 2 ^ 24 * L ^ 2 := by ring
  have e9 : 2 ^ 26 * (P * (σ / τ)) * L ^ 2
      = 2 ^ 25 * (P * (σ / τ)) * L ^ 2 + 2 ^ 25 * (P * (σ / τ) * L ^ 2) := by ring
  nlinarith

theorem loc_band (θ C ε : ℝ) (hC1 : 1 ≤ C) (hε : 0 < ε) (hC : LocLS θ C ε) (n : ℕ)
    (hX : 4096 ≤ Real.sqrt n) (τ σ : ℝ) (hτ0 : 0 < τ) (hτ2 : τ ≤ 1 / 2) (hτσ : τ ≤ σ)
    (hσ1 : σ ≤ 1) (hσx : ∀ x : ℝ, Real.sqrt n / 16 ≤ x → x ^ (-θ) ≤ σ) :
    ∫⁻ u in Set.Icc (Real.sqrt n * (1 + τ)) (Real.sqrt n * (1 + 2 * τ)),
        ENNReal.ofReal ((W n u : ℝ) / u)
      ≤ ENNReal.ofReal (2 ^ 26 * C * 128 ^ (2 + ε) * Real.sqrt n ^ ε * (Real.log n) ^ 2
          * (σ / τ)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hXX : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hPi := fun i => loc_Pi θ C ε (Real.sqrt n) τ σ (rr i) hC1 hε hC hX hτ0 hτ2 hτσ hσ1 hσx
    (loc_rr i).1 (loc_rr i).2
  have hMi := fun i => loc_Mi θ C ε τ σ (rr i) n hC1 hε hC hX hτ0 hτ2 hτσ hσ1 hσx
    (loc_rr i).1 (loc_rr i).2
  set X := Real.sqrt n with hXdef
  set L := Real.log n with hLdef
  have hX0 : 0 < X := by linarith
  have hnpos : (0 : ℝ) < n := by nlinarith
  have hXn : X ≤ n := by nlinarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    nlinarith
  have hnXZ : (n : ℝ) = 2 * X * (X / 2) := by rw [← hXX]; ring
  obtain ⟨N, hN4, hN8⟩ := block_N X (by linarith)
  have hNL := block_Nbound N n X hX0 hXn hN8 hL1
  set a := X * (1 + τ) with hadef
  set b := X * (1 + 2 * τ) with hbdef
  set S : ℕ → ℝ := fun i => 2 ^ 21 * C * σ * (128 * X) ^ (2 + ε) * rr i + 2 ^ 18 * X * τ
    with hSdef
  have hpt : ∀ u ∈ Set.Icc a b, ENNReal.ofReal ((W n u : ℝ) / u) ≤
      ENNReal.ofReal (2 / X + ∑ i ∈ range (N + 1), L / (rr i * τ * X ^ 2) *
        ((Bp (rr i) (kOf X (rr i)) u / Real.log u) ^ 2 +
          (2 * Bm (rr i) (kOf (X / 2) (rr i)) (n / u) /
            Real.log (n / u * Real.exp (-rr i))) ^ 2)) := by
    intro u hu
    apply ENNReal.ofReal_le_ofReal
    have hu1 : a ≤ u := hu.1
    have hu2 : u ≤ b := hu.2
    exact block_pt n X (X / 2) u τ N hnXZ (by linarith) (by linarith) (by nlinarith)
      (by nlinarith) (by nlinarith) hτ0 (by nlinarith) (by nlinarith)
  have hc0 : ∀ i, 0 ≤ L / (rr i * τ * X ^ 2) := by
    intro i
    have := (loc_rr i).1
    positivity
  have heq : ∀ u : ℝ, ENNReal.ofReal (2 / X + ∑ i ∈ range (N + 1), L / (rr i * τ * X ^ 2) *
        ((Bp (rr i) (kOf X (rr i)) u / Real.log u) ^ 2 +
          (2 * Bm (rr i) (kOf (X / 2) (rr i)) (n / u) /
            Real.log (n / u * Real.exp (-rr i))) ^ 2)) =
      ENNReal.ofReal (2 / X) + ∑ i ∈ range (N + 1),
        (ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
            ENNReal.ofReal ((Bp (rr i) (kOf X (rr i)) u / Real.log u) ^ 2) +
          ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
            ENNReal.ofReal ((2 * Bm (rr i) (kOf (X / 2) (rr i)) (n / u) /
              Real.log (n / u * Real.exp (-rr i))) ^ 2)) := by
    intro u
    rw [ENNReal.ofReal_add (by positivity)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hc0 i) (by positivity))),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hc0 i) (by positivity))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_mul (hc0 i), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), mul_add]
  have hmP : ∀ i, Measurable (fun u : ℝ => ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
      ENNReal.ofReal ((Bp (rr i) (kOf X (rr i)) u / Real.log u) ^ 2)) := by
    intro i
    exact measurable_const.mul
      ((((measurable_Bp _ _).div Real.measurable_log).pow_const 2).ennreal_ofReal)
  have hmM : ∀ i, Measurable (fun u : ℝ => ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
      ENNReal.ofReal ((2 * Bm (rr i) (kOf (X / 2) (rr i)) (n / u) /
        Real.log (n / u * Real.exp (-rr i))) ^ 2)) := by
    intro i
    have h1 := measurable_Bm (rr i) (kOf (X / 2) (rr i))
    fun_prop
  have hS0 : ∀ i, 0 ≤ S i := by
    intro i
    have := (loc_rr i).1
    have : 0 ≤ (128 * X) ^ (2 + ε) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ C := by linarith
    have : 0 ≤ σ := by linarith
    simp only [hSdef]
    positivity
  have hreal := loc_band_real C ε X τ σ L N hC1 hε hX hτ0 hτ2 hτσ hL1 hNL hN8
  calc (∫⁻ u in Set.Icc a b, ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ∫⁻ u in Set.Icc a b, ENNReal.ofReal (2 / X + ∑ i ∈ range (N + 1),
          L / (rr i * τ * X ^ 2) *
          ((Bp (rr i) (kOf X (rr i)) u / Real.log u) ^ 2 +
            (2 * Bm (rr i) (kOf (X / 2) (rr i)) (n / u) /
              Real.log (n / u * Real.exp (-rr i))) ^ 2)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (2 / X) * ENNReal.ofReal (b - a) + ∑ i ∈ range (N + 1),
        (ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
            (∫⁻ u in Set.Icc a b, ENNReal.ofReal ((Bp (rr i) (kOf X (rr i)) u / Real.log u) ^ 2)) +
          ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
            (∫⁻ u in Set.Icc a b, ENNReal.ofReal ((2 * Bm (rr i) (kOf (X / 2) (rr i)) (n / u) /
              Real.log (n / u * Real.exp (-rr i))) ^ 2))) := by
        have hmPM : ∀ i, Measurable (fun u : ℝ =>
            ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
              ENNReal.ofReal ((Bp (rr i) (kOf X (rr i)) u / Real.log u) ^ 2) +
            ENNReal.ofReal (L / (rr i * τ * X ^ 2)) *
              ENNReal.ofReal ((2 * Bm (rr i) (kOf (X / 2) (rr i)) (n / u) /
                Real.log (n / u * Real.exp (-rr i))) ^ 2)) := fun i => (hmP i).add (hmM i)
        simp_rw [heq]
        rw [lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Icc,
          lintegral_finsetSum _ (fun i _ => hmPM i)]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_add_left (hmP i), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 / X) * ENNReal.ofReal (b - a) + ∑ i ∈ range (N + 1),
        (ENNReal.ofReal (L / (rr i * τ * X ^ 2)) * ENNReal.ofReal (S i) +
          ENNReal.ofReal (L / (rr i * τ * X ^ 2)) * ENNReal.ofReal (S i)) := by
        gcongr with i hi
        · exact hPi i
        · exact hMi i
    _ = ENNReal.ofReal (2 / X * (b - a) + ∑ i ∈ range (N + 1),
      (L / (rr i * τ * X ^ 2) * S i + L / (rr i * τ * X ^ 2) * S i)) := by
        have hba : 0 ≤ b - a := by rw [hadef, hbdef]; nlinarith
        rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hba) (Finset.sum_nonneg (fun i _ =>
            add_nonneg (mul_nonneg (hc0 i) (hS0 i)) (mul_nonneg (hc0 i) (hS0 i)))),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ =>
            add_nonneg (mul_nonneg (hc0 i) (hS0 i)) (mul_nonneg (hc0 i) (hS0 i)))]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.ofReal_add (mul_nonneg (hc0 i) (hS0 i)) (mul_nonneg (hc0 i) (hS0 i)),
          ENNReal.ofReal_mul (hc0 i)]
    _ ≤ ENNReal.ofReal (2 ^ 26 * C * 128 ^ (2 + ε) * X ^ ε * L ^ 2 * (σ / τ)) :=
        ENNReal.ofReal_le_ofReal hreal

theorem loc_band_at (θ C ε : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hC1 : 1 ≤ C) (hε : 0 < ε)
    (hC : LocLS θ C ε) (n : ℕ) (hX : 4096 ≤ Real.sqrt n) (τ : ℝ) (hτ0 : 0 < τ)
    (hτ2 : τ ≤ 1 / 2) :
    ∫⁻ u in Set.Icc (Real.sqrt n * (1 + τ)) (Real.sqrt n * (1 + 2 * τ)),
        ENNReal.ofReal ((W n u : ℝ) / u)
      ≤ ENNReal.ofReal (2 ^ 26 * C * 128 ^ (2 + ε) * Real.sqrt n ^ ε * (Real.log n) ^ 2
          * (1 + 16 * Real.sqrt n ^ (-θ) / τ)) := by
  set X := Real.sqrt n with hXdef
  have hX0 : 0 < X := by linarith
  have hXθ : 0 ≤ X ^ (-θ) := Real.rpow_nonneg hX0.le _
  set c := 16 * X ^ (-θ) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  set σ := max τ (min 1 c) with hσdef
  have hτσ : τ ≤ σ := le_max_left _ _
  have hσ1 : σ ≤ 1 := max_le (by linarith) (min_le_left _ _)
  have hσx : ∀ x : ℝ, X / 16 ≤ x → x ^ (-θ) ≤ σ := fun x hx =>
    (loc_sig θ X x hθ0 hθ1 (by linarith) hx).trans (le_max_right _ _)
  have hσc : σ ≤ τ + c := max_le (by linarith) ((min_le_right _ _).trans (by linarith))
  refine (loc_band θ C ε hC1 hε hC n hX τ σ hτ0 hτ2 hτσ hσ1 hσx).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hB0 : 0 ≤ 2 ^ 26 * C * 128 ^ (2 + ε) * X ^ ε * (Real.log n) ^ 2 := by
    have : 0 ≤ X ^ ε := Real.rpow_nonneg hX0.le _
    have : 0 ≤ (128 : ℝ) ^ (2 + ε) := Real.rpow_nonneg (by norm_num) _
    have : 0 ≤ C := by linarith
    positivity
  apply mul_le_mul_of_nonneg_left _ hB0
  rw [div_le_iff₀ hτ0]
  have : (1 + c / τ) * τ = τ + c := by rw [add_mul, div_mul_cancel₀ c hτ0.ne', one_mul]
  linarith

theorem loc_lint_le (n : ℕ) (s : Set ℝ) (c : ℝ)
    (h : ∀ u ∈ s, (W n u : ℝ) / u ≤ c) :
    (∫⁻ u in s, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal c * volume s := by
  calc (∫⁻ u in s, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ∫⁻ _ in s, ENNReal.ofReal c :=
        setLIntegral_mono measurable_const (fun u hu => ENNReal.ofReal_le_ofReal (h u hu))
    _ = _ := setLIntegral_const _ _

theorem loc_lint_Ico (n : ℕ) (a b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ u ∈ Set.Ico a b, (W n u : ℝ) / u ≤ c) :
    (∫⁻ u in Set.Ico a b, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal (c * (b - a)) := by
  rw [ENNReal.ofReal_mul hc, ← Real.volume_Ico]
  exact loc_lint_le n _ c h

theorem loc_trivial (n : ℕ) (u : ℝ) (hu : 1 ≤ u) : (W n u : ℝ) / u ≤ n + 1 := by
  have h1 : (W n u : ℝ) ≤ (smallPrimes n).card := by exact_mod_cast W_le_card n u
  have h2 : (W n u : ℝ) / u ≤ W n u := div_le_self (by positivity) hu
  have h3 : ((smallPrimes n).card : ℝ) ≤ n + 1 := by
    have : (smallPrimes n).card ≤ n + 1 := by
      unfold smallPrimes
      exact (card_filter_le _ _).trans (card_range _).le
    exact_mod_cast this
  linarith

theorem loc_near (n : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hE : ∀ y : ℝ, 2 ≤ y → |E y| ≤ Cv * Real.sqrt y * Real.log y)
    (hX : 4096 ≤ Real.sqrt n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (D : ℝ)
    (ht : t * Real.sqrt (Real.sqrt n) ≤ D) :
    (∫⁻ u in Set.Ico (Real.sqrt n) (Real.sqrt n * (1 + t)), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ENNReal.ofReal (2 + 12 * Cv * Real.log n * D) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hXX : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  set X := Real.sqrt n with hXdef
  set L := Real.log n with hLdef
  have hX0 : 0 < X := by linarith
  have hn3600 : 3600 ≤ n := by
    have : (3600 : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hqq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0.le
  set q := Real.sqrt X with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  set B := 3 * Cv * q * L with hBdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  have hB : ∀ y : ℝ, X / 8 ≤ y → y ≤ 8 * X → |E y| ≤ B := by
    intro y hy1 hy2
    have hy : 2 ≤ y := by linarith
    have h1 := hE y hy
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hs : Real.sqrt y ≤ 3 * q := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have hl : Real.log y ≤ L := Real.log_le_log (by linarith) (by nlinarith)
    have h3 : Cv * Real.sqrt y * Real.log y ≤ Cv * (3 * q) * L :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs hCv) hl hl0 (by positivity)
    rw [hBdef]
    linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  refine (loc_lint_Ico n _ _ ((2 + 4 * B) / X) (by positivity) ?_).trans ?_
  · intro u hu
    have hu1 : X ≤ u := hu.1
    have hu2 : u ≤ 2 * X := by nlinarith [hu.2]
    have hWu : (W n u : ℝ) ≤ 2 + 4 * B := W_le_of_abs_E_le n u hn3600 hu1 hu2 B hB
    have hu0 : 0 < u := by linarith
    calc (W n u : ℝ) / u ≤ (2 + 4 * B) / u := div_le_div_of_nonneg_right hWu hu0.le
      _ ≤ (2 + 4 * B) / X := div_le_div_of_nonneg_left (by positivity) hX0 hu1
  · apply ENNReal.ofReal_le_ofReal
    have e : (2 + 4 * B) / X * (X * (1 + t) - X) = 2 * t + 12 * Cv * L * (t * q) := by
      rw [hBdef]; field_simp; ring
    rw [e]
    have : 12 * Cv * L * (t * q) ≤ 12 * Cv * L * D :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    linarith

theorem loc_cover (n : ℕ) (B c : ℝ) (hB0 : 0 ≤ B) (hc : 0 ≤ c)
    (hB : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      (∫⁻ u in Set.Icc (Real.sqrt n * (1 + τ)) (Real.sqrt n * (1 + 2 * τ)),
        ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal (B * (1 + c / τ))) :
    ∀ m : ℕ, (∫⁻ u in Set.Icc (Real.sqrt n * (1 + 1 / 2 ^ (m + 1))) (2 * Real.sqrt n),
        ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal (B * ((m + 1) + c * 2 ^ (m + 2))) := by
  set X := Real.sqrt n with hXdef
  intro m
  induction m with
  | zero =>
    have e1 : X * (1 + 1 / 2 ^ (0 + 1)) = X * (1 + 1 / 2) := by norm_num
    have e2 : 2 * X = X * (1 + 2 * (1 / 2)) := by ring
    rw [e1, e2]
    refine (hB (1 / 2) (by norm_num) le_rfl).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hB0
    have e3 : c / (1 / 2) = 2 * c := by field_simp
    rw [e3]
    push_cast
    nlinarith
  | succ m ih =>
    set τ : ℝ := 1 / 2 ^ (m + 1 + 1) with hτdef
    have hτ0 : 0 < τ := by positivity
    have h2τ : X * (1 + 2 * τ) = X * (1 + 1 / 2 ^ (m + 1)) := by
      rw [hτdef, pow_succ]; field_simp
    have hτ2 : τ ≤ 1 / 2 := by
      rw [hτdef]
      apply one_div_le_one_div_of_le (by norm_num)
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hcτ : c / τ = c * 2 ^ (m + 2) := by
      rw [hτdef, div_div_eq_mul_div, div_one]
    have hsub : Set.Icc (X * (1 + 1 / 2 ^ (m + 1 + 1))) (2 * X) ⊆
        Set.Icc (X * (1 + τ)) (X * (1 + 2 * τ)) ∪ Set.Icc (X * (1 + 1 / 2 ^ (m + 1))) (2 * X) := by
      intro u hu
      rcases le_or_gt u (X * (1 + 2 * τ)) with h1 | h1
      · exact Or.inl ⟨by rw [hτdef]; exact hu.1, h1⟩
      · exact Or.inr ⟨by rw [← h2τ]; exact h1.le, hu.2⟩
    have hP0 : 0 ≤ B * (1 + c / τ) := by positivity
    have hQ0 : 0 ≤ B * ((m + 1) + c * 2 ^ (m + 2)) := by positivity
    calc (∫⁻ u in Set.Icc (X * (1 + 1 / 2 ^ (m + 1 + 1))) (2 * X), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ∫⁻ u in Set.Icc (X * (1 + τ)) (X * (1 + 2 * τ)) ∪
            Set.Icc (X * (1 + 1 / 2 ^ (m + 1))) (2 * X), ENNReal.ofReal ((W n u : ℝ) / u) :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ u in Set.Icc (X * (1 + τ)) (X * (1 + 2 * τ)), ENNReal.ofReal ((W n u : ℝ) / u)) +
            ∫⁻ u in Set.Icc (X * (1 + 1 / 2 ^ (m + 1))) (2 * X), ENNReal.ofReal ((W n u : ℝ) / u) :=
          lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (B * (1 + c / τ)) + ENNReal.ofReal (B * ((m + 1) + c * 2 ^ (m + 2))) :=
          add_le_add (hB τ hτ0 hτ2) ih
      _ = ENNReal.ofReal (B * ((((m + 1 : ℕ) : ℝ) + 1) + c * 2 ^ (m + 1 + 2))) := by
          rw [← ENNReal.ofReal_add hP0 hQ0, hcτ]
          congr 1
          push_cast
          ring

theorem loc_absorb (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt n ^ ε * (Real.log n) ^ 3 ≤ (6 / ε) ^ 3 * (n : ℝ) ^ ε := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hX : Real.sqrt n ^ ε = (n : ℝ) ^ (ε / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0]
    ring_nf
  have hl := Real.log_le_rpow_div hn0 (show 0 < ε / 6 by positivity)
  have hl3 : (Real.log n) ^ 3 ≤ ((n : ℝ) ^ (ε / 6) / (ε / 6)) ^ 3 := pow_le_pow_left₀ hL0 hl 3
  have e1 : ((n : ℝ) ^ (ε / 6) / (ε / 6)) ^ 3 = (6 / ε) ^ 3 * (n : ℝ) ^ (ε / 2) := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
    field_simp
    ring_nf
  have e2 : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
    rw [← Real.rpow_add' hn0 (by positivity)]
    ring_nf
  rw [hX]
  have hpos : 0 ≤ (n : ℝ) ^ (ε / 2) := Real.rpow_nonneg hn0 _
  calc (n : ℝ) ^ (ε / 2) * Real.log n ^ 3 ≤ (n : ℝ) ^ (ε / 2) * ((6 / ε) ^ 3 * (n : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_left (e1 ▸ hl3) hpos
    _ = (6 / ε) ^ 3 * (n : ℝ) ^ ε := by rw [← e2]; ring

theorem loc_count (n M : ℕ) (hM : (2 : ℝ) ^ (M + 6) ≤ Real.sqrt (Real.sqrt n)) :
    (M : ℝ) + 1 ≤ Real.log n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hq : Real.log (Real.sqrt (Real.sqrt n)) = Real.log n / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hn0]; ring
  have h1 := Real.log_le_log (by positivity) hM
  rw [Real.log_pow, hq] at h1
  have h2 := Real.log_two_gt_d9
  push_cast at h1
  have h3 : 0 ≤ ((M : ℝ) + 6) * (Real.log 2 - 0.6931471803) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

theorem loc_final (Cv Cb G E L Mr c2 V : ℝ) (hCv : 0 ≤ Cv) (hCb : 0 ≤ Cb) (hG : 1 ≤ G)
    (hE : 1 ≤ E) (hL : 1 ≤ L) (hM : Mr + 1 ≤ L) (hc : c2 ≤ E) (hV : G * L ^ 3 ≤ V) :
    2 + 12 * Cv * L * (64 * E) + Cb * G * L ^ 2 * ((Mr + 1) + c2)
      ≤ (2 + 768 * Cv + 2 * Cb) * (E * V) := by
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hLL : L ≤ L ^ 3 := le_self_pow₀ hL (by norm_num)
  have hL23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by norm_num)
  have hB0 : 0 ≤ Cb * G * L ^ 2 := by positivity
  have b1 : Cb * G * L ^ 2 * ((Mr + 1) + c2) ≤ Cb * G * L ^ 2 * (L + E) :=
    mul_le_mul_of_nonneg_left (by linarith) hB0
  have b2 : Cb * G * L ^ 3 ≤ Cb * G * L ^ 3 * E := le_mul_of_one_le_right (by positivity) hE
  have b3 : Cb * G * E * L ^ 2 ≤ Cb * G * E * L ^ 3 :=
    mul_le_mul_of_nonneg_left hL23 (by positivity)
  have hU1 : 1 ≤ G * E * L ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hG hE) hL3
  have hLU : L * E ≤ G * E * L ^ 3 := by
    have h1 : L * E ≤ L ^ 3 * E := mul_le_mul_of_nonneg_right hLL (by linarith)
    have h2 : L ^ 3 * E ≤ G * (L ^ 3 * E) := le_mul_of_one_le_left (by positivity) hG
    have e : G * (L ^ 3 * E) = G * E * L ^ 3 := by ring
    linarith
  have n1 : 768 * Cv * (L * E) ≤ 768 * Cv * (G * E * L ^ 3) :=
    mul_le_mul_of_nonneg_left hLU (by positivity)
  have hUV : G * E * L ^ 3 ≤ E * V := by
    have h1 := mul_le_mul_of_nonneg_left hV (show (0 : ℝ) ≤ E by linarith)
    have e : G * E * L ^ 3 = E * (G * L ^ 3) := by ring
    linarith
  have hK0 : 0 ≤ 2 + 768 * Cv + 2 * Cb := by positivity
  have e4 := mul_le_mul_of_nonneg_left hUV hK0
  have e5 : (2 + 768 * Cv + 2 * Cb) * (G * E * L ^ 3) = 2 * (G * E * L ^ 3)
      + 768 * Cv * (G * E * L ^ 3) + 2 * (Cb * G * L ^ 3 * E) := by ring
  have e6 : Cb * G * L ^ 2 * (L + E) = Cb * G * L ^ 3 + Cb * G * E * L ^ 2 := by ring
  have e7 : Cb * G * E * L ^ 3 = Cb * G * L ^ 3 * E := by ring
  have e8 : 12 * Cv * L * (64 * E) = 768 * Cv * (L * E) := by ring
  linarith

theorem loc_large (θ C ε Cv : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hC1 : 1 ≤ C) (hε : 0 < ε)
    (hC : LocLS θ C ε) (hCv : 0 ≤ Cv)
    (hE : ∀ y : ℝ, 2 ≤ y → |E y| ≤ Cv * Real.sqrt y * Real.log y)
    (n : ℕ) (hX24 : 2 ^ 24 ≤ Real.sqrt n) :
    (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ENNReal.ofReal ((2 + 768 * Cv + 2 * (2 ^ 26 * C * 128 ^ (2 + ε))) *
          ((6 / ε) ^ 3 * (n : ℝ) ^ ((1 - 2 * θ) / 8 + ε))) := by
  classical
  have hc1 : 1 ≤ (128 : ℝ) ^ (2 + ε) := Real.one_le_rpow (by norm_num) (by linarith)
  set Cb : ℝ := 2 ^ 26 * C * 128 ^ (2 + ε) with hCbdef
  have hCb0 : 0 ≤ Cb := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hXX : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hX : 4096 ≤ Real.sqrt n := by linarith
  set X := Real.sqrt n with hXdef
  set L := Real.log n with hLdef
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hnpos : (0 : ℝ) < n := by rw [← hXX]; positivity
  have hXn : X ≤ n := by
    have := le_self_pow₀ hX1 (two_ne_zero)
    rw [hXX] at this
    exact this
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hqq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0.le
  have hqr : Real.sqrt X = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
  have h4096 : 4096 ≤ Real.sqrt X :=
    (Real.le_sqrt (by norm_num) hX0.le).mpr (by norm_num; linarith)
  have h64 : 64 ≤ Real.sqrt (Real.sqrt X) :=
    (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr (by norm_num; linarith)
  have h14 : X ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt X) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    norm_num
  set q := Real.sqrt X with hqdef
  set Q := X ^ ((1 + 2 * θ) / 4) with hQdef
  set Eₓ := X ^ ((1 - 2 * θ) / 4) with hEdef
  have hQ64 : 64 ≤ Q := by
    have h1 : X ^ (1 / 4 : ℝ) ≤ Q := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    linarith
  have hQq : Q ≤ q := by
    rw [hqr]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hEQ : Eₓ * Q = q := by
    rw [hEdef, hQdef, ← Real.rpow_add hX0, hqr]
    congr 1
    ring
  have hθQ : X ^ (-θ) * Q = Eₓ := by
    rw [hEdef, hQdef, ← Real.rpow_add hX0]
    congr 1
    ring
  have hE1 : 1 ≤ Eₓ := Real.one_le_rpow hX1 (by linarith)
  have hEn : Eₓ * (n : ℝ) ^ ε = (n : ℝ) ^ ((1 - 2 * θ) / 8 + ε) := by
    rw [hEdef, hXdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0, ← Real.rpow_add hnpos]
    congr 1
    ring
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  have hXe : 1 ≤ X ^ ε := Real.one_le_rpow hX1 hε.le
  have hXθ : 0 ≤ X ^ (-θ) := Real.rpow_nonneg hX0.le _
  have hqX : q ≤ X := by
    have := le_self_pow₀ (show (1 : ℝ) ≤ q by linarith) (two_ne_zero)
    rw [hqq] at this
    exact this
  set P : ℕ → Prop := fun m => (2 : ℝ) ^ (m + 6) ≤ Q with hP
  have hP0 : P 0 := by
    show (2 : ℝ) ^ (0 + 6) ≤ Q
    norm_num
    linarith
  set M := Nat.findGreatest P n with hMdef
  have hPM : P M := Nat.findGreatest_spec (Nat.zero_le n) hP0
  have hPM' : (2 : ℝ) ^ (M + 6) ≤ Q := hPM
  have hMn : M + 1 ≤ n := by
    have h1 : M + 6 < 2 ^ (M + 6) := Nat.lt_two_pow_self
    have h2 : ((M + 6 : ℕ) : ℝ) < n := by
      calc ((M + 6 : ℕ) : ℝ) < ((2 ^ (M + 6) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2 : ℝ) ^ (M + 6) := by push_cast; ring
        _ ≤ n := by linarith
    have h3 : M + 6 < n := by exact_mod_cast h2
    omega
  have hnotP : ¬ P (M + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self M) hMn
  have hnotP' : Q < (2 : ℝ) ^ (M + 1 + 6) := not_le.mp hnotP
  have hML : (M : ℝ) + 1 ≤ L := loc_count n M (hPM'.trans hQq)
  set t : ℝ := 1 / 2 ^ (M + 1) with htdef
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have htQ : t * Q ≤ 64 := by
    rw [htdef, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    have e : (2 : ℝ) ^ (M + 1 + 6) = 64 * 2 ^ (M + 1) := by
      rw [pow_add]; norm_num; ring
    linarith
  have htq : t * q ≤ 64 * Eₓ := by
    calc t * q = Eₓ * (t * Q) := by rw [← hEQ]; ring
      _ ≤ Eₓ * 64 := mul_le_mul_of_nonneg_left htQ (by linarith)
      _ = 64 * Eₓ := by ring
  have hnear := loc_near n Cv hCv hE hX t ht0 ht1 (64 * Eₓ) htq
  have hbands := loc_cover n (Cb * X ^ ε * L ^ 2) (16 * X ^ (-θ)) (by positivity)
    (by positivity)
    (fun τ hτ0 hτ2 => loc_band_at θ C ε hθ0 (by linarith) hC1 hε hC n hX τ hτ0 hτ2) M
  have hsub : Set.Ico X (2 * X) ⊆ Set.Ico X (X * (1 + t)) ∪ Set.Icc (X * (1 + t)) (2 * X) := by
    intro u hu
    rcases lt_or_ge u (X * (1 + t)) with h1 | h1
    · exact Or.inl ⟨hu.1, h1⟩
    · exact Or.inr ⟨h1, hu.2.le⟩
  have habs := loc_absorb n hn1 ε hε
  have hcM : 16 * X ^ (-θ) * 2 ^ (M + 2) ≤ Eₓ := by
    have e : 16 * X ^ (-θ) * 2 ^ (M + 2) = X ^ (-θ) * 2 ^ (M + 6) := by ring
    rw [e, ← hθQ]
    exact mul_le_mul_of_nonneg_left hPM' hXθ
  have hfin := loc_final Cv Cb (X ^ ε) Eₓ L (M : ℝ) (16 * X ^ (-θ) * 2 ^ (M + 2))
    ((6 / ε) ^ 3 * (n : ℝ) ^ ε) hCv hCb0 hXe hE1 hL1 hML hcM habs
  have hEV : Eₓ * ((6 / ε) ^ 3 * (n : ℝ) ^ ε) = (6 / ε) ^ 3 * (n : ℝ) ^ ((1 - 2 * θ) / 8 + ε) := by
    rw [← hEn]; ring
  rw [hEV] at hfin
  calc (∫⁻ u in Set.Ico X (2 * X), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ∫⁻ u in Set.Ico X (X * (1 + t)) ∪ Set.Icc (X * (1 + t)) (2 * X),
          ENNReal.ofReal ((W n u : ℝ) / u) := lintegral_mono_set hsub
    _ ≤ (∫⁻ u in Set.Ico X (X * (1 + t)), ENNReal.ofReal ((W n u : ℝ) / u)) +
          ∫⁻ u in Set.Icc (X * (1 + t)) (2 * X), ENNReal.ofReal ((W n u : ℝ) / u) :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (2 + 12 * Cv * L * (64 * Eₓ)) +
          ENNReal.ofReal (Cb * X ^ ε * L ^ 2 * ((M + 1) + 16 * X ^ (-θ) * 2 ^ (M + 2))) :=
        add_le_add hnear hbands
    _ = ENNReal.ofReal (2 + 12 * Cv * L * (64 * Eₓ) +
          Cb * X ^ ε * L ^ 2 * ((M + 1) + 16 * X ^ (-θ) * 2 ^ (M + 2))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

theorem localised_bound_at (hV : VonKoch) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2)
    (hLS : HypothesisLSAt θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ ((1 - 2 * θ) / 8 + ε)) := by
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := hLS ε hε
  set C := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC : LocLS θ C ε := by
    intro x hx η hη hη1 δ hδ hδ1
    have h := hC₀ x hx η hη hη1 δ hδ hδ1
    have hη0 : 0 ≤ η := le_trans (Real.rpow_nonneg (by linarith) _) hη
    have hxe : 0 ≤ x ^ (2 + ε) := Real.rpow_nonneg (by linarith) _
    have h0 : 0 ≤ δ * η * x ^ (2 + ε) := by positivity
    have hm := mul_le_mul_of_nonneg_right (le_max_left C₀ 1) h0
    have e1 : C₀ * δ * η * x ^ (2 + ε) = C₀ * (δ * η * x ^ (2 + ε)) := by ring
    have e2 : C * δ * η * x ^ (2 + ε) = C * (δ * η * x ^ (2 + ε)) := by ring
    rw [e2]
    linarith
  obtain ⟨Cv0, hCv0⟩ := hV
  set Cv := max Cv0 0 with hCvdef
  have hCv : 0 ≤ Cv := le_max_right _ _
  have hE : ∀ y : ℝ, 2 ≤ y → |E y| ≤ Cv * Real.sqrt y * Real.log y := by
    intro y hy
    have h1 := hCv0 y hy
    have h2 : Cv0 * Real.sqrt y * Real.log y ≤ Cv * Real.sqrt y * Real.log y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.sqrt_nonneg y)) (Real.log_nonneg (by linarith))
    unfold E
    linarith
  have hc1 : 1 ≤ (128 : ℝ) ^ (2 + ε) := Real.one_le_rpow (by norm_num) (by linarith)
  set K : ℝ := 2 + 768 * Cv + 2 * (2 ^ 26 * C * 128 ^ (2 + ε)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  set N0 : ℝ := 2 ^ 48 with hN0
  refine ⟨(N0 + 1) * N0 + K * (6 / ε) ^ 3, ?_⟩
  intro n hn
  set γ := (1 - 2 * θ) / 8 + ε with hγdef
  have hγ0 : 0 ≤ γ := by rw [hγdef]; linarith
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hne : 1 ≤ (n : ℝ) ^ γ := Real.one_le_rpow (by linarith) hγ0
  have hA : 0 ≤ (N0 + 1) * N0 := by positivity
  have hXX : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hX1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
  have hsplit : ((N0 + 1) * N0 + K * (6 / ε) ^ 3) * (n : ℝ) ^ γ
      = (N0 + 1) * N0 * (n : ℝ) ^ γ + K * ((6 / ε) ^ 3 * (n : ℝ) ^ γ) := by ring
  have hpos1 : 0 ≤ (N0 + 1) * N0 * (n : ℝ) ^ γ := by positivity
  have hpos2 : 0 ≤ K * ((6 / ε) ^ 3 * (n : ℝ) ^ γ) := by positivity
  rw [hsplit]
  by_cases hsmall : (n : ℝ) < N0
  · have hXn : Real.sqrt n ≤ n := by
      have := le_self_pow₀ hX1 (two_ne_zero)
      rw [hXX] at this
      exact this
    calc (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal ((n + 1) * (2 * Real.sqrt n - Real.sqrt n)) :=
          loc_lint_Ico n _ _ _ (by positivity) (fun u hu => loc_trivial n u (by linarith [hu.1]))
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have e1 : ((n : ℝ) + 1) * (2 * Real.sqrt n - Real.sqrt n) ≤ ((n : ℝ) + 1) * n :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have e2 : ((n : ℝ) + 1) * n ≤ (N0 + 1) * N0 :=
            mul_le_mul (by linarith) hsmall.le (by positivity) (by positivity)
          have e3 : (N0 + 1) * N0 ≤ (N0 + 1) * N0 * (n : ℝ) ^ γ :=
            le_mul_of_one_le_right hA hne
          linarith
  · replace hsmall := not_lt.mp hsmall
    have hX24 : 2 ^ 24 ≤ Real.sqrt n := by
      apply (Real.le_sqrt (by norm_num) hn0).mpr
      rw [hN0] at hsmall
      norm_num at hsmall ⊢
      linarith
    refine (loc_large θ C ε Cv hθ0 hθ hC1 hε hC hCv hE n hX24).trans
      (ENNReal.ofReal_le_ofReal ?_)
    linarith

theorem localised_bound (hV : VonKoch) (hLS : HypothesisLS) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ ε) := by
  intro ε hε
  obtain ⟨C, hC⟩ := localised_bound_at hV (1 / 2) (by norm_num) le_rfl hLS ε hε
  refine ⟨C, fun n hn => ?_⟩
  have h := hC n hn
  rwa [show (1 - 2 * (1 / 2 : ℝ)) / 8 + ε = ε by ring] at h

end Erdos879
