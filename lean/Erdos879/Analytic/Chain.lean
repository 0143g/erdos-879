import Erdos879.Analytic.Defs

open Finset MeasureTheory

namespace Erdos879

lemma chain_ii_inv_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x ≠ 0 := by grind
  have : Real.log x ≠ 0 := Real.log_ne_zero.mpr (by grind)
  fun_prop (disch := assumption)

lemma chain_ii_g {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (c : ℝ → ℝ) (hc : Continuous c) :
    IntervalIntegrable (fun t : ℝ => c t / (t * Real.log t ^ 2)) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx => ContinuousAt.continuousWithinAt ?_
  rw [Set.mem_uIcc] at hx
  have : x ≠ 0 := by grind
  have : Real.log x ≠ 0 := Real.log_ne_zero.mpr (by grind)
  have : x * Real.log x ^ 2 ≠ 0 := by positivity
  exact hc.continuousAt.div (by fun_prop) this

lemma chain_integral_g {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (t * Real.log t ^ 2) = 1 / Real.log a - 1 / Real.log b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun t => -(Real.log t)⁻¹) (f' := fun t => 1 / (t * Real.log t ^ 2)) ?_ ?_
  · rw [h]; simp only [one_div]; ring
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have h1 := Real.hasDerivAt_inv_log (x := x) (by linarith [hx.1]) (by linarith [hx.1])
      (by linarith [hx.1])
    have : x ≠ 0 := by linarith [hx.1]
    convert h1.neg using 1
    · ext t; simp
    · field_simp
  · exact chain_ii_g ha (by linarith) (fun _ => 1) continuous_const

lemma chain_ii_theta {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume a b := by
  have h := (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (2:ℝ) ≤ b)).mpr
    (Chebyshev.integrableOn_theta_div_id_mul_log_sq b)
  refine h.mono_set ?_
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith)]
  exact Set.Icc_subset_Icc ha le_rfl


lemma chain_li_split {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t
      = (b - a) / Real.log b + ∫ t in a..b, (t - a) / (t * Real.log t ^ 2) := by
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t => (t - a) / Real.log t)
      (1 / Real.log x - (x - a) / (x * Real.log x ^ 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hl : Real.log x ≠ 0 := Real.log_ne_zero.mpr (by grind)
    have h1 : HasDerivAt (fun t => (t - a) / Real.log t)
        ((1 * Real.log x - (x - a) * x⁻¹) / Real.log x ^ 2) x :=
      ((hasDerivAt_id' x).sub_const a).fun_div (Real.hasDerivAt_log hx0) hl
    convert h1 using 1
    field_simp
  have hi1 := chain_ii_inv_log (a := a) (b := b) (by linarith) (by linarith)
  have hi2 := chain_ii_g (a := a) (b := b) (by linarith) (by linarith) (fun t => t - a)
    (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2] at h
  rw [sub_self, zero_div, sub_zero] at h
  linarith

theorem E_sub_eq (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    E b - E a = (F b - F a) / Real.log b
      + ∫ t in a..b, (F t - F a) / (t * (Real.log t) ^ 2) := by
  have hpi : piR b - piR a = Chebyshev.theta b / Real.log b - Chebyshev.theta a / Real.log a
      + ∫ t in a..b, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    unfold piR
    rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith),
      Chebyshev.primeCounting_eq_theta_div_log_add_integral ha,
      ← intervalIntegral.integral_interval_sub_left (chain_ii_theta le_rfl (by linarith))
        (chain_ii_theta le_rfl ha)]
    ring
  have hli : li b - li a = ∫ t in a..b, 1 / Real.log t := by
    unfold li
    exact intervalIntegral.integral_interval_sub_left (chain_ii_inv_log (by norm_num)
      (by linarith)) (chain_ii_inv_log (by norm_num) (by linarith))
  have hF : ∫ t in a..b, (F t - F a) / (t * (Real.log t) ^ 2)
      = (∫ t in a..b, Chebyshev.theta t / (t * Real.log t ^ 2))
        - (∫ t in a..b, (t - a) / (t * Real.log t ^ 2))
        - Chebyshev.theta a * ∫ t in a..b, 1 / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (chain_ii_theta ha hab)
        (chain_ii_g (by linarith) (by linarith) (fun t => t - a) (by fun_prop)),
      ← intervalIntegral.integral_sub ((chain_ii_theta ha hab).sub
        (chain_ii_g (by linarith) (by linarith) (fun t => t - a) (by fun_prop)))
        ((chain_ii_g (by linarith) (by linarith) (fun _ => 1) continuous_const).const_mul _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [F]
    ring
  have hE : E b - E a = (piR b - piR a) - (li b - li a) := by unfold E; ring
  rw [hE, hF, hpi, hli, chain_li_split ha hab, chain_integral_g (by linarith) hab]
  simp only [F]
  ring


lemma chain_arg_two (i : ℕ) (r : ℝ) (k : ℕ) :
    ((2 * i : ℕ) : ℝ) * r / 2 ^ (k + 1) = (i : ℝ) * r / 2 ^ k := by
  push_cast
  rw [pow_succ]
  field_simp

lemma chain_tele (G : ℝ → ℝ) (r : ℝ) (D : ℕ → ℕ → ℝ)
    (hD : ∀ j l : ℕ, (G (((l : ℝ) + 1) * r / 2 ^ j) - G ((l : ℝ) * r / 2 ^ j)) ^ 2 = (D j l) ^ 2) :
    ∀ k i : ℕ, i ≤ 2 ^ k → |G ((i : ℝ) * r / 2 ^ k) - G 0|
      ≤ ∑ j ∈ range (k + 1), Real.sqrt (∑ l ∈ range (2 ^ j), (D j l) ^ 2) := by
  have hS : ∀ j l : ℕ, l < 2 ^ j →
      |G (((l : ℝ) + 1) * r / 2 ^ j) - G ((l : ℝ) * r / 2 ^ j)|
        ≤ Real.sqrt (∑ l ∈ range (2 ^ j), (D j l) ^ 2) := by
    intro j l hl
    apply Real.abs_le_sqrt
    rw [hD]
    exact single_le_sum (f := fun l => (D j l) ^ 2) (fun _ _ => sq_nonneg _) (mem_range.mpr hl)
  intro k
  induction k with
  | zero =>
    intro i hi
    interval_cases i
    · simp
    · have := hS 0 0 (by norm_num)
      simpa using this
  | succ k ih =>
    intro i hi
    rw [sum_range_succ]
    have hnn := Real.sqrt_nonneg (∑ l ∈ range (2 ^ (k + 1)), (D (k + 1) l) ^ 2)
    rcases Nat.even_or_odd' i with ⟨i', rfl | rfl⟩
    · have h1 := ih i' (by rw [pow_succ] at hi; omega)
      rw [chain_arg_two]
      linarith
    · have h1 := ih i' (by rw [pow_succ] at hi; omega)
      have h2 := hS (k + 1) (2 * i') (by omega)
      have e1 : ((2 * i' + 1 : ℕ) : ℝ) = ((2 * i' : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e1, chain_arg_two] at *
      calc |G ((((2 * i' : ℕ) : ℝ) + 1) * r / 2 ^ (k + 1)) - G 0|
          = |(G ((((2 * i' : ℕ) : ℝ) + 1) * r / 2 ^ (k + 1)) - G ((i' : ℝ) * r / 2 ^ k))
              + (G ((i' : ℝ) * r / 2 ^ k) - G 0)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := by linarith


lemma chain_floor (r s : ℝ) (k : ℕ) (hr : 0 < r) (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    ∃ i : ℕ, i ≤ 2 ^ k ∧ (i : ℝ) * r / 2 ^ k ≤ s ∧ s ≤ ((i : ℝ) + 1) * r / 2 ^ k ∧
      (i = 2 ^ k → s = (i : ℝ) * r / 2 ^ k) := by
  have hμ : 0 < r / 2 ^ k := by positivity
  have h1 : ((⌊s / (r / 2 ^ k)⌋₊ : ℕ) : ℝ) ≤ s / (r / 2 ^ k) := Nat.floor_le (by positivity)
  have h2 : s / (r / 2 ^ k) < ((⌊s / (r / 2 ^ k)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hμ] at h1
  rw [div_lt_iff₀ hμ] at h2
  set i := ⌊s / (r / 2 ^ k)⌋₊
  have hr' : r = (2 ^ k : ℝ) * (r / 2 ^ k) := by field_simp
  have hi : i ≤ 2 ^ k := by
    by_contra h
    push Not at h
    have h3 : ((2 ^ k : ℕ) : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
    push_cast at h3
    nlinarith
  refine ⟨i, hi, ?_, ?_, ?_⟩
  · rw [mul_div_assoc]; exact h1
  · rw [mul_div_assoc]; exact h2.le
  · intro h
    rw [h, mul_div_assoc]
    push_cast
    rw [← hr']
    rw [h] at h1
    push_cast at h1
    rw [← hr'] at h1
    linarith

theorem Bp_nonneg (r : ℝ) (k : ℕ) (y : ℝ) (hr : 0 ≤ r) (hy : 0 ≤ y) : 0 ≤ Bp r k y := by
  unfold Bp
  have h1 : 0 ≤ ∑ j ∈ range (k + 1), Real.sqrt (∑ l ∈ range (2 ^ j), (Dp r j l y) ^ 2) :=
    sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.exp (r / 2 ^ k) - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have h3 : 0 ≤ y * Real.exp r * (Real.exp (r / 2 ^ k) - 1) := by positivity
  linarith

theorem Bm_nonneg (r : ℝ) (k : ℕ) (y : ℝ) (hr : 0 ≤ r) (hy : 0 ≤ y) : 0 ≤ Bm r k y := by
  unfold Bm
  have h1 : 0 ≤ ∑ j ∈ range (k + 1), Real.sqrt (∑ l ∈ range (2 ^ j), (Dm r j l y) ^ 2) :=
    sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.exp (r / 2 ^ k) - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have h3 : 0 ≤ y * (Real.exp (r / 2 ^ k) - 1) := by positivity
  linarith

lemma chain_rem_plus (r : ℝ) (k i : ℕ) (y s : ℝ) (hy : 0 < y) (hr : 0 < r) (hi : i ≤ 2 ^ k)
    (hlo : (i : ℝ) * r / 2 ^ k ≤ s) (hhi : s ≤ ((i : ℝ) + 1) * r / 2 ^ k)
    (heq : i = 2 ^ k → s = (i : ℝ) * r / 2 ^ k) (hsr : s ≤ r) :
    |F (y * Real.exp s) - F (y * Real.exp ((i : ℝ) * r / 2 ^ k))|
      ≤ Real.sqrt (∑ l ∈ range (2 ^ k), (Dp r k l y) ^ 2)
        + y * Real.exp r * (Real.exp (r / 2 ^ k) - 1) := by
  have hm : 0 ≤ Real.exp (r / 2 ^ k) - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hE : 0 ≤ y * Real.exp r * (Real.exp (r / 2 ^ k) - 1) := by positivity
  have hq := Real.sqrt_nonneg (∑ l ∈ range (2 ^ k), (Dp r k l y) ^ 2)
  rcases lt_or_eq_of_le hi with hlt | heq'
  · have hA : y * Real.exp ((i : ℝ) * r / 2 ^ k) ≤ y * Real.exp s :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlo) hy.le
    have hX : y * Real.exp s ≤ y * Real.exp (((i : ℝ) + 1) * r / 2 ^ k) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hhi) hy.le
    have hθ1 := Chebyshev.theta_mono hA
    have hθ2 := Chebyshev.theta_mono hX
    have hCA : y * Real.exp (((i : ℝ) + 1) * r / 2 ^ k) - y * Real.exp ((i : ℝ) * r / 2 ^ k)
        ≤ y * Real.exp r * (Real.exp (r / 2 ^ k) - 1) := by
      have e : y * Real.exp (((i : ℝ) + 1) * r / 2 ^ k) - y * Real.exp ((i : ℝ) * r / 2 ^ k)
          = y * Real.exp ((i : ℝ) * r / 2 ^ k) * (Real.exp (r / 2 ^ k) - 1) := by
        rw [show ((i : ℝ) + 1) * r / 2 ^ k = (i : ℝ) * r / 2 ^ k + r / 2 ^ k by ring,
          Real.exp_add]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hlo.trans hsr)) hy.le) hm
    have hD : |Dp r k i y| ≤ Real.sqrt (∑ l ∈ range (2 ^ k), (Dp r k l y) ^ 2) :=
      Real.abs_le_sqrt (single_le_sum (f := fun l => (Dp r k l y) ^ 2)
        (fun _ _ => sq_nonneg _) (mem_range.mpr hlt))
    have hDe : Dp r k i y = F (y * Real.exp (((i : ℝ) + 1) * r / 2 ^ k))
        - F (y * Real.exp ((i : ℝ) * r / 2 ^ k)) := rfl
    have hDa := le_abs_self (Dp r k i y)
    unfold F at *
    rw [abs_le]
    constructor <;> linarith
  · rw [← heq heq']
    simp only [sub_self, abs_zero]
    linarith

lemma chain_rem_minus (r : ℝ) (k i : ℕ) (y s : ℝ) (hy : 0 < y) (hr : 0 < r) (hi : i ≤ 2 ^ k)
    (hlo : (i : ℝ) * r / 2 ^ k ≤ s) (hhi : s ≤ ((i : ℝ) + 1) * r / 2 ^ k)
    (heq : i = 2 ^ k → s = (i : ℝ) * r / 2 ^ k) :
    |F (y * Real.exp (-s)) - F (y * Real.exp (-((i : ℝ) * r / 2 ^ k)))|
      ≤ Real.sqrt (∑ l ∈ range (2 ^ k), (Dm r k l y) ^ 2)
        + y * (Real.exp (r / 2 ^ k) - 1) := by
  have hm : 0 ≤ Real.exp (r / 2 ^ k) - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hE : 0 ≤ y * (Real.exp (r / 2 ^ k) - 1) := by positivity
  have hq := Real.sqrt_nonneg (∑ l ∈ range (2 ^ k), (Dm r k l y) ^ 2)
  rcases lt_or_eq_of_le hi with hlt | heq'
  · have hA : y * Real.exp (-s) ≤ y * Real.exp (-((i : ℝ) * r / 2 ^ k)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hy.le
    have hX : y * Real.exp (-(((i : ℝ) + 1) * r / 2 ^ k)) ≤ y * Real.exp (-s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hy.le
    have hθ1 := Chebyshev.theta_mono hA
    have hθ2 := Chebyshev.theta_mono hX
    have hCA : y * Real.exp (-((i : ℝ) * r / 2 ^ k)) - y * Real.exp (-(((i : ℝ) + 1) * r / 2 ^ k))
        ≤ y * (Real.exp (r / 2 ^ k) - 1) := by
      have e : y * Real.exp (-((i : ℝ) * r / 2 ^ k)) - y * Real.exp (-(((i : ℝ) + 1) * r / 2 ^ k))
          = y * Real.exp (-(((i : ℝ) + 1) * r / 2 ^ k)) * (Real.exp (r / 2 ^ k) - 1) := by
        rw [mul_assoc, mul_sub, ← Real.exp_add,
          show -(((i : ℝ) + 1) * r / 2 ^ k) + r / 2 ^ k = -((i : ℝ) * r / 2 ^ k) by ring]
        ring
      rw [e]
      have h1 : Real.exp (-(((i : ℝ) + 1) * r / 2 ^ k)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have : 0 ≤ ((i : ℝ) + 1) * r / 2 ^ k := by positivity
          linarith)
      have h2 : y * Real.exp (-(((i : ℝ) + 1) * r / 2 ^ k)) ≤ y := by
        calc _ ≤ y * 1 := mul_le_mul_of_nonneg_left h1 hy.le
          _ = y := mul_one y
      exact mul_le_mul_of_nonneg_right h2 hm
    have hD : |Dm r k i y| ≤ Real.sqrt (∑ l ∈ range (2 ^ k), (Dm r k l y) ^ 2) :=
      Real.abs_le_sqrt (single_le_sum (f := fun l => (Dm r k l y) ^ 2)
        (fun _ _ => sq_nonneg _) (mem_range.mpr hlt))
    have hDe : Dm r k i y = F (y * Real.exp (-((i : ℝ) * r / 2 ^ k)))
        - F (y * Real.exp (-(((i : ℝ) + 1) * r / 2 ^ k))) := rfl
    have hDa := le_abs_self (Dm r k i y)
    unfold F at *
    rw [abs_le]
    constructor <;> linarith
  · rw [← heq heq']
    simp only [sub_self, abs_zero]
    linarith

theorem chain_plus (r : ℝ) (k : ℕ) (y s : ℝ) (hy : 0 < y) (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    |F (y * Real.exp s) - F y| ≤ Bp r k y := by
  rcases eq_or_lt_of_le (hs0.trans hsr) with hr | hr
  · have hs : s = 0 := le_antisymm (hr ▸ hsr) hs0
    subst hs
    simp only [Real.exp_zero, mul_one, sub_self, abs_zero]
    exact Bp_nonneg r k y hsr hy.le
  · obtain ⟨i, hi, hlo, hhi, heq⟩ := chain_floor r s k hr hs0 hsr
    have htele := chain_tele (fun x => F (y * Real.exp x)) r (fun j l => Dp r j l y)
      (fun _ _ => rfl) k i hi
    simp only [Real.exp_zero, mul_one] at htele
    have hSk : Real.sqrt (∑ l ∈ range (2 ^ k), (Dp r k l y) ^ 2)
        ≤ ∑ j ∈ range (k + 1), Real.sqrt (∑ l ∈ range (2 ^ j), (Dp r j l y) ^ 2) :=
      single_le_sum (f := fun j => Real.sqrt (∑ l ∈ range (2 ^ j), (Dp r j l y) ^ 2))
        (fun _ _ => Real.sqrt_nonneg _) (self_mem_range_succ k)
    have hrem := chain_rem_plus r k i y s hy hr hi hlo hhi heq hsr
    have htri := abs_sub_le (F (y * Real.exp s)) (F (y * Real.exp ((i : ℝ) * r / 2 ^ k))) (F y)
    unfold Bp
    linarith

theorem chain_minus (r : ℝ) (k : ℕ) (y s : ℝ) (hy : 0 < y) (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    |F (y * Real.exp (-s)) - F y| ≤ Bm r k y := by
  rcases eq_or_lt_of_le (hs0.trans hsr) with hr | hr
  · have hs : s = 0 := le_antisymm (hr ▸ hsr) hs0
    subst hs
    simp only [neg_zero, Real.exp_zero, mul_one, sub_self, abs_zero]
    exact Bm_nonneg r k y hsr hy.le
  · obtain ⟨i, hi, hlo, hhi, heq⟩ := chain_floor r s k hr hs0 hsr
    have htele := chain_tele (fun x => F (y * Real.exp (-x))) r (fun j l => Dm r j l y)
      (fun j l => by simp only [Dm]; ring) k i hi
    simp only [neg_zero, Real.exp_zero, mul_one] at htele
    have hSk : Real.sqrt (∑ l ∈ range (2 ^ k), (Dm r k l y) ^ 2)
        ≤ ∑ j ∈ range (k + 1), Real.sqrt (∑ l ∈ range (2 ^ j), (Dm r j l y) ^ 2) :=
      single_le_sum (f := fun j => Real.sqrt (∑ l ∈ range (2 ^ j), (Dm r j l y) ^ 2))
        (fun _ _ => Real.sqrt_nonneg _) (self_mem_range_succ k)
    have hrem := chain_rem_minus r k i y s hy hr hi hlo hhi heq
    have htri := abs_sub_le (F (y * Real.exp (-s)))
      (F (y * Real.exp (-((i : ℝ) * r / 2 ^ k)))) (F y)
    unfold Bm
    linarith


lemma chain_abs_int_le {a b B : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (h : ℝ → ℝ)
    (hh : ∀ t ∈ Set.Icc a b, |h t| ≤ B) :
    |∫ t in a..b, h t / (t * Real.log t ^ 2)| ≤ B * (1 / Real.log a - 1 / Real.log b) := by
  rw [← chain_integral_g (by linarith) hab, ← intervalIntegral.integral_const_mul]
  have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun t => h t / (t * Real.log t ^ 2))
    (g := fun t => B * (1 / (t * Real.log t ^ 2))) hab ?_
    ((chain_ii_g (by linarith) (by linarith) (fun _ => 1) continuous_const).const_mul B)
  · simpa only [Real.norm_eq_abs] using this
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    have hpos : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right (hh t ⟨ht.1.le, ht.2⟩) hpos.le

theorem abs_E_exp_sub_le (r : ℝ) (k : ℕ) (y s : ℝ) (hy : 2 ≤ y) (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    |E (y * Real.exp s) - E y| ≤ Bp r k y / Real.log y := by
  have hy0 : 0 < y := by linarith
  have hb : y ≤ y * Real.exp s := le_mul_of_one_le_right hy0.le (Real.one_le_exp hs0)
  have hB0 : 0 ≤ Bp r k y := Bp_nonneg r k y (hs0.trans hsr) hy0.le
  have hFt : ∀ t ∈ Set.Icc y (y * Real.exp s), |F t - F y| ≤ Bp r k y := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : 1 ≤ t / y := by rw [le_div_iff₀ hy0]; linarith [ht.1]
    have h2 : t / y ≤ Real.exp s := by rw [div_le_iff₀ hy0]; linarith [ht.2]
    have hσ0 : 0 ≤ Real.log (t / y) := Real.log_nonneg h1
    have hσs : Real.log (t / y) ≤ s := (Real.log_le_iff_le_exp (by positivity)).mpr h2
    have := chain_plus r k y (Real.log (t / y)) hy0 hσ0 (hσs.trans hsr)
    rwa [Real.exp_log (by positivity), mul_div_cancel₀ t hy0.ne'] at this
  have hlb : 0 < Real.log (y * Real.exp s) := Real.log_pos (by linarith)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  rw [E_sub_eq y (y * Real.exp s) hy hb]
  have hI := chain_abs_int_le hy hb (fun t => F t - F y) hFt
  have hFb : |F (y * Real.exp s) - F y| / Real.log (y * Real.exp s)
      ≤ Bp r k y / Real.log (y * Real.exp s) :=
    div_le_div_of_nonneg_right (hFt _ ⟨hb, le_rfl⟩) hlb.le
  calc _ ≤ |(F (y * Real.exp s) - F y) / Real.log (y * Real.exp s)|
        + |∫ t in y..y * Real.exp s, (F t - F y) / (t * Real.log t ^ 2)| := abs_add_le _ _
    _ ≤ Bp r k y / Real.log (y * Real.exp s)
        + Bp r k y * (1 / Real.log y - 1 / Real.log (y * Real.exp s)) := by
      rw [abs_div, abs_of_pos hlb]
      exact add_le_add hFb hI
    _ = Bp r k y / Real.log y := by field_simp; ring

theorem abs_E_exp_neg_sub_le (r : ℝ) (k : ℕ) (y s : ℝ) (hy : 2 ≤ y * Real.exp (-r))
    (hs0 : 0 ≤ s) (hsr : s ≤ r) :
    |E (y * Real.exp (-s)) - E y| ≤ 2 * Bm r k y / Real.log (y * Real.exp (-r)) := by
  have hr0 : 0 ≤ r := hs0.trans hsr
  have hy0 : 0 < y := by
    by_contra h
    push Not at h
    have : y * Real.exp (-r) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos _).le
    linarith
  have hya : y * Real.exp (-r) ≤ y * Real.exp (-s) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hy0.le
  have hab : y * Real.exp (-s) ≤ y :=
    mul_le_of_le_one_right hy0.le (Real.exp_le_one_iff.mpr (by linarith))
  have ha2 : 2 ≤ y * Real.exp (-s) := hy.trans hya
  have hB0 : 0 ≤ Bm r k y := Bm_nonneg r k y hr0 hy0.le
  have hFt : ∀ t ∈ Set.Icc (y * Real.exp (-s)) y, |F t - F y| ≤ Bm r k y := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : 1 ≤ y / t := by rw [le_div_iff₀ ht0]; linarith [ht.2]
    have h2 : y / t ≤ Real.exp s := by
      rw [div_le_iff₀ ht0]
      have := mul_le_mul_of_nonneg_left ht.1 (Real.exp_pos s).le
      rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
      linarith
    have hσ0 : 0 ≤ Real.log (y / t) := Real.log_nonneg h1
    have hσs : Real.log (y / t) ≤ s := (Real.log_le_iff_le_exp (by positivity)).mpr h2
    have := chain_minus r k y (Real.log (y / t)) hy0 hσ0 (hσs.trans hsr)
    rwa [Real.exp_neg, Real.exp_log (by positivity), inv_div, mul_div_cancel₀ t hy0.ne'] at this
  have hFt2 : ∀ t ∈ Set.Icc (y * Real.exp (-s)) y,
      |F t - F (y * Real.exp (-s))| ≤ 2 * Bm r k y := by
    intro t ht
    have h1 := hFt t ht
    have h2 := hFt _ ⟨le_rfl, hab⟩
    have h3 := abs_sub_le (F t) (F y) (F (y * Real.exp (-s)))
    rw [abs_sub_comm (F y)] at h3
    linarith
  have hla : 0 < Real.log (y * Real.exp (-s)) := Real.log_pos (by linarith)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlr : 0 < Real.log (y * Real.exp (-r)) := Real.log_pos (by linarith)
  have hlra : Real.log (y * Real.exp (-r)) ≤ Real.log (y * Real.exp (-s)) :=
    Real.log_le_log (by linarith) hya
  rw [abs_sub_comm, E_sub_eq (y * Real.exp (-s)) y ha2 hab]
  have hI := chain_abs_int_le ha2 hab (fun t => F t - F (y * Real.exp (-s))) hFt2
  have hFb : |F y - F (y * Real.exp (-s))| / Real.log y ≤ 2 * Bm r k y / Real.log y := by
    apply div_le_div_of_nonneg_right _ hly.le
    have := hFt _ ⟨le_rfl, hab⟩
    rw [abs_sub_comm] at this
    linarith
  calc _ ≤ |(F y - F (y * Real.exp (-s))) / Real.log y|
        + |∫ t in y * Real.exp (-s)..y, (F t - F (y * Real.exp (-s))) / (t * Real.log t ^ 2)| :=
        abs_add_le _ _
    _ ≤ 2 * Bm r k y / Real.log y
        + 2 * Bm r k y * (1 / Real.log (y * Real.exp (-s)) - 1 / Real.log y) := by
      rw [abs_div, abs_of_pos hly]
      exact add_le_add hFb hI
    _ = 2 * Bm r k y / Real.log (y * Real.exp (-s)) := by field_simp; ring
    _ ≤ 2 * Bm r k y / Real.log (y * Real.exp (-r)) :=
      div_le_div_of_nonneg_left (by linarith) hlr hlra

lemma chain_primeCounting_succ_le (n : ℕ) : Nat.primeCounting (n + 1) ≤ Nat.primeCounting n + 1 := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

lemma chain_piR_diff {y₁ y₂ : ℝ} (h0 : 0 ≤ y₂) (h : y₂ ≤ y₁) (h1 : y₁ ≤ y₂ + 1) :
    0 ≤ piR y₁ - piR y₂ ∧ piR y₁ - piR y₂ ≤ 1 := by
  have hf1 : ⌊y₂⌋₊ ≤ ⌊y₁⌋₊ := Nat.floor_le_floor h
  have hf2 : ⌊y₁⌋₊ ≤ ⌊y₂⌋₊ + 1 := by
    rw [← Nat.floor_add_one h0]
    exact Nat.floor_le_floor h1
  have m1 : Nat.primeCounting ⌊y₂⌋₊ ≤ Nat.primeCounting ⌊y₁⌋₊ := Nat.monotone_primeCounting hf1
  have m2 : Nat.primeCounting ⌊y₁⌋₊ ≤ Nat.primeCounting ⌊y₂⌋₊ + 1 :=
    (Nat.monotone_primeCounting hf2).trans (chain_primeCounting_succ_le _)
  unfold piR
  constructor
  · have : (Nat.primeCounting ⌊y₂⌋₊ : ℝ) ≤ Nat.primeCounting ⌊y₁⌋₊ := by exact_mod_cast m1
    linarith
  · have : (Nat.primeCounting ⌊y₁⌋₊ : ℝ) ≤ Nat.primeCounting ⌊y₂⌋₊ + 1 := by exact_mod_cast m2
    linarith

theorem abs_E_sub_le_three (y₁ y₂ : ℝ) (h₁ : 2 ≤ y₁) (h₂ : 2 ≤ y₂) (hd : |y₁ - y₂| ≤ 1) :
    |E y₁ - E y₂| ≤ 3 := by
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  have hpi : |piR y₁ - piR y₂| ≤ 1 := by
    rcases le_total y₂ y₁ with h | h
    · obtain ⟨a1, a2⟩ := chain_piR_diff (by linarith) h (by linarith)
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨a1, a2⟩ := chain_piR_diff (y₁ := y₂) (y₂ := y₁) (by linarith) h (by linarith)
      rw [abs_le]; constructor <;> linarith
  have hli : li y₁ - li y₂ = ∫ t in y₂..y₁, 1 / Real.log t := by
    unfold li
    exact intervalIntegral.integral_interval_sub_left (chain_ii_inv_log (by norm_num)
      (by linarith)) (chain_ii_inv_log (by norm_num) (by linarith))
  have hl2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  have hlib : |li y₁ - li y₂| ≤ 1 / Real.log 2 * |y₁ - y₂| := by
    rw [hli, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx2 : 2 < x := by
      rcases Set.mem_uIoc.mp hx with hx | hx <;> linarith [hx.1]
    have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2.le
    rw [Real.norm_eq_abs, abs_of_pos (by have := Real.log_pos (by linarith : (1:ℝ) < x); positivity)]
    exact one_div_le_one_div_of_le hl2' hlx
  have h12 : 1 / Real.log 2 < 2 := by
    rw [div_lt_iff₀ hl2']
    linarith
  have hlib' : |li y₁ - li y₂| ≤ 2 := by
    have : 1 / Real.log 2 * |y₁ - y₂| ≤ 1 / Real.log 2 * 1 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    linarith
  have : E y₁ - E y₂ = (piR y₁ - piR y₂) - (li y₁ - li y₂) := by unfold E; ring
  rw [this]
  calc _ ≤ |piR y₁ - piR y₂| + |li y₁ - li y₂| := abs_sub _ _
    _ ≤ 3 := by linarith

end Erdos879
