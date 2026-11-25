import Erdos879.Analytic.Localised

open MeasureTheory

namespace Erdos879

theorem gap_theta_eq (p q : ℕ) (hgap : ∀ m : ℕ, p < m → m < q → ¬ m.Prime) (y z : ℝ)
    (hp : (p : ℝ) ≤ y) (hyz : y ≤ z) (hzq : z < q) :
    Chebyshev.theta z = Chebyshev.theta y := by
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg p) hp
  have hz0 : 0 ≤ z := le_trans hy0 hyz
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  congr 1
  ext l
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨hlz, hl⟩
    refine ⟨?_, hl⟩
    by_contra h
    push Not at h
    have h1 : y < l := Nat.lt_of_floor_lt h
    have h2 : (l : ℝ) ≤ z := (Nat.le_floor_iff hz0).1 hlz
    have h3 : p < l := by exact_mod_cast lt_of_le_of_lt hp h1
    have h4 : l < q := by exact_mod_cast lt_of_le_of_lt h2 hzq
    exact hgap l h3 h4 hl
  · rintro ⟨hly, hl⟩
    exact ⟨le_trans hly (Nat.floor_le_floor hyz), hl⟩

theorem gap_lower (p q : ℕ) (hgap : ∀ m : ℕ, p < m → m < q → ¬ m.Prime)
    (x g δ η mm : ℝ) (hx : x = p) (hx2 : 2 ≤ x) (hqg : (q : ℝ) = x + g) (hg0 : 0 < g)
    (hgx : g ≤ x) (hδ : δ = g / (2 * x)) (hm0 : 0 < mm) (hmg : mm ≤ g / 4)
    (hmx : mm ≤ x * η) :
    mm * (g ^ 2 / 4) ≤ ∫ y in x..(x * (1 + η)),
      (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set f : ℝ → ℝ := fun y =>
    (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2 with hf
  set b := x * (1 + η) with hbdef
  have hxb : x ≤ b := by rw [hbdef]; nlinarith
  have hθm : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
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
  have hintb : IntervalIntegrable f volume x b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hxb).2 hint
  have hxm : x ≤ x + mm := by linarith
  have hmb : x + mm ≤ b := by rw [hbdef]; nlinarith
  have hpt : ∀ y ∈ Set.Icc x (x + mm), g ^ 2 / 4 ≤ f y := by
    intro y hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hδy : δ * x ≤ δ * y := mul_le_mul_of_nonneg_left hy.1 hδ0.le
    have hz : y + δ * y < q := by
      have h1 : δ * y ≤ δ * (x + g / 4) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.2]) hδ0.le
      have h2 : δ * (x + g / 4) = g / 2 + g ^ 2 / (8 * x) := by rw [hδ]; field_simp; ring
      have h3 : g ^ 2 / (8 * x) ≤ g / 8 := by rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith [hy.2]
    have hth := gap_theta_eq p q hgap y (y + δ * y) (by rw [← hx]; exact hy.1)
      (le_add_of_nonneg_right (mul_nonneg hδ0.le hy0)) hz
    have hδx : δ * x = g / 2 := by rw [hδ]; field_simp
    have h5 : (g / 2) ^ 2 ≤ (δ * y) ^ 2 := pow_le_pow_left₀ (by positivity) (hδx ▸ hδy) 2
    have e : f y = (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2 := rfl
    rw [e, hth]
    have e2 : (Chebyshev.theta y - Chebyshev.theta y - δ * y) ^ 2 = (δ * y) ^ 2 := by ring
    rw [e2]
    linarith
  have hintm : IntervalIntegrable f volume x (x + mm) :=
    hintb.mono_set (by
      rw [Set.uIcc_of_le hxb, Set.uIcc_of_le hxm]
      exact Set.Icc_subset_Icc le_rfl hmb)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc x b)] f :=
    Filter.Eventually.of_forall fun y => by rw [hf]; positivity
  have h1 : ∫ y in x..(x + mm), f y ≤ ∫ y in x..b, f y :=
    intervalIntegral.integral_mono_interval le_rfl hxm hmb hnn hintb
  have h2 : ∫ y in x..(x + mm), (g ^ 2 / 4) ≤ ∫ y in x..(x + mm), f y :=
    intervalIntegral.integral_mono_on hxm intervalIntegrable_const hintm hpt
  have h3 : ∫ y in x..(x + mm), (g ^ 2 / 4) = mm * (g ^ 2 / 4) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h4 : ∫ y in x..b, f y = ∫ y in x..(x * (1 + η)),
      (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2 := rfl
  linarith

theorem gap_final (θ ε K x g : ℝ) (hθ : θ ≤ 1 / 2) (hε : 0 < ε) (hK1 : 1 ≤ K) (hx1 : 1 ≤ x)
    (hg0 : 0 < g)
    (hmain : min (g / 4) (x * x ^ (-θ)) * (g ^ 2 / 4) ≤ K * (g / (2 * x)) * x ^ (-θ) * x ^ (2 + ε)) :
    g ≤ (Real.sqrt (8 * K) + 2 * K) * x ^ ((1 - θ) / 2 + ε) := by
  have hx0 : 0 < x := by linarith
  set mm := min (g / 4) (x * x ^ (-θ)) with hmdef
  set R := x ^ (1 - θ + ε) with hRdef
  have hR : x ^ (-θ) * x ^ (2 + ε) = x * R := by
    rw [hRdef, ← Real.rpow_add hx0, show -θ + (2 + ε) = 1 + (1 - θ + ε) by ring,
      Real.rpow_add hx0, Real.rpow_one]
  have hxη : x * x ^ (-θ) = x ^ (1 - θ) := by
    rw [show (1 - θ) = 1 + -θ by ring, Real.rpow_add hx0, Real.rpow_one]
  have hRs : R = x ^ (1 - θ) * x ^ ε := by
    rw [hRdef, ← Real.rpow_add hx0]
  have hmain' : mm * (g ^ 2 / 4) ≤ K * g * R / 2 := by
    have e : K * (g / (2 * x)) * x ^ (-θ) * x ^ (2 + ε) = K * g * R / 2 := by
      rw [show K * (g / (2 * x)) * x ^ (-θ) * x ^ (2 + ε)
          = K * (g / (2 * x)) * (x ^ (-θ) * x ^ (2 + ε)) by ring, hR]
      field_simp
    linarith
  have hkey : mm * g ≤ 2 * K * R := by
    have e1 : mm * (g ^ 2 / 4) = g / 4 * (mm * g) := by ring
    have e2 : K * g * R / 2 = g / 4 * (2 * K * R) := by ring
    rw [e1, e2] at hmain'
    exact le_of_mul_le_mul_left hmain' (by positivity)
  have hT0 : 0 ≤ x ^ ((1 - θ) / 2 + ε) := Real.rpow_nonneg hx0.le _
  have hs8 : 0 ≤ Real.sqrt (8 * K) := Real.sqrt_nonneg _
  have e : (Real.sqrt (8 * K) + 2 * K) * x ^ ((1 - θ) / 2 + ε)
      = Real.sqrt (8 * K) * x ^ ((1 - θ) / 2 + ε) + 2 * K * x ^ ((1 - θ) / 2 + ε) := by ring
  rw [e]
  rcases le_or_gt (g / 4) (x * x ^ (-θ)) with hA | hB
  · have hm : mm = g / 4 := min_eq_left hA
    rw [hm] at hkey
    have hg2 : g ^ 2 ≤ 8 * K * R := by nlinarith
    have hR0 : 0 ≤ R := Real.rpow_nonneg hx0.le _
    have hsq : g ≤ Real.sqrt (8 * K) * Real.sqrt R := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_sq hg0.le]
      exact Real.sqrt_le_sqrt hg2
    have hsR : Real.sqrt R ≤ x ^ ((1 - θ) / 2 + ε) := by
      rw [Real.sqrt_eq_rpow, hRdef, ← Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h4 : Real.sqrt (8 * K) * Real.sqrt R ≤ Real.sqrt (8 * K) * x ^ ((1 - θ) / 2 + ε) :=
      mul_le_mul_of_nonneg_left hsR hs8
    have h5 : 0 ≤ 2 * K * x ^ ((1 - θ) / 2 + ε) := by positivity
    linarith
  · have hm : mm = x * x ^ (-θ) := min_eq_right hB.le
    rw [hm, hxη, hRs] at hkey
    have hx1θ : 0 < x ^ (1 - θ) := Real.rpow_pos_of_pos hx0 _
    have hgK : g ≤ 2 * K * x ^ ε := by
      have e : 2 * K * (x ^ (1 - θ) * x ^ ε) = x ^ (1 - θ) * (2 * K * x ^ ε) := by ring
      rw [e] at hkey
      exact le_of_mul_le_mul_left hkey hx1θ
    have hε' : x ^ ε ≤ x ^ ((1 - θ) / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h4 : 2 * K * x ^ ε ≤ 2 * K * x ^ ((1 - θ) / 2 + ε) :=
      mul_le_mul_of_nonneg_left hε' (by positivity)
    have h5 : 0 ≤ Real.sqrt (8 * K) * x ^ ((1 - θ) / 2 + ε) := by positivity
    linarith

theorem gap_bound_of_LS (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hLS : HypothesisLSAt θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (∀ m : ℕ, p < m → m < q → ¬ m.Prime) →
      (q : ℝ) - p ≤ C * (p : ℝ) ^ ((1 - θ) / 2 + ε) := by
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := hLS ε hε
  refine ⟨Real.sqrt (8 * max C₀ 1) + 2 * max C₀ 1, ?_⟩
  intro p q hp hq hpq hgap
  obtain ⟨r, hr, hpr, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hqr : q ≤ r := by
    by_contra h
    push Not at h
    exact hgap r hpr h hr
  have hx2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hqx : (q : ℝ) ≤ 2 * p := by exact_mod_cast hqr.trans hr2
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hx0 : (0 : ℝ) < p := by linarith
  have hx1 : (1 : ℝ) ≤ p := by linarith
  have hg0 : (0 : ℝ) < q - p := by linarith
  have hgx : (q : ℝ) - p ≤ p := by linarith
  have hη0 : 0 < (p : ℝ) ^ (-θ) := Real.rpow_pos_of_pos hx0 _
  have hη1 : (p : ℝ) ^ (-θ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hδ0 : 0 < ((q : ℝ) - p) / (2 * p) := by positivity
  have hδ1 : ((q : ℝ) - p) / (2 * p) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hI := hC₀ p hx2 ((p : ℝ) ^ (-θ)) le_rfl hη1 _ hδ0 hδ1
  have hlow := gap_lower p q hgap p ((q : ℝ) - p) (((q : ℝ) - p) / (2 * p)) ((p : ℝ) ^ (-θ))
    (min (((q : ℝ) - p) / 4) (p * (p : ℝ) ^ (-θ))) rfl hx2 (by ring) hg0 hgx rfl
    (lt_min (by positivity) (by positivity)) (min_le_left _ _) (min_le_right _ _)
  have hCK : C₀ * (((q : ℝ) - p) / (2 * p)) * (p : ℝ) ^ (-θ) * (p : ℝ) ^ (2 + ε)
      ≤ max C₀ 1 * (((q : ℝ) - p) / (2 * p)) * (p : ℝ) ^ (-θ) * (p : ℝ) ^ (2 + ε) := by
    have hxe : 0 ≤ (p : ℝ) ^ (2 + ε) := Real.rpow_nonneg hx0.le _
    have h0 : 0 ≤ ((q : ℝ) - p) / (2 * p) * (p : ℝ) ^ (-θ) * (p : ℝ) ^ (2 + ε) := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_left C₀ 1) h0
    linarith
  exact gap_final θ ε (max C₀ 1) p ((q : ℝ) - p) hθ hε (le_max_right _ _) hx1 hg0
    (by linarith)

end Erdos879
