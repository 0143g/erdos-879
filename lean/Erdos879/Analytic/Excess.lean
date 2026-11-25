import Erdos879.Analytic.Defs

open Finset MeasureTheory

namespace Erdos879

private lemma primeCounting_eq_card (m : ℕ) :
    Nat.primeCounting m = ((range (m + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

private lemma card_filter_prime_gt (a b : ℕ) (hab : a ≤ b) :
    ((range (b + 1)).filter (fun q : ℕ => q.Prime ∧ a < q)).card + Nat.primeCounting a =
      Nat.primeCounting b := by
  rw [primeCounting_eq_card, primeCounting_eq_card]
  have h1 : (range (b + 1)).filter (fun q : ℕ => q.Prime ∧ a < q) =
      ((range (b + 1)).filter Nat.Prime).filter (fun q => a < q) := by
    rw [filter_filter]
  have h2 : (range (a + 1)).filter Nat.Prime =
      ((range (b + 1)).filter Nat.Prime).filter (fun q => ¬ a < q) := by
    ext q
    simp only [mem_filter, mem_range, not_lt]
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨⟨by omega, hp⟩, by omega⟩
    · rintro ⟨⟨h, hp⟩, h'⟩
      exact ⟨by omega, hp⟩
  rw [h1, h2, card_filter_add_card_filter_not]

theorem primesBetween_eq (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    (primesBetween u v : ℝ) = piR v - piR u := by
  have hfl : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_le_floor huv
  have h := card_filter_prime_gt ⌊u⌋₊ ⌊v⌋₊ hfl
  have he : primesBetween u v = ((range (⌊v⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧ ⌊u⌋₊ < q)).card := by
    unfold primesBetween
    congr 1
    apply filter_congr
    intro q _
    rw [Nat.floor_lt hu]
  unfold piR
  rw [he, ← h]
  push_cast
  ring

theorem A_le_piR (n : ℕ) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    (A n u v : ℝ) ≤ piR (n / u) - piR (n / v) + 1 := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hsub : (smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v) ⊆
      insert ⌊(n : ℝ) / v⌋₊ ((range (⌊(n : ℝ) / u⌋₊ + 1)).filter
        (fun q : ℕ => q.Prime ∧ (n : ℝ) / v < (q : ℝ))) := by
    intro p hp
    simp only [smallPrimes, mem_filter, mem_range] at hp
    obtain ⟨⟨_, hpp, _⟩, h1, h2⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlt : (p : ℝ) < n / u := by
      rw [lt_div_iff₀ hu]
      rw [lt_div_iff₀ hp0] at h1
      linarith
    have hge : (n : ℝ) / v ≤ p := by
      rw [div_le_iff₀ hv]
      rw [div_le_iff₀ hp0] at h2
      linarith
    rw [mem_insert, mem_filter, mem_range]
    rcases hge.lt_or_eq with h | h
    · right
      refine ⟨?_, hpp, h⟩
      have : p ≤ ⌊(n : ℝ) / u⌋₊ := Nat.le_floor hlt.le
      omega
    · left
      rw [h, Nat.floor_natCast]
  have hc := card_le_card hsub
  have hc2 := (card_insert_le _ _).trans' hc
  have hpb := primesBetween_eq ((n : ℝ) / v) ((n : ℝ) / u) (by positivity)
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hu huv)
  unfold primesBetween at hpb
  unfold A
  have : (((smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v)).card : ℝ) ≤
      (((range (⌊(n : ℝ) / u⌋₊ + 1)).filter
        (fun q : ℕ => q.Prime ∧ (n : ℝ) / v < (q : ℝ))).card : ℝ) + 1 := by
    exact_mod_cast hc2
  linarith

theorem W_le_piR (n : ℕ) (u : ℝ) (hu : 0 < u) : (W n u : ℝ) ≤ piR (n / u) := by
  have hmem : Nat.primeCounting ⌊(n : ℝ) / u⌋₊ ∈
      {w : ℕ | ∀ v : ℝ, u ≤ v → v ≤ 4 * u → A n u v ≤ primesBetween u v + w} := by
    intro v _ _
    have hsub : (smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v) ⊆
        (range (⌊(n : ℝ) / u⌋₊ + 1)).filter Nat.Prime := by
      intro p hp
      simp only [smallPrimes, mem_filter, mem_range] at hp
      obtain ⟨⟨_, hpp, _⟩, h1, _⟩ := hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlt : (p : ℝ) < n / u := by
        rw [lt_div_iff₀ hu]
        rw [lt_div_iff₀ hp0] at h1
        linarith
      have : p ≤ ⌊(n : ℝ) / u⌋₊ := Nat.le_floor hlt.le
      rw [mem_filter, mem_range]
      exact ⟨by omega, hpp⟩
    have := card_le_card hsub
    unfold A
    rw [primeCounting_eq_card]
    omega
  have := Nat.sInf_le hmem
  unfold W piR
  exact_mod_cast this

private lemma continuousOn_inv_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := by
  apply continuousOn_const.div (Real.continuousOn_log.mono ?_)
  · intro t ht
    exact ne_of_gt (Real.log_pos ht)
  · intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_trans one_pos ht)

private lemma hasDerivAt_li {y : ℝ} (hy : 1 < y) : HasDerivAt li (1 / Real.log y) y := by
  have hsub : Set.uIcc 2 y ⊆ Set.Ioi 1 := by
    intro t ht
    rcases Set.mem_uIcc.1 ht with h | h
    · exact lt_of_lt_of_le (by norm_num) h.1
    · exact lt_of_lt_of_le hy h.1
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuousOn_inv_log.mono hsub).intervalIntegrable
  · exact continuousOn_inv_log.stronglyMeasurableAtFilter isOpen_Ioi y hy
  · exact continuousOn_inv_log.continuousAt (isOpen_Ioi.mem_nhds hy)

private lemma exp_two_lt : Real.exp 2 < 7.5 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

private lemma log_four_lt_two : Real.log 4 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

private lemma key_ineq (X t m : ℝ) (hX : 0 < X) (ht : X ≤ t) (hmt : m * t = X * X) (hm : 2 ≤ Real.log m) :
    m / Real.log m ≤ X / Real.log t := by
  have ht0 : 0 < t := lt_of_lt_of_le hX ht
  set z := t / X with hz
  have hz1 : 1 ≤ z := by rw [hz, le_div_iff₀ hX]; linarith
  have hz0 : 0 < z := by linarith
  have htz : t = X * z := by rw [hz]; field_simp
  have hmz : m = X / z := by
    rw [htz] at hmt
    field_simp
    nlinarith
  have hlt : Real.log t = Real.log X + Real.log z := by
    rw [htz, Real.log_mul hX.ne' hz0.ne']
  have hlm : Real.log m = Real.log X - Real.log z := by
    rw [hmz, Real.log_div hX.ne' hz0.ne']
  have hlz := Real.log_le_sub_one_of_pos hz0
  have hlz0 : 0 ≤ Real.log z := Real.log_nonneg hz1
  have hLt : 0 < Real.log t := by linarith
  have hm0 : 0 < m := by rw [hmz]; positivity
  have hmzX : m * z = X := by rw [hmz]; field_simp
  rw [div_le_div_iff₀ (by linarith) hLt]
  have h1 : Real.log m + 2 * Real.log z ≤ z * Real.log m := by nlinarith
  have h2 : Real.log t = Real.log m + 2 * Real.log z := by rw [hlt, hlm]; ring
  rw [h2, ← hmzX]
  have := mul_le_mul_of_nonneg_left h1 hm0.le
  linarith


theorem drift (n : ℕ) (hn : 1 ≤ n) (u s : ℝ) (hu : Real.sqrt n ≤ u) (hun : 30 * u ≤ n)
    (hs0 : 0 ≤ s) (hs : s ≤ Real.log 4) :
    s / Real.log n * (u - Real.sqrt n + Real.sqrt n * s / 2) ≤
      (li (u * Real.exp s) - li u) - (li (n / u) - li (n / (u * Real.exp s))) := by
  set X := Real.sqrt n with hXdef
  set L := Real.log n with hLdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX0 : 0 < X := Real.sqrt_pos.2 (by linarith)
  have hXX : X * X = n := Real.mul_self_sqrt (by linarith)
  have hX30 : 30 ≤ X := by nlinarith
  have hu30 : 30 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set g : ℝ → ℝ := fun σ => (li (u * Real.exp σ) - li u) - (li (n / u) - li (n / (u * Real.exp σ)))
    - σ / L * (u - X + X * σ / 2) with hg
  set g' : ℝ → ℝ := fun σ => 1 / Real.log (u * Real.exp σ) * (u * Real.exp σ)
    - (0 - 1 / Real.log (n / (u * Real.exp σ)) * (-(n / (u * Real.exp σ))))
    - (u - X + X * σ) / L with hg'
  have hderiv : ∀ σ ∈ Set.Icc 0 (Real.log 4), HasDerivAt g (g' σ) σ := by
    intro σ hσ
    have he1 : 1 ≤ Real.exp σ := Real.one_le_exp hσ.1
    have he4 : Real.exp σ ≤ 4 := by
      calc Real.exp σ ≤ Real.exp (Real.log 4) := Real.exp_le_exp.2 hσ.2
        _ = 4 := Real.exp_log (by norm_num)
    have ht1 : 1 < u * Real.exp σ := by nlinarith
    have ht0 : 0 < u * Real.exp σ := by linarith
    have hm1 : 1 < (n : ℝ) / (u * Real.exp σ) := by
      rw [lt_div_iff₀ ht0]; nlinarith
    have h1 : HasDerivAt (fun σ => li (u * Real.exp σ))
        (1 / Real.log (u * Real.exp σ) * (u * Real.exp σ)) σ := by
      have := (hasDerivAt_li ht1).comp σ ((Real.hasDerivAt_exp σ).const_mul u)
      exact this
    have hq : HasDerivAt (fun σ => (n : ℝ) / (u * Real.exp σ)) (-((n : ℝ) / (u * Real.exp σ))) σ := by
      have := (hasDerivAt_const σ (n : ℝ)).div ((Real.hasDerivAt_exp σ).const_mul u) ht0.ne'
      refine this.congr_deriv ?_
      have hne := ht0.ne'
      field_simp
      ring
    have h2 : HasDerivAt (fun σ => li ((n : ℝ) / (u * Real.exp σ)))
        (1 / Real.log ((n : ℝ) / (u * Real.exp σ)) * (-((n : ℝ) / (u * Real.exp σ)))) σ := by
      have := (hasDerivAt_li hm1).comp σ hq
      exact this
    have h3 : HasDerivAt (fun σ => σ / L * (u - X + X * σ / 2)) ((u - X + X * σ) / L) σ := by
      have h := ((hasDerivAt_id' σ).mul_const ((u - X) / L)).add
        ((hasDerivAt_pow 2 σ).mul_const (X / (2 * L)))
      have hf : (fun σ => σ / L * (u - X + X * σ / 2)) =
          (fun x => x * ((u - X) / L) + x ^ 2 * (X / (2 * L))) := by
        funext x
        field_simp
      rw [hf]
      refine h.congr_deriv ?_
      norm_num
      field_simp
    exact ((h1.sub_const (li u)).sub ((hasDerivAt_const σ (li (n / u))).sub h2)).sub h3
  have hpos : ∀ σ ∈ Set.Icc 0 (Real.log 4), 0 ≤ g' σ := by
    intro σ hσ
    have he1 : 1 ≤ Real.exp σ := Real.one_le_exp hσ.1
    have he4 : Real.exp σ ≤ 4 := by
      calc Real.exp σ ≤ Real.exp (Real.log 4) := Real.exp_le_exp.2 hσ.2
        _ = 4 := Real.exp_log (by norm_num)
    have hes : σ + 1 ≤ Real.exp σ := Real.add_one_le_exp σ
    set t := u * Real.exp σ with ht
    set m := (n : ℝ) / t with hm
    have ht0 : 0 < t := by positivity
    have htX : X ≤ t := by nlinarith
    have htn : t ≤ n := by nlinarith
    have hmt : m * t = X * X := by rw [hm, hXX]; field_simp
    have hm75 : 7.5 ≤ m := by rw [hm, le_div_iff₀ ht0]; nlinarith
    have hlm : 2 ≤ Real.log m := by
      have := exp_two_lt
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith
    have hlt0 : 0 < Real.log t := Real.log_pos (by linarith)
    have hltL : Real.log t ≤ L := Real.log_le_log ht0 htn
    have hk := key_ineq X t m hX0 htX hmt hlm
    have hA : g' σ = t / Real.log t - m / Real.log m - (u - X + X * σ) / L := by
      simp only [hg']
      ring
    rw [hA]
    have hB : (t - X) / L ≤ (t - X) / Real.log t :=
      div_le_div_of_nonneg_left (by linarith) hlt0 hltL
    have hC : (u - X + X * σ) / L ≤ (t - X) / L := by
      apply div_le_div_of_nonneg_right _ hL.le
      nlinarith
    have hD : t / Real.log t - X / Real.log t = (t - X) / Real.log t := by ring
    linarith
  have hmono : MonotoneOn g (Set.Icc 0 (Real.log 4)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (Real.log 4)) (f' := g')
    · intro x hx
      exact (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hpos x (interior_subset hx)
  have h0 : g 0 = 0 := by simp [hg]
  have hle := hmono ⟨le_refl 0, hl4⟩ ⟨hs0, hs⟩ hs0
  rw [h0] at hle
  simp only [hg] at hle
  linarith


private lemma W_le_of_forall (n : ℕ) (u B : ℝ) (hB : 0 ≤ B)
    (h : ∀ v : ℝ, u ≤ v → v ≤ 4 * u → (A n u v : ℝ) ≤ primesBetween u v + B) :
    (W n u : ℝ) ≤ B := by
  have hmem : ⌊B⌋₊ ∈ {w : ℕ | ∀ v : ℝ, u ≤ v → v ≤ 4 * u → A n u v ≤ primesBetween u v + w} := by
    intro v h1 h2
    have hv := h v h1 h2
    by_cases hle : A n u v ≤ primesBetween u v
    · omega
    · have hlt : primesBetween u v ≤ A n u v := (not_le.1 hle).le
      have : A n u v - primesBetween u v ≤ ⌊B⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub hlt]
        linarith
      omega
  exact (Nat.cast_le.2 (Nat.sInf_le hmem)).trans (Nat.floor_le hB)

private lemma A_sub_le (n : ℕ) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    (A n u v : ℝ) ≤ primesBetween u v + 1 - ((li v - li u) - (li (n / u) - li (n / v)))
      + (E (n / u) - E (n / v)) - (E v - E u) := by
  have h1 := A_le_piR n u v hu huv
  have h2 := primesBetween_eq u v hu.le huv
  unfold E
  linarith

private lemma A_mem_bounds (n : ℕ) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (p : ℕ)
    (hp : p ∈ (smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v)) :
    (n : ℝ) / v ≤ p ∧ (p : ℝ) < n / u := by
  simp only [smallPrimes, mem_filter, mem_range] at hp
  obtain ⟨⟨_, hpp, _⟩, h1, h2⟩ := hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  constructor
  · rw [div_le_iff₀ hv]
    rw [div_le_iff₀ hp0] at h2
    linarith
  · rw [lt_div_iff₀ hu]
    rw [lt_div_iff₀ hp0] at h1
    linarith

private lemma A_le_one (n : ℕ) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (h : (n : ℝ) / u - n / v ≤ 1) :
    A n u v ≤ 1 := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  unfold A
  rw [card_le_one]
  intro a ha b hb
  have ha' := A_mem_bounds n u v hu hv a ha
  have hb' := A_mem_bounds n u v hu hv b hb
  by_contra hab
  rcases Nat.lt_or_gt_of_ne hab with h' | h'
  · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h'
    linarith
  · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h'
    linarith

private lemma rr_pos (i : ℕ) : 0 < rr i := by
  unfold rr
  positivity

private lemma rr_succ (i : ℕ) : rr (i + 1) = rr i / 2 := by
  unfold rr
  rw [pow_succ]
  field_simp

theorem excess (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : Real.sqrt n ≤ u) (hun : 30 * u ≤ n) (N : ℕ)
    (hN : 2 * u ≤ 2 ^ N) (Mp Mm : ℕ → ℝ)
    (hMp : ∀ i ≤ N, ∀ s : ℝ, 0 ≤ s → s ≤ rr i → |E (u * Real.exp s) - E u| ≤ Mp i)
    (hMm : ∀ i ≤ N, ∀ s : ℝ, 0 ≤ s → s ≤ rr i →
      |E (n / u * Real.exp (-s)) - E (n / u)| ≤ Mm i) :
    (W n u : ℝ) ≤ 2 + ∑ i ∈ range (N + 1), (Mp i + Mm i) ^ 2 / (4 * bfun n (rr i) u) := by
  set X := Real.sqrt n with hXdef
  set L := Real.log n with hLdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX0 : 0 < X := Real.sqrt_pos.2 (by linarith)
  have hXX : X * X = n := Real.mul_self_sqrt (by linarith)
  have hX30 : 30 ≤ X := by nlinarith
  have hu0 : 0 < u := by linarith
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hb : ∀ i, 0 < bfun n (rr i) u := by
    intro i
    have hr := rr_pos i
    unfold bfun
    apply mul_pos (div_pos hr (by positivity))
    nlinarith
  set S := ∑ i ∈ range (N + 1), (Mp i + Mm i) ^ 2 / (4 * bfun n (rr i) u) with hSdef
  have hS : 0 ≤ S := sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (by linarith [hb i]))
  apply W_le_of_forall n u _ (by linarith)
  intro v huv hv4
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  have hvu : 0 < v / u := div_pos hv0 hu0
  set s := Real.log (v / u) with hsdef
  have hes : Real.exp s = v / u := Real.exp_log hvu
  have hv : u * Real.exp s = v := by rw [hes]; field_simp
  have hs0 : 0 ≤ s := Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
  have hs4 : s ≤ Real.log 4 := Real.log_le_log hvu (by rw [div_le_iff₀ hu0]; linarith)
  have hnv : (n : ℝ) / u * Real.exp (-s) = n / v := by
    rw [Real.exp_neg, hes]
    field_simp
  have hpb : (0 : ℝ) ≤ primesBetween u v := Nat.cast_nonneg _
  by_cases hsN : s ≤ rr N
  · have hnu : (n : ℝ) / u ≤ u := by rw [div_le_iff₀ hu0]; nlinarith
    have hnu0 : (0 : ℝ) ≤ n / u := by positivity
    have h1 : 1 - Real.exp (-s) ≤ s := by linarith [Real.add_one_le_exp (-s)]
    have huN : u * rr N ≤ 1 := by
      unfold rr
      rw [mul_div_assoc', div_le_one (by positivity)]
      linarith
    have hdiff : (n : ℝ) / u - n / v ≤ 1 := by
      rw [← hnv]
      have : (n : ℝ) / u - n / u * Real.exp (-s) = n / u * (1 - Real.exp (-s)) := by ring
      rw [this]
      calc (n : ℝ) / u * (1 - Real.exp (-s)) ≤ n / u * s := mul_le_mul_of_nonneg_left h1 hnu0
        _ ≤ u * s := mul_le_mul_of_nonneg_right hnu hs0
        _ ≤ u * rr N := mul_le_mul_of_nonneg_left hsN hu0.le
        _ ≤ 1 := huN
    have hA1 : (A n u v : ℝ) ≤ 1 := by exact_mod_cast A_le_one n u v hu0 huv hdiff
    linarith
  · push Not at hsN
    have hex : ∃ i, rr i < s := ⟨N, hsN⟩
    have hi : rr (Nat.find hex) < s := Nat.find_spec hex
    have hiN : Nat.find hex ≤ N := Nat.find_min' hex hsN
    have hi0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h] at hi
      unfold rr at hi
      norm_num at hi
      linarith [log_four_lt_two]
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hjs : s ≤ rr j := by
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      push Not at this
      exact this
    have hjN : j ≤ N := by omega
    have hr2 : rr j / 2 < s := by rw [← rr_succ, ← hj]; exact hi
    have hMpj := hMp j hjN s hs0 hjs
    have hMmj := hMm j hjN s hs0 hjs
    rw [hv] at hMpj
    rw [hnv] at hMmj
    have hd : s / L * (u - X + X * s / 2) ≤ (li v - li u) - (li (n / u) - li (n / v)) := by
      have h := drift n hn u s hu hun hs0 hs4
      rw [hv] at h
      exact h
    have hrj := rr_pos j
    have hbl : bfun n (rr j) u ≤ s / L * (u - X + X * s / 2) := by
      unfold bfun
      have e1 : rr j / (2 * Real.log n) * (u - X + X * rr j / 4) =
          (rr j / 2 * (u - X + X * (rr j / 2) / 2)) / L := by
        rw [hLdef]; field_simp; ring
      have e2 : s / L * (u - X + X * s / 2) = (s * (u - X + X * s / 2)) / L := by ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ hL.le
      nlinarith [mul_nonneg (sub_nonneg.2 hr2.le) (sub_nonneg.2 hu),
        mul_nonneg (mul_nonneg (sub_nonneg.2 hr2.le) (by linarith : 0 ≤ s + rr j / 2)) hX0.le]
    have hAs := A_sub_le n u v hu0 huv
    have hbj := hb j
    have hM : (Mp j + Mm j) - bfun n (rr j) u ≤ (Mp j + Mm j) ^ 2 / (4 * bfun n (rr j) u) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (Mp j + Mm j - 2 * bfun n (rr j) u)]
    have hterm : (Mp j + Mm j) ^ 2 / (4 * bfun n (rr j) u) ≤ S := by
      rw [hSdef]
      exact single_le_sum (f := fun i => (Mp i + Mm i) ^ 2 / (4 * bfun n (rr i) u))
        (fun i _ => div_nonneg (sq_nonneg _) (by linarith [hb i])) (mem_range.2 (by omega))
    have hp1 := (abs_le.1 hMpj).1
    have hm1 := (abs_le.1 hMmj).1
    linarith

theorem W_le_of_abs_E_le (n : ℕ) (u : ℝ) (hn : 3600 ≤ n) (hu : Real.sqrt n ≤ u)
    (hu2 : u ≤ 2 * Real.sqrt n) (B : ℝ)
    (hB : ∀ y : ℝ, Real.sqrt n / 8 ≤ y → y ≤ 8 * Real.sqrt n → |E y| ≤ B) :
    (W n u : ℝ) ≤ 2 + 4 * B := by
  set X := Real.sqrt n with hXdef
  set L := Real.log n with hLdef
  have hn1 : (3600 : ℝ) ≤ n := by exact_mod_cast hn
  have hX0 : 0 < X := Real.sqrt_pos.2 (by linarith)
  have hXX : X * X = n := Real.mul_self_sqrt (by linarith)
  have hX60 : 60 ≤ X := by nlinarith
  have hu0 : 0 < u := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hun : 30 * u ≤ n := by nlinarith
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB X (by linarith) (by linarith))
  have hfin : (W n u : ℝ) ≤ 1 + 4 * B := by
    apply W_le_of_forall n u _ (by linarith)
    intro v huv hv4
    have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
    have hvu : 0 < v / u := div_pos hv0 hu0
    set s := Real.log (v / u) with hsdef
    have hes : Real.exp s = v / u := Real.exp_log hvu
    have hv : u * Real.exp s = v := by rw [hes]; field_simp
    have hs0 : 0 ≤ s := Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
    have hs4 : s ≤ Real.log 4 := Real.log_le_log hvu (by rw [div_le_iff₀ hu0]; linarith)
    have hd : s / L * (u - X + X * s / 2) ≤ (li v - li u) - (li (n / u) - li (n / v)) := by
      have h := drift n (by omega) u s hu hun hs0 hs4
      rw [hv] at h
      exact h
    have hd0 : 0 ≤ s / L * (u - X + X * s / 2) :=
      mul_nonneg (div_nonneg hs0 hL.le) (by nlinarith)
    have hAs := A_sub_le n u v hu0 huv
    have e1 := abs_le.1 (hB (n / u) (by rw [le_div_iff₀ hu0]; nlinarith)
      (by rw [div_le_iff₀ hu0]; nlinarith))
    have e2 := abs_le.1 (hB (n / v) (by rw [le_div_iff₀ hv0]; nlinarith)
      (by rw [div_le_iff₀ hv0]; nlinarith))
    have e3 := abs_le.1 (hB v (by linarith) (by linarith))
    have e4 := abs_le.1 (hB u (by linarith) (by linarith))
    linarith
  linarith

end Erdos879
