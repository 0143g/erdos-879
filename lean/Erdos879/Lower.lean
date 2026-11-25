import Erdos879.Defs

open Finset MeasureTheory

namespace Erdos879

namespace LowerAux

def mv (S : Finset ℕ) (p : ℕ) : ℕ := ∑ a ∈ S.filter (fun a => 2 ≤ a ∧ a.minFac = p), a

def cv (S : Finset ℕ) (p : ℕ) : ℕ := mv S p / p

noncomputable def sg (n : ℕ) (S : Finset ℕ) (p : ℕ) : ℝ :=
  if n < cv S p * cv S p then (cv S p : ℝ) else Real.sqrt n

noncomputable def Ks (n : ℕ) (S : Finset ℕ) (u : ℝ) : Finset ℕ :=
  (smallPrimes n).filter (fun p => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ 4 * u ∧ sg n S p ≤ u)

variable {n : ℕ} {S : Finset ℕ}

theorem mem_smallPrimes {p : ℕ} : p ∈ smallPrimes n ↔ p.Prime ∧ p * p ≤ n := by
  unfold smallPrimes
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨hp, h⟩
    refine ⟨?_, hp, h⟩
    have := hp.two_le
    nlinarith

theorem card_filter_le_one (hS : Admissible n S) (p : ℕ) :
    (S.filter (fun a => 2 ≤ a ∧ a.minFac = p)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [mem_filter] at ha hb
  by_contra hab
  have hc := hS.2 a ha.1 b hb.1 hab
  have hpa : p ∣ a := ha.2.2 ▸ Nat.minFac_dvd a
  have hpb : p ∣ b := hb.2.2 ▸ Nat.minFac_dvd b
  have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hc hpa hpb
  have : (a.minFac).Prime := Nat.minFac_prime (by omega)
  rw [ha.2.2, hp1] at this
  exact Nat.not_prime_one this

theorem mv_cases (hS : Admissible n S) (p : ℕ) :
    mv S p = 0 ∨ (mv S p ∈ S ∧ 2 ≤ mv S p ∧ (mv S p).minFac = p) := by
  have h := card_filter_le_one hS p
  unfold mv
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · left
    rw [Finset.card_eq_zero.mp h0, sum_empty]
  · right
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have : a ∈ S.filter (fun a => 2 ≤ a ∧ a.minFac = p) := by
      rw [ha]
      exact mem_singleton_self a
    rw [ha, sum_singleton]
    simp only [mem_filter] at this
    exact ⟨this.1, this.2.1, this.2.2⟩

theorem mv_le (hS : Admissible n S) (p : ℕ) : mv S p ≤ n := by
  rcases mv_cases hS p with h | h
  · rw [h]
    exact Nat.zero_le _
  · exact (hS.1 _ h.1).2

theorem dvd_mv (hS : Admissible n S) (p : ℕ) : p ∣ mv S p := by
  rcases mv_cases hS p with h | h
  · rw [h]
    exact dvd_zero p
  · conv_lhs => rw [← h.2.2]
    exact Nat.minFac_dvd _

theorem mul_cv (hS : Admissible n S) (p : ℕ) : p * cv S p = mv S p :=
  Nat.mul_div_cancel' (dvd_mv hS p)

theorem cv_prime (hS : Admissible n S) {p : ℕ} (hp : p ∈ smallPrimes n) (h3 : n < p * p * p)
    (hc : n < cv S p * cv S p) : (cv S p).Prime := by
  rw [mem_smallPrimes] at hp
  have hp2 := hp.1.two_le
  have hmul := mul_cv hS p
  have hle := mv_le hS p
  have hc0 : cv S p ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hc1 : cv S p ≠ 1 := by
    intro h
    rw [h] at hc
    nlinarith
  have hm0 : mv S p ≠ 0 := by
    rw [← hmul]
    exact Nat.mul_ne_zero (by omega) hc0
  rcases mv_cases hS p with h | ⟨_, _, hmf⟩
  · exact absurd h hm0
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hc0) hnp
  have hq := Nat.minFac_prime hc1
  have hqd : (cv S p).minFac ∣ mv S p :=
    dvd_trans (Nat.minFac_dvd _) (Dvd.intro_left p hmul)
  have hpq : p ≤ (cv S p).minFac :=
    calc p = (mv S p).minFac := hmf.symm
      _ ≤ (cv S p).minFac := Nat.minFac_le_of_dvd hq.two_le hqd
  have h1 : p * p ≤ cv S p := by
    calc p * p ≤ (cv S p).minFac * (cv S p).minFac := Nat.mul_le_mul hpq hpq
      _ = (cv S p).minFac ^ 2 := by ring
      _ ≤ cv S p := hsq
  have h2 : p * (p * p) ≤ p * cv S p := Nat.mul_le_mul_left p h1
  rw [hmul] at h2
  have : p * p * p = p * (p * p) := by ring
  linarith

theorem cv_inj (hS : Admissible n S) {p p' : ℕ} (hc : (cv S p).Prime) (heq : cv S p = cv S p') :
    p = p' := by
  have hc' : (cv S p').Prime := heq ▸ hc
  have hm : mv S p ≠ 0 := by
    intro h
    unfold cv at hc
    rw [h, Nat.zero_div] at hc
    exact Nat.not_prime_zero hc
  have hm' : mv S p' ≠ 0 := by
    intro h
    unfold cv at hc'
    rw [h, Nat.zero_div] at hc'
    exact Nat.not_prime_zero hc'
  rcases mv_cases hS p with h | ⟨hmS, _, hmf⟩
  · exact absurd h hm
  rcases mv_cases hS p' with h | ⟨hmS', _, hmf'⟩
  · exact absurd h hm'
  by_contra hne
  have hne' : mv S p ≠ mv S p' := by
    intro h
    apply hne
    rw [← hmf, ← hmf', h]
  have hcop := hS.2 _ hmS _ hmS' hne'
  have d1 : cv S p ∣ mv S p := Dvd.intro_left p (mul_cv hS p)
  have d2 : cv S p ∣ mv S p' := heq ▸ Dvd.intro_left p' (mul_cv hS p')
  exact hc.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop d1 d2)

theorem sg_le (hS : Admissible n S) {p : ℕ} (hp : p ∈ smallPrimes n) :
    sg n S p ≤ (n : ℝ) / p := by
  rw [mem_smallPrimes] at hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  rw [le_div_iff₀ hp0]
  unfold sg
  split_ifs with h
  · have : cv S p * p ≤ n := (Nat.div_mul_le_self _ _).trans (mv_le hS p)
    exact_mod_cast this
  · have h2 : p ^ 2 ≤ n := by
      rw [sq]
      exact hp.2
    have hpn : (p : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast h2)
    have := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) n)
    nlinarith [Real.sqrt_nonneg n]

theorem mv_le_sg (hS : Admissible n S) (p : ℕ) : (mv S p : ℝ) ≤ p * sg n S p := by
  have hmul : ((p : ℝ) * cv S p) = mv S p := by exact_mod_cast mul_cv hS p
  rw [← hmul]
  unfold sg
  split_ifs with h
  · exact le_rfl
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p)
    apply Real.le_sqrt_of_sq_le
    have : cv S p ^ 2 ≤ n := by
      rw [sq]
      exact Nat.le_of_not_lt h
    exact_mod_cast this

theorem card_smallPrimes : (smallPrimes n).card = Nat.primeCounting (Nat.sqrt n) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  congr 1
  ext p
  rw [mem_smallPrimes, mem_filter, mem_range]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_sqrt.mpr h), hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨hp, Nat.le_sqrt.mp (Nat.le_of_lt_succ h)⟩

theorem sum_S_le (hS : Admissible n S) :
    ∑ a ∈ S, a ≤ 1 + ∑ p ∈ smallPrimes n, mv S p + ((∑ p ∈ (range n).filter Nat.Prime, p) + n) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a < 2)]
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun a => ¬ a < 2))
    (fun a => a.minFac * a.minFac ≤ n)]
  have h1 : ∑ a ∈ S.filter (fun a => a < 2), a ≤ 1 := by
    calc ∑ a ∈ S.filter (fun a => a < 2), a ≤ ∑ a ∈ ({1} : Finset ℕ), a := by
          apply sum_le_sum_of_subset
          intro a ha
          rw [mem_filter] at ha
          have := (hS.1 a ha.1).1
          rw [mem_singleton]
          omega
      _ = 1 := sum_singleton _ _
  have h2 : ∑ a ∈ (S.filter (fun a => ¬ a < 2)).filter (fun a => a.minFac * a.minFac ≤ n), a ≤
      ∑ p ∈ smallPrimes n, mv S p := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.minFac) (t := smallPrimes n)]
    · apply sum_le_sum
      intro p _
      apply sum_le_sum_of_subset
      intro a ha
      simp only [mem_filter] at ha ⊢
      exact ⟨ha.1.1.1, by omega, ha.2⟩
    · intro a ha
      simp only [mem_filter] at ha
      rw [mem_smallPrimes]
      exact ⟨Nat.minFac_prime (by omega), ha.2⟩
  have h3 : ∑ a ∈ (S.filter (fun a => ¬ a < 2)).filter (fun a => ¬ a.minFac * a.minFac ≤ n), a ≤
      (∑ p ∈ (range n).filter Nat.Prime, p) + n := by
    calc _ ≤ ∑ q ∈ (range (n + 1)).filter Nat.Prime, q := by
          apply sum_le_sum_of_subset
          intro a ha
          simp only [mem_filter, mem_range] at ha ⊢
          have han := (hS.1 a ha.1.1).2
          refine ⟨by omega, ?_⟩
          by_contra hnp
          have := Nat.minFac_sq_le_self (by omega) hnp
          apply ha.2
          nlinarith
      _ ≤ _ := by
          rw [range_add_one, filter_insert]
          split_ifs with h
          · rw [sum_insert (by simp)]
            omega
          · omega
  omega

theorem sum_bound (hS : Admissible n S) :
    ∑ p ∈ smallPrimes n, ((n : ℝ) - mv S p) ≤ (H n : ℝ) - ∑ a ∈ S, (a : ℝ) + n + 1 := by
  have h := sum_S_le hS
  have hH : H n = (∑ p ∈ (range n).filter Nat.Prime, p) + n * (smallPrimes n).card := by
    rw [card_smallPrimes]
    rfl
  have e1 : (H n : ℝ) = ((∑ p ∈ (range n).filter Nat.Prime, p : ℕ) : ℝ) +
      (n : ℝ) * ((smallPrimes n).card : ℝ) := by
    rw [hH]
    push_cast
    ring
  have e2 : ((∑ a ∈ S, a : ℕ) : ℝ) ≤ 1 + ((∑ p ∈ smallPrimes n, mv S p : ℕ) : ℝ) +
      (((∑ p ∈ (range n).filter Nat.Prime, p : ℕ) : ℝ) + n) := by
    exact_mod_cast h
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  push_cast at e1 e2 ⊢
  linarith

theorem cube_lt {p : ℕ} {u : ℝ} (hn : 0 < n) (hp : 0 < p) (h1 : (n : ℝ) / p ≤ 4 * u)
    (h2 : u < (n : ℝ) ^ (2 / 3 : ℝ) / 4) : n < p * p * p := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hlt : (n : ℝ) < (n : ℝ) ^ (2 / 3 : ℝ) * p := by
    rw [← div_lt_iff₀ hp']
    linarith
  have hcube : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hn'.le]
    norm_num
  have h3 : (n : ℝ) ^ 3 < ((n : ℝ) ^ (2 / 3 : ℝ) * p) ^ 3 :=
    pow_lt_pow_left₀ hlt hn'.le (by norm_num)
  rw [mul_pow, hcube] at h3
  have h5 : (n : ℝ) ^ 2 * n < (n : ℝ) ^ 2 * ((p : ℝ) * p * p) := by
    have e1 : (n : ℝ) ^ 3 = (n : ℝ) ^ 2 * n := by ring
    have e2 : (p : ℝ) ^ 3 = (p : ℝ) * p * p := by ring
    rw [e1, e2] at h3
    exact h3
  have h4 : (n : ℝ) < (p : ℝ) * p * p := lt_of_mul_lt_mul_left h5 (by positivity)
  exact_mod_cast h4

theorem bad_facts (hS : Admissible n S) {u v : ℝ} (hu1 : Real.sqrt n ≤ u)
    (hu2 : u < (n : ℝ) ^ (2 / 3 : ℝ) / 4) (hv4 : v ≤ 4 * u) {p : ℕ} (hp : p ∈ smallPrimes n)
    (hpv : (n : ℝ) / p ≤ v) (hs : ¬ sg n S p ≤ u) :
    (cv S p).Prime ∧ u < cv S p ∧ (cv S p : ℝ) ≤ v := by
  have hpp := mem_smallPrimes.mp hp
  have hn : 0 < n := by
    have := hpp.1.two_le
    nlinarith [hpp.2]
  have h3 := cube_lt hn hpp.1.pos (hpv.trans hv4) hu2
  have hc : n < cv S p * cv S p := by
    by_contra h
    apply hs
    unfold sg
    rw [if_neg h]
    exact hu1
  have hsg : sg n S p = cv S p := by
    unfold sg
    rw [if_pos hc]
  refine ⟨cv_prime hS hp h3 hc, ?_, ?_⟩
  · rw [← hsg]
    exact lt_of_not_ge hs
  · rw [← hsg]
    exact (sg_le hS hp).trans hpv

theorem W_le (hS : Admissible n S) {u : ℝ} (hu1 : Real.sqrt n ≤ u)
    (hu2 : u < (n : ℝ) ^ (2 / 3 : ℝ) / 4) : W n u ≤ (Ks n S u).card := by
  apply Nat.sInf_le
  intro v _ hv4
  unfold A primesBetween
  rw [← card_filter_add_card_filter_not
    (s := (smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v))
    (fun p => sg n S p ≤ u)]
  rw [add_comm]
  apply add_le_add
  · apply card_le_card_of_injOn (cv S)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨⟨hp, _, hpv⟩, hs⟩ := hp
      obtain ⟨hpr, hlt, hle⟩ := bad_facts hS hu1 hu2 hv4 hp hpv hs
      simp only [Finset.mem_coe, Finset.mem_filter, mem_range]
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hle), hpr, hlt⟩
    · intro p hp p' _ heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨⟨hp, _, hpv⟩, hs⟩ := hp
      obtain ⟨hpr, _, _⟩ := bad_facts hS hu1 hu2 hv4 hp hpv hs
      exact cv_inj hS hpr heq
  · apply card_le_card
    intro p hp
    simp only [mem_filter] at hp
    simp only [Ks, mem_filter]
    exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2.trans hv4, hp.2⟩

theorem pointwise (hS : Admissible n S) {u : ℝ}
    (hu : u ∈ Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4)) :
    ENNReal.ofReal ((n : ℝ) / 4) * ENNReal.ofReal ((W n u : ℝ) / u) ≤
      ∑ p ∈ smallPrimes n,
        (Set.Ico (sg n S p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u := by
  obtain ⟨hu1, hu2⟩ := hu
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hu0 : 0 < u := hsq.trans_le hu1
  have hW := W_le hS hu1 hu2
  rw [← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((n : ℝ) / 4 * ((W n u : ℝ) / u))
      ≤ ENNReal.ofReal (∑ p ∈ Ks n S u, (p : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        calc (n : ℝ) / 4 * ((W n u : ℝ) / u) ≤ (n : ℝ) / 4 * (((Ks n S u).card : ℝ) / u) := by
              gcongr
          _ = ∑ p ∈ Ks n S u, (n : ℝ) / (4 * u) := by
              rw [sum_const, nsmul_eq_mul]
              field_simp
          _ ≤ ∑ p ∈ Ks n S u, (p : ℝ) := by
              apply sum_le_sum
              intro p hp
              simp only [Ks, mem_filter] at hp
              have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_smallPrimes.mp hp.1).1.pos
              rw [div_le_iff₀ (by positivity)]
              have := hp.2.2.1
              rw [div_le_iff₀ hp0] at this
              linarith
    _ = ∑ p ∈ Ks n S u, ENNReal.ofReal p :=
        ENNReal.ofReal_sum_of_nonneg (fun p _ => Nat.cast_nonneg p)
    _ ≤ _ := by
        unfold Ks
        rw [sum_filter]
        apply sum_le_sum
        intro p _
        split_ifs with h
        · rw [Set.indicator_of_mem (show u ∈ Set.Ico _ _ from ⟨h.2.2, h.1⟩)]
        · exact bot_le

end LowerAux

theorem lower_bound (n : ℕ) (S : Finset ℕ) (hS : Admissible n S) :
    ENNReal.ofReal ((n : ℝ) / 4) *
        ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4),
          ENNReal.ofReal ((W n u : ℝ) / u)
      ≤ ENNReal.ofReal ((H n : ℝ) - (∑ a ∈ S, (a : ℝ)) + n + 1) := by
  classical
  calc ENNReal.ofReal ((n : ℝ) / 4) *
        ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4),
          ENNReal.ofReal ((W n u : ℝ) / u)
      = ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4),
          ENNReal.ofReal ((n : ℝ) / 4) * ENNReal.ofReal ((W n u : ℝ) / u) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) ^ (2 / 3 : ℝ) / 4), ∑ p ∈ smallPrimes n,
          (Set.Ico (LowerAux.sg n S p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u :=
        setLIntegral_mono' measurableSet_Ico (fun u hu => LowerAux.pointwise hS hu)
    _ ≤ ∫⁻ u, ∑ p ∈ smallPrimes n,
          (Set.Ico (LowerAux.sg n S p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u :=
        setLIntegral_le_lintegral _ _
    _ = ∑ p ∈ smallPrimes n, ∫⁻ u,
          (Set.Ico (LowerAux.sg n S p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u :=
        lintegral_finsetSum _ (fun p _ => measurable_const.indicator measurableSet_Ico)
    _ = ∑ p ∈ smallPrimes n,
          ENNReal.ofReal p * ENNReal.ofReal ((n : ℝ) / p - LowerAux.sg n S p) := by
        apply sum_congr rfl
        intro p _
        rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
    _ ≤ ∑ p ∈ smallPrimes n, ENNReal.ofReal ((n : ℝ) - LowerAux.mv S p) := by
        apply sum_le_sum
        intro p hp
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg p)]
        apply ENNReal.ofReal_le_ofReal
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (LowerAux.mem_smallPrimes.mp hp).1.pos
        have e : (p : ℝ) * ((n : ℝ) / p) = n := by field_simp
        rw [mul_sub, e]
        linarith [LowerAux.mv_le_sg hS p]
    _ = ENNReal.ofReal (∑ p ∈ smallPrimes n, ((n : ℝ) - LowerAux.mv S p)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro p _
        have := LowerAux.mv_le hS p
        rw [sub_nonneg]
        exact_mod_cast this
    _ ≤ _ := ENNReal.ofReal_le_ofReal (LowerAux.sum_bound hS)

end Erdos879
