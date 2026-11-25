import Erdos879.Defs
import Erdos879.UpperMatch

open Finset MeasureTheory

namespace Erdos879

def bp (n p : ℕ) : ℕ := (partner n p).getD p

def mp (n p : ℕ) : ℕ := p * bp n p

def L (n : ℕ) : Finset ℕ := (range (n + 1)).filter (fun q => q.Prime ∧ n < q * q)

def U (n : ℕ) : Finset ℕ := (L n).filter (fun q => ∃ p ∈ smallPrimes n, partner n p = some q)

def Sset (n : ℕ) : Finset ℕ := (smallPrimes n).image (mp n) ∪ (L n \ U n)

lemma bp_spec {n p : ℕ} :
    (partner n p = none ∧ bp n p = p) ∨ partner n p = some (bp n p) := by
  cases h : partner n p with
  | none => left; simp [bp, h]
  | some q => right; simp [bp, h]

lemma bp_prime {n p : ℕ} (hp : p ∈ smallPrimes n) : (bp n p).Prime := by
  rcases bp_spec (n := n) (p := p) with ⟨_, h⟩ | h
  · rw [h]
    exact (mem_smallPrimes.1 hp).1
  · exact (partner_spec h).1

lemma mul_bp_le {n p : ℕ} (hp : p ∈ smallPrimes n) : p * bp n p ≤ n := by
  rcases bp_spec (n := n) (p := p) with ⟨_, h⟩ | h
  · rw [h]
    exact (mem_smallPrimes.1 hp).2
  · exact (partner_spec h).2.2.1

lemma small_ne_large {n x y : ℕ} (hx : x * x ≤ n) (hy : n < y * y) : x ≠ y := by
  rintro rfl
  omega

lemma bp_ne_of_small {n p x : ℕ} (_hp : p ∈ smallPrimes n) (hx : x ∈ smallPrimes n)
    (hxp : x ≠ p) : bp n p ≠ x := by
  rcases bp_spec (n := n) (p := p) with ⟨_, h⟩ | h
  · rw [h]
    exact Ne.symm hxp
  · exact Ne.symm (small_ne_large (mem_smallPrimes.1 hx).2 (partner_spec h).2.1)

lemma bp_inj {n p p' : ℕ} (hp : p ∈ smallPrimes n) (hp' : p' ∈ smallPrimes n)
    (h : bp n p = bp n p') : p = p' := by
  by_contra hne
  rcases bp_spec (n := n) (p := p) with ⟨_, h1⟩ | h1
  · exact bp_ne_of_small hp' hp hne (h.symm.trans h1)
  · rcases bp_spec (n := n) (p := p') with ⟨_, h2⟩ | h2
    · exact bp_ne_of_small hp hp' (Ne.symm hne) (h.trans h2)
    · rw [h] at h1
      exact hne (partner_inj hp hp' h1 h2)

lemma coprime_mp {n p p' : ℕ} (hp : p ∈ smallPrimes n) (hp' : p' ∈ smallPrimes n)
    (hne : p ≠ p') : Nat.Coprime (mp n p) (mp n p') := by
  have hpp := (mem_smallPrimes.1 hp).1
  have hpp' := (mem_smallPrimes.1 hp').1
  have hb := bp_prime hp
  have hb' := bp_prime hp'
  unfold mp
  refine Nat.Coprime.mul_left (Nat.Coprime.mul_right ?_ ?_) (Nat.Coprime.mul_right ?_ ?_)
  · exact (Nat.coprime_primes hpp hpp').2 hne
  · exact (Nat.coprime_primes hpp hb').2 (Ne.symm (bp_ne_of_small hp' hp hne))
  · exact (Nat.coprime_primes hb hpp').2 (bp_ne_of_small hp hp' (Ne.symm hne))
  · exact (Nat.coprime_primes hb hb').2 (fun h => hne (bp_inj hp hp' h))

lemma four_le_mp {n p : ℕ} (hp : p ∈ smallPrimes n) : 4 ≤ mp n p := by
  have h1 := (mem_smallPrimes.1 hp).1.two_le
  have h2 := (bp_prime hp).two_le
  unfold mp
  nlinarith

lemma mp_injOn (n : ℕ) : Set.InjOn (mp n) (smallPrimes n) := by
  intro p hp p' hp' h
  by_contra hne
  have hc := coprime_mp hp hp' hne
  rw [← h, Nat.coprime_self] at hc
  have := four_le_mp hp
  omega

lemma coprime_mp_large {n p q : ℕ} (hp : p ∈ smallPrimes n) (hq : q ∈ L n \ U n) :
    Nat.Coprime (mp n p) q := by
  simp only [L, U, mem_sdiff, mem_filter, mem_range, not_and, not_exists] at hq
  obtain ⟨⟨hqn, hqp, hqq⟩, hnot⟩ := hq
  have hpp := (mem_smallPrimes.1 hp).1
  unfold mp
  refine Nat.Coprime.mul_left ?_ ?_
  · exact (Nat.coprime_primes hpp hqp).2 (small_ne_large (mem_smallPrimes.1 hp).2 hqq)
  · refine (Nat.coprime_primes (bp_prime hp) hqp).2 ?_
    rcases bp_spec (n := n) (p := p) with ⟨_, h⟩ | h
    · rw [h]
      exact small_ne_large (mem_smallPrimes.1 hp).2 hqq
    · intro he
      rw [he] at h
      exact hnot ⟨by omega, hqp, hqq⟩ p hp h

lemma admissible_Sset (n : ℕ) : Admissible n (Sset n) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [Sset, mem_union, mem_image] at ha
    rcases ha with ⟨p, hp, rfl⟩ | ha
    · exact ⟨by have := four_le_mp hp; omega, mul_bp_le hp⟩
    · simp only [L, U, mem_sdiff, mem_filter, mem_range] at ha
      exact ⟨ha.1.2.1.one_lt.le, by omega⟩
  · intro a ha b hb hab
    rw [Sset, mem_union, mem_image] at ha hb
    rcases ha with ⟨p, hp, rfl⟩ | ha <;> rcases hb with ⟨p', hp', rfl⟩ | hb
    · exact coprime_mp hp hp' (fun h => hab (by rw [h]))
    · exact coprime_mp_large hp hb
    · exact (coprime_mp_large hp' ha).symm
    · have h1 : a.Prime := by
        simp only [L, U, mem_sdiff, mem_filter] at ha
        exact ha.1.2.1
      have h2 : b.Prime := by
        simp only [L, U, mem_sdiff, mem_filter] at hb
        exact hb.1.2.1
      exact (Nat.coprime_primes h1 h2).2 hab

lemma sum_Sset (n : ℕ) :
    ∑ a ∈ Sset n, (a : ℝ) = ∑ p ∈ smallPrimes n, (mp n p : ℝ) + ∑ q ∈ L n \ U n, (q : ℝ) := by
  rw [Sset, sum_union, sum_image (fun p hp p' hp' h => mp_injOn n hp hp' h)]
  rw [disjoint_left]
  intro a ha hb
  rw [mem_image] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  simp only [L, U, mem_sdiff, mem_filter] at hb
  have h1 := (mem_smallPrimes.1 hp).1.one_lt
  have h2 := (bp_prime hp).one_lt
  exact Nat.not_prime_mul (by omega) (by omega) hb.1.2.1

lemma primeCounting_sqrt (n : ℕ) : Nat.primeCounting (Nat.sqrt n) = (smallPrimes n).card := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  congr 1
  ext p
  rw [Nat.mem_primesLE, mem_smallPrimes, Nat.le_sqrt]
  tauto

lemma sum_small_le (n : ℕ) : ∑ p ∈ smallPrimes n, (p : ℝ) ≤ n := by
  have h1 : ∑ p ∈ smallPrimes n, p ≤ ∑ p ∈ smallPrimes n, Nat.sqrt n :=
    sum_le_sum fun p hp => Nat.le_sqrt.2 (mem_smallPrimes.1 hp).2
  have h2 : (smallPrimes n).card ≤ Nat.sqrt n := by
    have : smallPrimes n ⊆ Icc 1 (Nat.sqrt n) := by
      intro p hp
      rw [mem_Icc]
      exact ⟨(mem_smallPrimes.1 hp).1.one_lt.le, Nat.le_sqrt.2 (mem_smallPrimes.1 hp).2⟩
    have := card_le_card this
    rw [Nat.card_Icc] at this
    omega
  rw [sum_const, smul_eq_mul] at h1
  have h3 : ∑ p ∈ smallPrimes n, p ≤ n :=
    h1.trans ((Nat.mul_le_mul_right _ h2).trans (Nat.sqrt_le n))
  rw [← Nat.cast_sum]
  exact_mod_cast h3

lemma sum_U_le (n : ℕ) : ∑ q ∈ U n, (q : ℝ) ≤ ∑ p ∈ smallPrimes n, (n : ℝ) / p := by
  have hsub : U n ⊆ (smallPrimes n).image (bp n) := by
    intro q hq
    simp only [U, mem_filter] at hq
    obtain ⟨p, hp, hpq⟩ := hq.2
    rw [mem_image]
    exact ⟨p, hp, by simp [bp, hpq]⟩
  calc ∑ q ∈ U n, (q : ℝ) ≤ ∑ q ∈ (smallPrimes n).image (bp n), (q : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ p ∈ smallPrimes n, (bp n p : ℝ) :=
        sum_image_le_of_nonneg (fun _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ p ∈ smallPrimes n, (n : ℝ) / p :=
        sum_le_sum fun p hp => le_div_of_mul_le (mem_smallPrimes.1 hp).1.pos (mul_bp_le hp)

lemma accounting (n : ℕ) :
    (H n : ℝ) - ∑ a ∈ Sset n, (a : ℝ) ≤
      ∑ p ∈ smallPrimes n, ((n : ℝ) - mp n p) +
        ((n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) + n) := by
  have hH : (H n : ℝ) = ∑ p ∈ (range n).filter Nat.Prime, (p : ℝ) +
      n * (smallPrimes n).card := by
    rw [H, primeCounting_sqrt]
    push_cast
    rfl
  have hsub : (range n).filter Nat.Prime ⊆ smallPrimes n ∪ L n := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    rw [mem_union]
    by_cases hpp : p * p ≤ n
    · exact Or.inl (mem_smallPrimes.2 ⟨hp.2, hpp⟩)
    · right
      simp only [L, mem_filter, mem_range]
      exact ⟨by omega, hp.2, by omega⟩
  have hdisj : Disjoint (smallPrimes n) (L n) := by
    rw [disjoint_left]
    intro p hp hL
    simp only [L, mem_filter] at hL
    have := (mem_smallPrimes.1 hp).2
    omega
  have h1 : ∑ p ∈ (range n).filter Nat.Prime, (p : ℝ) ≤
      ∑ p ∈ smallPrimes n, (p : ℝ) + ∑ q ∈ L n, (q : ℝ) := by
    rw [← sum_union hdisj]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have h2 : ∑ q ∈ L n, (q : ℝ) = ∑ q ∈ L n \ U n, (q : ℝ) + ∑ q ∈ U n, (q : ℝ) :=
    (sum_sdiff (filter_subset _ _)).symm
  have h3 : ∑ p ∈ smallPrimes n, ((n : ℝ) - mp n p) =
      n * (smallPrimes n).card - ∑ p ∈ smallPrimes n, (mp n p : ℝ) := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  have h4 : (n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) = ∑ p ∈ smallPrimes n, (n : ℝ) / p := by
    rw [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    ring
  have h5 := sum_small_le n
  have h6 := sum_U_le n
  rw [hH, sum_Sset, h3, h4]
  linarith

lemma apt_le {n p : ℕ} (hp : p ∈ smallPrimes n) : apt n p ≤ (n : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_smallPrimes.1 hp).1.pos
  rcases bp_spec (n := n) (p := p) with ⟨h, _⟩ | h
  · rw [apt_none h, le_div_iff₀ hp0]
    have h1 : (p : ℝ) ≤ Real.sqrt n := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      have : ((p * p : ℕ) : ℝ) ≤ n := by exact_mod_cast (mem_smallPrimes.1 hp).2
      push_cast at this
      nlinarith
    have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  · rw [apt_some h]
    exact le_div_of_mul_le (mem_smallPrimes.1 hp).1.pos (partner_spec h).2.2.1

lemma sqrt_le_apt {n p : ℕ} : Real.sqrt n ≤ apt n p := by
  rcases bp_spec (n := n) (p := p) with ⟨h, _⟩ | h
  · rw [apt_none h]
  · rw [apt_some h, Real.sqrt_le_left (Nat.cast_nonneg _)]
    have : ((n : ℕ) : ℝ) ≤ ((bp n p * bp n p : ℕ) : ℝ) := by
      exact_mod_cast (partner_spec h).2.1.le
    push_cast at this
    nlinarith

lemma mp_bound {n p : ℕ} (hp : p ∈ smallPrimes n) :
    (n : ℝ) - mp n p ≤ 2 * ((p : ℝ) * ((n : ℝ) / p - apt n p)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_smallPrimes.1 hp).1.pos
  have hpn : (p : ℝ) * ((n : ℝ) / p) = n := by field_simp
  have hm : (mp n p : ℝ) = (p : ℝ) * (bp n p : ℝ) := by
    unfold mp
    push_cast
    ring
  rw [hm, mul_sub, hpn]
  rcases bp_spec (n := n) (p := p) with ⟨h, hb⟩ | h
  · rw [apt_none h, hb]
    have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
    nlinarith [sq_nonneg (Real.sqrt n - p)]
  · rw [apt_some h]
    rw [← h] at *
    have : ((p * bp n p : ℕ) : ℝ) ≤ n := by exact_mod_cast mul_bp_le hp
    push_cast at this
    nlinarith

lemma Ico_sub {n p : ℕ} (hp : p ∈ smallPrimes n) :
    Set.Ico (apt n p) ((n : ℝ) / p) ⊆ Set.Ico (Real.sqrt n) ((n : ℝ) / 2) := by
  refine Set.Ico_subset_Ico sqrt_le_apt ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_smallPrimes.1 hp).1.two_le
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) h2

lemma pointwise (n : ℕ) (u : ℝ) (hu : u ∈ Set.Ico (Real.sqrt n) ((n : ℝ) / 2)) :
    ∑ p ∈ smallPrimes n,
        (Set.Ico (apt n p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u ≤
      ENNReal.ofReal n * ENNReal.ofReal ((Winf n u : ℝ) / u) := by
  obtain ⟨hu1, hu2⟩ := hu
  have hn0 : (0 : ℝ) < n := by linarith [Real.sqrt_nonneg (n : ℝ)]
  have hu0 : 0 < u := lt_of_lt_of_le (Real.sqrt_pos.2 hn0) hu1
  have heq : ∑ p ∈ smallPrimes n,
      (Set.Ico (apt n p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u =
      ∑ p ∈ Q n u, ENNReal.ofReal p := by
    rw [Q, sum_filter]
    refine sum_congr rfl fun p _ => ?_
    simp only [Set.indicator, Set.mem_Ico]
  rw [heq, ← ENNReal.ofReal_sum_of_nonneg (fun p _ => Nat.cast_nonneg p),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hc := card_Q_le n u hu1
  calc ∑ p ∈ Q n u, (p : ℝ) ≤ ∑ p ∈ Q n u, (n : ℝ) / u := by
        refine sum_le_sum fun p hp => ?_
        rw [Q, mem_filter] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_smallPrimes.1 hp.1).1.pos
        have h1 := hp.2.2
        rw [lt_div_iff₀ hp0] at h1
        rw [le_div_iff₀ hu0]
        linarith
    _ = (Q n u).card * ((n : ℝ) / u) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Winf n u * ((n : ℝ) / u) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = n * ((Winf n u : ℝ) / u) := by ring

lemma layer (n : ℕ) :
    ENNReal.ofReal (∑ p ∈ smallPrimes n, ((n : ℝ) - mp n p)) ≤
      ENNReal.ofReal (2 * (n : ℝ)) *
        ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), ENNReal.ofReal ((Winf n u : ℝ) / u) := by
  have h1 : ENNReal.ofReal (∑ p ∈ smallPrimes n, ((n : ℝ) - mp n p)) ≤
      2 * ∑ p ∈ smallPrimes n, ENNReal.ofReal p * volume (Set.Ico (apt n p) ((n : ℝ) / p)) := by
    calc ENNReal.ofReal (∑ p ∈ smallPrimes n, ((n : ℝ) - mp n p))
        ≤ ENNReal.ofReal (∑ p ∈ smallPrimes n, 2 * ((p : ℝ) * ((n : ℝ) / p - apt n p))) :=
          ENNReal.ofReal_le_ofReal (sum_le_sum fun p hp => mp_bound hp)
      _ = ∑ p ∈ smallPrimes n, ENNReal.ofReal (2 * ((p : ℝ) * ((n : ℝ) / p - apt n p))) := by
          refine ENNReal.ofReal_sum_of_nonneg (fun p hp => ?_)
          have := apt_le hp
          have : (0 : ℝ) ≤ (n : ℝ) / p - apt n p := by linarith
          positivity
      _ = 2 * ∑ p ∈ smallPrimes n,
            ENNReal.ofReal p * volume (Set.Ico (apt n p) ((n : ℝ) / p)) := by
          rw [mul_sum]
          refine sum_congr rfl fun p _ => ?_
          rw [Real.volume_Ico, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_ofNat]
  have h2 : ∑ p ∈ smallPrimes n, ENNReal.ofReal p * volume (Set.Ico (apt n p) ((n : ℝ) / p)) =
      ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), ∑ p ∈ smallPrimes n,
        (Set.Ico (apt n p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u := by
    rw [lintegral_finsetSum _ (fun p _ => measurable_const.indicator measurableSet_Ico)]
    refine sum_congr rfl fun p hp => ?_
    rw [lintegral_indicator_const measurableSet_Ico, Measure.restrict_apply measurableSet_Ico,
      Set.inter_eq_left.2 (Ico_sub hp)]
  have h3 : ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), ∑ p ∈ smallPrimes n,
        (Set.Ico (apt n p) ((n : ℝ) / p)).indicator (fun _ => ENNReal.ofReal p) u ≤
      ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2),
        ENNReal.ofReal n * ENNReal.ofReal ((Winf n u : ℝ) / u) :=
    lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2
      (Filter.Eventually.of_forall fun u hu => pointwise n u hu))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h3
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
  calc _ ≤ _ := h1
    _ = _ := by rw [h2]
    _ ≤ _ := mul_le_mul_right h3 2

theorem upper_bound (n : ℕ) :
    ∃ S : Finset ℕ, Admissible n S ∧
      ENNReal.ofReal ((H n : ℝ) - ∑ a ∈ S, (a : ℝ)) ≤
        (ENNReal.ofReal (2 * (n : ℝ)) *
            ∫⁻ u in Set.Ico (Real.sqrt n) ((n : ℝ) / 2), ENNReal.ofReal ((Winf n u : ℝ) / u))
          + ENNReal.ofReal ((n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) + n) := by
  refine ⟨Sset n, admissible_Sset n, ?_⟩
  calc ENNReal.ofReal ((H n : ℝ) - ∑ a ∈ Sset n, (a : ℝ))
      ≤ ENNReal.ofReal (∑ p ∈ smallPrimes n, ((n : ℝ) - mp n p) +
          ((n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) + n)) :=
        ENNReal.ofReal_le_ofReal (accounting n)
    _ ≤ ENNReal.ofReal (∑ p ∈ smallPrimes n, ((n : ℝ) - mp n p)) +
          ENNReal.ofReal ((n : ℝ) * (∑ p ∈ smallPrimes n, (1 : ℝ) / p) + n) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add_left (layer n) _

end Erdos879
