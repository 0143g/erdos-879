import Erdos879.Defs

open Finset MeasureTheory

namespace Erdos879

lemma A_le_card (n : ℕ) (u v : ℝ) : A n u v ≤ (smallPrimes n).card :=
  card_filter_le _ _

lemma card_mem_W (n : ℕ) (u : ℝ) :
    (smallPrimes n).card ∈
      {w : ℕ | ∀ v : ℝ, u ≤ v → v ≤ 4 * u → A n u v ≤ primesBetween u v + w} :=
  fun v _ _ => (A_le_card n u v).trans (Nat.le_add_left _ _)

lemma card_mem_Winf (n : ℕ) (u : ℝ) :
    (smallPrimes n).card ∈ {w : ℕ | ∀ v : ℝ, u ≤ v → A n u v ≤ primesBetween u v + w} :=
  fun v _ => (A_le_card n u v).trans (Nat.le_add_left _ _)

lemma W_spec (n : ℕ) (u v : ℝ) (h1 : u ≤ v) (h2 : v ≤ 4 * u) :
    A n u v ≤ primesBetween u v + W n u :=
  Nat.sInf_mem ⟨_, card_mem_W n u⟩ v h1 h2

lemma Winf_spec (n : ℕ) (u v : ℝ) (h1 : u ≤ v) :
    A n u v ≤ primesBetween u v + Winf n u :=
  Nat.sInf_mem ⟨_, card_mem_Winf n u⟩ v h1

lemma A_le_primeCounting (n : ℕ) (u v : ℝ) (hu : Real.sqrt n ≤ u) :
    A n u v ≤ Nat.primeCounting ⌊u⌋₊ := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  refine (A_le_card n u v).trans (card_le_card ?_)
  intro p hp
  simp only [smallPrimes, mem_filter, mem_range] at hp
  rw [Nat.mem_primesLE]
  refine ⟨Nat.le_floor ?_, hp.2.1⟩
  refine le_trans ?_ hu
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact_mod_cast (by nlinarith [hp.2.2] : p ^ 2 ≤ n)

lemma primeCounting_le_primesBetween
    (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 4 * u < v) :
    Nat.primeCounting ⌊u⌋₊ ≤ primesBetween u v := by
  have h1 := hπ ⌊u⌋₊
  have h2 : Nat.primeCounting (4 * ⌊u⌋₊) ≤ Nat.primeCounting ⌊u⌋₊ + primesBetween u v := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro q hq
    rw [Nat.mem_primesLE] at hq
    rw [mem_union, Nat.mem_primesLE]
    by_cases hqu : q ≤ ⌊u⌋₊
    · exact Or.inl ⟨hqu, hq.2⟩
    · right
      simp only [mem_filter, mem_range]
      have hfl : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor ?_), hq.2, ?_⟩
      · have : (q : ℝ) ≤ 4 * ⌊u⌋₊ := by exact_mod_cast hq.1
        linarith
      · have : (⌊u⌋₊ : ℝ) + 1 ≤ q := by exact_mod_cast (by omega : ⌊u⌋₊ + 1 ≤ q)
        linarith [Nat.lt_floor_add_one u]
  omega

noncomputable def brk (n : ℕ) : Finset ℝ :=
  (smallPrimes n).image (fun p : ℕ => (n : ℝ) / p) ∪
    (smallPrimes n).image (fun p : ℕ => (n : ℝ) / p / 4) ∪
    (range (n + 1)).image (fun q : ℕ => (q : ℝ))

lemma core (n : ℕ) (u u' v : ℝ) (hb : ∀ b ∈ brk n, (u < b ↔ u' < b)) (hA : 0 < A n u v) :
    ∃ v', u' ≤ v' ∧ (v ≤ 4 * u → v' ≤ 4 * u') ∧ A n u v ≤ A n u' v' ∧
      primesBetween u' v' ≤ primesBetween u v := by
  classical
  have hne : ((smallPrimes n).filter
      (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v)).Nonempty := by
    rw [← card_pos]
    exact hA
  obtain ⟨p0, hp0, hmax⟩ := exists_max_image _ (fun p : ℕ => (n : ℝ) / p) hne
  rw [mem_filter] at hp0
  have hb1 : ∀ p ∈ smallPrimes n, (u < (n : ℝ) / p ↔ u' < (n : ℝ) / p) := fun p hp =>
    hb _ (by simp only [brk, mem_union, mem_image]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩))
  have hb2 : ∀ p ∈ smallPrimes n, (u < (n : ℝ) / p / 4 ↔ u' < (n : ℝ) / p / 4) := fun p hp =>
    hb _ (by simp only [brk, mem_union, mem_image]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩))
  have hb3 : ∀ q : ℕ, q ≤ n → (u < (q : ℝ) ↔ u' < (q : ℝ)) := fun q hq =>
    hb _ (by
      simp only [brk, mem_union, mem_image, mem_range]
      exact Or.inr ⟨q, Nat.lt_succ_of_le hq, rfl⟩)
  have hp0P := hp0.1
  have hp0prime : p0.Prime := by
    simp only [smallPrimes, mem_filter] at hp0P
    exact hp0P.2.1
  have hp0one : (1 : ℝ) ≤ p0 := by exact_mod_cast hp0prime.one_lt.le
  have hv'n : (n : ℝ) / p0 ≤ n := div_le_self (Nat.cast_nonneg _) hp0one
  refine ⟨(n : ℝ) / p0, ((hb1 p0 hp0P).1 hp0.2.1).le, ?_, ?_, ?_⟩
  · intro h4
    have h5 : ¬ u < (n : ℝ) / p0 / 4 := by
      intro h
      linarith [hp0.2.2]
    rw [hb2 p0 hp0P] at h5
    linarith [not_lt.mp h5]
  · refine card_le_card ?_
    intro p hp
    rw [mem_filter] at hp ⊢
    exact ⟨hp.1, (hb1 p hp.1).1 hp.2.1, hmax p (mem_filter.mpr hp)⟩
  · refine card_le_card ?_
    intro q hq
    simp only [mem_filter, mem_range] at hq ⊢
    have hqv : q ≤ ⌊(n : ℝ) / p0⌋₊ := Nat.lt_succ_iff.mp hq.1
    have hqn : q ≤ n := by
      have := Nat.floor_le_floor (R := ℝ) hv'n
      rw [Nat.floor_natCast] at this
      omega
    refine ⟨Nat.lt_succ_of_le (hqv.trans (Nat.floor_le_floor hp0.2.2)), hq.2.1, ?_⟩
    exact (hb3 q hqn).2 hq.2.2

lemma W_inv (n : ℕ) (u u' : ℝ) (hb : ∀ b ∈ brk n, (u < b ↔ u' < b)) : W n u = W n u' := by
  have key : ∀ x y : ℝ, (∀ b ∈ brk n, (x < b ↔ y < b)) →
      ∀ w : ℕ, (∀ v : ℝ, y ≤ v → v ≤ 4 * y → A n y v ≤ primesBetween y v + w) →
        ∀ v : ℝ, x ≤ v → v ≤ 4 * x → A n x v ≤ primesBetween x v + w := by
    intro x y hxy w hw v h1 h2
    rcases Nat.eq_zero_or_pos (A n x v) with h0 | h0
    · omega
    obtain ⟨v', h1', h2', h3', h4'⟩ := core n x y v hxy h0
    have := hw v' h1' (h2' h2)
    omega
  unfold W
  congr 1
  ext w
  exact ⟨key u' u (fun b hb' => (hb b hb').symm) w, key u u' hb w⟩

lemma Winf_inv (n : ℕ) (u u' : ℝ) (hb : ∀ b ∈ brk n, (u < b ↔ u' < b)) :
    Winf n u = Winf n u' := by
  have key : ∀ x y : ℝ, (∀ b ∈ brk n, (x < b ↔ y < b)) →
      ∀ w : ℕ, (∀ v : ℝ, y ≤ v → A n y v ≤ primesBetween y v + w) →
        ∀ v : ℝ, x ≤ v → A n x v ≤ primesBetween x v + w := by
    intro x y hxy w hw v h1
    rcases Nat.eq_zero_or_pos (A n x v) with h0 | h0
    · omega
    obtain ⟨v', h1', -, h3', h4'⟩ := core n x y v hxy h0
    have := hw v' h1'
    omega
  unfold Winf
  congr 1
  ext w
  exact ⟨key u' u (fun b hb' => (hb b hb').symm) w, key u u' hb w⟩

noncomputable def pat (n : ℕ) (u : ℝ) : brk n → Bool := fun b => decide (u < (b : ℝ))

lemma measurable_pat (n : ℕ) : Measurable (pat n) := by
  rw [measurable_pi_iff]
  intro b
  refine measurable_to_bool ?_
  have : (fun u : ℝ => pat n u b) ⁻¹' {true} = Set.Iio (b : ℝ) := by
    ext u
    simp [pat]
  rw [this]
  exact measurableSet_Iio

lemma iff_of_pat (n : ℕ) (u u' : ℝ) (h : pat n u = pat n u') :
    ∀ b ∈ brk n, (u < b ↔ u' < b) := by
  intro b hb
  have := congrFun h ⟨b, hb⟩
  simpa [pat] using this

lemma measurable_of_pat_inv (n : ℕ) (f : ℝ → ℕ)
    (hf : ∀ u u' : ℝ, pat n u = pat n u' → f u = f u') : Measurable f := by
  classical
  let g : (brk n → Bool) → ℕ := fun π => if h : ∃ u, pat n u = π then f h.choose else 0
  have hfg : f = g ∘ pat n := by
    funext u
    have h : ∃ u', pat n u' = pat n u := ⟨u, rfl⟩
    simp only [Function.comp, g, dif_pos h]
    exact hf _ _ h.choose_spec.symm
  rw [hfg]
  exact (measurable_of_finite g).comp (measurable_pat n)

theorem measurable_W (n : ℕ) : Measurable (fun u : ℝ => W n u) := by
  exact measurable_of_pat_inv n _ (fun u u' h => W_inv n u u' (iff_of_pat n u u' h))

theorem measurable_Winf (n : ℕ) : Measurable (fun u : ℝ => Winf n u) := by
  exact measurable_of_pat_inv n _ (fun u u' h => Winf_inv n u u' (iff_of_pat n u u' h))

theorem W_le_card (n : ℕ) (u : ℝ) : W n u ≤ (smallPrimes n).card := by
  exact Nat.sInf_le (card_mem_W n u)

theorem Winf_le_card (n : ℕ) (u : ℝ) : Winf n u ≤ (smallPrimes n).card := by
  exact Nat.sInf_le (card_mem_Winf n u)

theorem W_le_Winf (n : ℕ) (u : ℝ) : W n u ≤ Winf n u := by
  exact Nat.sInf_le (fun v h1 _ => Winf_spec n u v h1)

theorem Winf_eq_W (hπ : ∀ m : ℕ, 2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m))
    (n : ℕ) (u : ℝ) (hu : Real.sqrt n ≤ u) : Winf n u = W n u := by
  refine le_antisymm (Nat.sInf_le ?_) (W_le_Winf n u)
  intro v h1
  by_cases h2 : v ≤ 4 * u
  · exact W_spec n u v h1 h2
  · have hu0 : 0 ≤ u := (Real.sqrt_nonneg _).trans hu
    have := (A_le_primeCounting n u v hu).trans
      (primeCounting_le_primesBetween hπ u v hu0 (lt_of_not_ge h2))
    omega

end Erdos879
