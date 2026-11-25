import Erdos879.Analytic.Block
import Erdos879.Measurable

open Finset MeasureTheory

namespace Erdos879

private lemma bnd_one_lt_log {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

private lemma bnd_card_le (n : ℕ) : ((smallPrimes n).card : ℝ) ≤ n + 1 := by
  have : (smallPrimes n).card ≤ n + 1 := by
    unfold smallPrimes
    exact (card_filter_le _ _).trans (card_range _).le
  exact_mod_cast this

private lemma bnd_primeCounting_le (k : ℕ) : Nat.primeCounting k ≤ k := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hsub : Nat.primesLE k ⊆ (range (k + 1)).erase 0 := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [mem_erase, mem_range]
    exact ⟨hp.2.ne_zero, by omega⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (by simp), card_range] at this
  simpa using this

private lemma bnd_lint_le (n : ℕ) (s : Set ℝ) (c : ℝ)
    (h : ∀ u ∈ s, (W n u : ℝ) / u ≤ c) :
    (∫⁻ u in s, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal c * volume s := by
  calc (∫⁻ u in s, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ∫⁻ _ in s, ENNReal.ofReal c :=
        setLIntegral_mono measurable_const (fun u hu => ENNReal.ofReal_le_ofReal (h u hu))
    _ = _ := setLIntegral_const _ _

private lemma bnd_lint_Ico (n : ℕ) (a b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ u ∈ Set.Ico a b, (W n u : ℝ) / u ≤ c) :
    (∫⁻ u in Set.Ico a b, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal (c * (b - a)) := by
  rw [ENNReal.ofReal_mul hc, ← Real.volume_Ico]
  exact bnd_lint_le n _ c h

private lemma bnd_lint_Ioo (n : ℕ) (a b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ u ∈ Set.Ioo a b, (W n u : ℝ) / u ≤ c) :
    (∫⁻ u in Set.Ioo a b, ENNReal.ofReal ((W n u : ℝ) / u)) ≤ ENNReal.ofReal (c * (b - a)) := by
  rw [ENNReal.ofReal_mul hc, ← Real.volume_Ioo]
  exact bnd_lint_le n _ c h

private lemma bnd_trivial (n : ℕ) (u : ℝ) (hu : 1 ≤ u) : (W n u : ℝ) / u ≤ n + 1 := by
  have h1 : (W n u : ℝ) ≤ (smallPrimes n).card := by exact_mod_cast W_le_card n u
  have h2 : (W n u : ℝ) / u ≤ W n u := div_le_self (by positivity) hu
  linarith [bnd_card_le n]

theorem outer_bound (hS : SelbergMS) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      (∫⁻ u in Set.Ico (2 * Real.sqrt n) ((n : ℝ) / 2), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (C * (Real.log n) ^ 5) := by
  classical
  obtain ⟨Cb, Z, hCb, hZ, hblock⟩ := block hS
  set N0 : ℝ := 16 * Z ^ 2 with hN0
  have hN0p : 0 ≤ N0 := by positivity
  refine ⟨(N0 + 1) * N0 + 1 + 4 * Cb + 2 * Z ^ 2, by positivity, ?_⟩
  intro n hn
  have hL : 1 < Real.log n := bnd_one_lt_log hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set L := Real.log n with hLdef
  set X := Real.sqrt n with hXdef
  have hX2 : X ^ 2 = n := Real.sq_sqrt (by linarith)
  have hX1 : 1 ≤ X := Real.one_le_sqrt.mpr (by linarith)
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL.le
  have hL5 : 1 ≤ L ^ 5 := one_le_pow₀ hL.le
  have hZ0 : 0 < Z := by linarith
  have hA : 0 ≤ (N0 + 1) * N0 + 1 := by positivity
  by_cases hsmall : (n : ℝ) < N0
  · have hXn : X ≤ n := by nlinarith
    calc (∫⁻ u in Set.Ico (2 * X) ((n : ℝ) / 2), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal ((n + 1) * ((n : ℝ) / 2 - 2 * X)) :=
          bnd_lint_Ico n _ _ _ (by positivity) (fun u hu => bnd_trivial n u (by linarith [hu.1]))
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have e1 : ((n : ℝ) + 1) * ((n : ℝ) / 2 - 2 * X) ≤ ((n : ℝ) + 1) * n :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have e2 : ((n : ℝ) + 1) * n ≤ (N0 + 1) * N0 :=
            mul_le_mul (by linarith) hsmall.le (by positivity) (by positivity)
          have e3 : (N0 + 1) * N0 + 1 + 4 * Cb + 2 * Z ^ 2 ≤
              ((N0 + 1) * N0 + 1 + 4 * Cb + 2 * Z ^ 2) * L ^ 5 :=
            le_mul_of_one_le_right (by positivity) hL5
          nlinarith
  · replace hsmall := not_lt.mp hsmall
    have hX4 : 4 * Z ≤ X := by nlinarith
    set U : ℕ → ℝ := fun m => 2 ^ (m + 1) * X with hU
    have hU0 : ∀ m, 0 ≤ U m := fun m => by simp only [hU]; positivity
    have hUs : ∀ m, U (m + 1) = 2 * U m := fun m => by simp only [hU]; ring
    have hblk : ∀ m, 2 * U m * Z ≤ n →
        (∫⁻ u in Set.Icc (U m) (2 * U m), ENNReal.ofReal ((W n u : ℝ) / u))
          ≤ ENNReal.ofReal (2 * Cb * L ^ 4) := by
      intro m hm
      have hXU : X ≤ U m := by
        simp only [hU]
        exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
      have hXU2 : X + 1 / 2 * U m ≤ U m := by
        have : X ≤ 2 ^ m * X := le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
        simp only [hU]
        rw [pow_succ]
        linarith
      have := hblock n (U m) (U m) (1 / 2) hXU hm le_rfl hXU2 (by norm_num) (by norm_num)
      rw [← hLdef] at this
      refine this.trans (le_of_eq ?_)
      congr 1
      field_simp
    have key : ∀ m : ℕ, 2 * U m * Z ≤ n →
        (∫⁻ u in Set.Icc (2 * X) (2 * U m), ENNReal.ofReal ((W n u : ℝ) / u))
          ≤ ENNReal.ofReal ((m + 1) * (2 * Cb * L ^ 4)) := by
      intro m
      induction m with
      | zero =>
        intro h
        have e : 2 * X = U 0 := by simp only [hU]; ring
        rw [e]
        refine (hblk 0 h).trans (le_of_eq ?_)
        congr 1
        push_cast
        ring
      | succ m ih =>
        intro h
        have h' : 2 * U m * Z ≤ n := by
          rw [hUs] at h
          nlinarith [hU0 m]
        have hsub : Set.Icc (2 * X) (2 * U (m + 1)) ⊆
            Set.Icc (2 * X) (2 * U m) ∪ Set.Icc (U (m + 1)) (2 * U (m + 1)) := by
          intro u hu
          rcases le_or_gt u (2 * U m) with h1 | h1
          · exact Or.inl ⟨hu.1, h1⟩
          · exact Or.inr ⟨by rw [hUs]; exact h1.le, hu.2⟩
        calc (∫⁻ u in Set.Icc (2 * X) (2 * U (m + 1)), ENNReal.ofReal ((W n u : ℝ) / u))
            ≤ ∫⁻ u in Set.Icc (2 * X) (2 * U m) ∪ Set.Icc (U (m + 1)) (2 * U (m + 1)),
                ENNReal.ofReal ((W n u : ℝ) / u) := lintegral_mono_set hsub
          _ ≤ (∫⁻ u in Set.Icc (2 * X) (2 * U m), ENNReal.ofReal ((W n u : ℝ) / u)) +
                ∫⁻ u in Set.Icc (U (m + 1)) (2 * U (m + 1)), ENNReal.ofReal ((W n u : ℝ) / u) :=
              lintegral_union_le _ _ _
          _ ≤ ENNReal.ofReal ((m + 1) * (2 * Cb * L ^ 4)) + ENNReal.ofReal (2 * Cb * L ^ 4) :=
              add_le_add (ih h') (hblk (m + 1) h)
          _ = ENNReal.ofReal ((((m + 1 : ℕ) : ℝ) + 1) * (2 * Cb * L ^ 4)) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              push_cast
              ring
    set P : ℕ → Prop := fun m => 2 * U m * Z ≤ n with hP
    have hPk : ∀ k, P k → (2 : ℝ) ^ (k + 2) ≤ n := by
      intro k hk
      simp only [hP, hU] at hk
      have e : 2 * (2 ^ (k + 1) * X) * Z = 2 ^ (k + 2) * Z * X := by ring
      rw [e, ← hX2] at hk
      have h1 : (2 : ℝ) ^ (k + 2) * Z ≤ X := by nlinarith
      have h2 : (2 : ℝ) ^ (k + 2) ≤ (2 : ℝ) ^ (k + 2) * Z := le_mul_of_one_le_right (by positivity) (by linarith)
      nlinarith
    have hP0 : P 0 := by
      simp only [hP, hU]
      rw [← hX2]
      have : 4 * Z * X ≤ X * X := mul_le_mul_of_nonneg_right hX4 (by linarith)
      have e : 2 * (2 ^ (0 + 1) * X) * Z = 4 * Z * X := by ring
      rw [e, sq]
      exact this
    set ms := Nat.findGreatest P n with hms
    have hPms : P ms := Nat.findGreatest_spec (Nat.zero_le n) hP0
    have hms2 : (2 : ℝ) ^ (ms + 2) ≤ n := hPk ms hPms
    have hmsn : ms + 1 ≤ n := by
      have h1 : ms + 2 < 2 ^ (ms + 2) := Nat.lt_two_pow_self
      have h2 : ((ms + 2 : ℕ) : ℝ) < n := by
        calc ((ms + 2 : ℕ) : ℝ) < ((2 ^ (ms + 2) : ℕ) : ℝ) := by exact_mod_cast h1
          _ = (2 : ℝ) ^ (ms + 2) := by push_cast; ring
          _ ≤ n := hms2
      have h3 : ms + 2 < n := by exact_mod_cast h2
      omega
    have hnotP : ¬ P (ms + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self ms) hmsn
    have hmsL : ((ms : ℝ) + 1) ≤ 2 * L := by
      have h1 := Real.log_le_log (by positivity) hms2
      rw [Real.log_pow] at h1
      have h2 := Real.log_two_gt_d9
      push_cast at h1
      have h3 : 0 ≤ ((ms : ℝ) + 2) * (Real.log 2 - 1 / 2) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith
    have hlow : (n : ℝ) < 2 * Z * (2 * U ms) := by
      simp only [hP, not_le] at hnotP
      rw [hUs] at hnotP
      linarith
    have hn0 : (0 : ℝ) < n := by linarith
    have hsub : Set.Ico (2 * X) ((n : ℝ) / 2) ⊆
        Set.Icc (2 * X) (2 * U ms) ∪ Set.Ioo (2 * U ms) ((n : ℝ) / 2) := by
      intro u hu
      rcases le_or_gt u (2 * U ms) with h1 | h1
      · exact Or.inl ⟨hu.1, h1⟩
      · exact Or.inr ⟨h1, hu.2⟩
    have htail : (∫⁻ u in Set.Ioo (2 * U ms) ((n : ℝ) / 2), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (2 * Z ^ 2) := by
      refine (bnd_lint_Ioo n _ _ (4 * Z ^ 2 / n) (by positivity) ?_).trans ?_
      · intro u hu
        have hu0 : 0 < u := lt_of_le_of_lt (by linarith [hU0 ms]) hu.1
        have hnu : (n : ℝ) < 2 * Z * u := by nlinarith [hu.1]
        have hW1 : (W n u : ℝ) ≤ piR (n / u) := W_le_piR n u hu0
        have hW2 : piR ((n : ℝ) / u) ≤ (n : ℝ) / u := by
          unfold piR
          have := bnd_primeCounting_le ⌊(n : ℝ) / u⌋₊
          calc (Nat.primeCounting ⌊(n : ℝ) / u⌋₊ : ℝ) ≤ (⌊(n : ℝ) / u⌋₊ : ℝ) := by
                exact_mod_cast this
            _ ≤ (n : ℝ) / u := Nat.floor_le (by positivity)
        have hW3 : (n : ℝ) / u ≤ 2 * Z := by
          rw [div_le_iff₀ hu0]
          linarith
        have hW0 : (0 : ℝ) ≤ W n u := by positivity
        rw [div_le_div_iff₀ hu0 hn0]
        nlinarith
      · apply ENNReal.ofReal_le_ofReal
        have e : 4 * Z ^ 2 / n * ((n : ℝ) / 2 - 2 * U ms) = 2 * Z ^ 2 - 8 * Z ^ 2 * U ms / n := by
          field_simp
          ring
        rw [e]
        have : 0 ≤ 8 * Z ^ 2 * U ms / n := by have := hU0 ms; positivity
        linarith
    calc (∫⁻ u in Set.Ico (2 * X) ((n : ℝ) / 2), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ∫⁻ u in Set.Icc (2 * X) (2 * U ms) ∪ Set.Ioo (2 * U ms) ((n : ℝ) / 2),
            ENNReal.ofReal ((W n u : ℝ) / u) := lintegral_mono_set hsub
      _ ≤ (∫⁻ u in Set.Icc (2 * X) (2 * U ms), ENNReal.ofReal ((W n u : ℝ) / u)) +
            ∫⁻ u in Set.Ioo (2 * U ms) ((n : ℝ) / 2), ENNReal.ofReal ((W n u : ℝ) / u) :=
          lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal ((ms + 1) * (2 * Cb * L ^ 4)) + ENNReal.ofReal (2 * Z ^ 2) :=
          add_le_add (key ms hPms) htail
      _ = ENNReal.ofReal ((ms + 1) * (2 * Cb * L ^ 4) + 2 * Z ^ 2) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have e1 : ((ms : ℝ) + 1) * (2 * Cb * L ^ 4) ≤ 2 * L * (2 * Cb * L ^ 4) :=
            mul_le_mul_of_nonneg_right hmsL (by positivity)
          have e2 : 2 * Z ^ 2 ≤ 2 * Z ^ 2 * L ^ 5 := le_mul_of_one_le_right (by positivity) hL5
          have e3 : 0 ≤ ((N0 + 1) * N0 + 1) * L ^ 5 := by positivity
          have e4 : 2 * L * (2 * Cb * L ^ 4) = 4 * Cb * L ^ 5 := by ring
          nlinarith

private lemma bnd_ineq1 (Cv q r T : ℝ) (hCv : 0 ≤ Cv) (hq1 : 1 ≤ q) (hr1 : 1 ≤ r)
    (hTq : T * q = r ^ 3) :
    (2 + 4 * (3 * Cv * q ^ 2 * r ^ 2)) * T ≤ (2 + 12 * Cv) * q * r ^ 5 := by
  have hq0 : 0 < q := by linarith
  have hq2r2 : 1 ≤ q ^ 2 * r ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1) (one_le_pow₀ hr1)
  have h5 : r ^ 3 * 1 ≤ r ^ 3 * (q ^ 2 * r ^ 2) :=
    mul_le_mul_of_nonneg_left hq2r2 (by positivity)
  have h6 : 0 ≤ Cv * q ^ 2 * r ^ 5 := by positivity
  apply le_of_mul_le_mul_right _ hq0
  rw [mul_assoc, hTq]
  linarith

private lemma bnd_inner_large (n : ℕ) (Cb Cv Z : ℝ) (hCb : 0 ≤ Cb) (hCv : 0 ≤ Cv) (hZ : 30 ≤ Z)
    (hblock : ∀ (U a β : ℝ), Real.sqrt n ≤ U → 2 * U * Z ≤ n →
      U ≤ a → Real.sqrt n + β * U ≤ a → 0 < β → β ≤ 1 →
      (∫⁻ u in Set.Icc a (2 * U), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (Cb * (Real.log n) ^ 4 / β))
    (hE : ∀ y : ℝ, 2 ≤ y → |E y| ≤ Cv * Real.sqrt y * Real.log y)
    (hn : 3600 + 4 * Z ^ 2 ≤ (n : ℝ)) (q r : ℝ) (hq1 : 1 ≤ q) (hq4 : q ^ 4 = Real.sqrt n)
    (hr1 : 1 ≤ r) (hr2 : r ^ 2 = Real.log n) :
    (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ENNReal.ofReal ((2 + 12 * Cv + Cb) * q * r ^ 5) := by
  set L := Real.log n with hLdef
  set X := Real.sqrt n with hXdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hX2 : X ^ 2 = n := Real.sq_sqrt hn0
  have hq0 : 0 < q := by linarith
  have hZ0 : 0 < Z := by linarith
  have hn3600 : 3600 ≤ n := by
    have : (3600 : ℝ) ≤ n := by linarith [sq_nonneg Z]
    exact_mod_cast this
  have hX60 : 60 ≤ X := (Real.le_sqrt (by norm_num) hn0).mpr (by linarith [sq_nonneg Z])
  have hX2Z : 2 * Z ≤ X := (Real.le_sqrt (by linarith) hn0).mpr (by linarith)
  have hX0 : 0 < X := by linarith
  have hXX : ∀ c : ℝ, c ≤ X → c * X ≤ n := fun c hc => by
    rw [← hX2, sq]
    exact mul_le_mul_of_nonneg_right hc hX0.le
  have h8X : 8 * X ≤ n := by
    have := hXX 8 (by linarith)
    linarith
  have hq2 : Real.sqrt X = q ^ 2 := by
    rw [← hq4, show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  set B := 3 * Cv * q ^ 2 * L with hBdef
  have hB : ∀ y : ℝ, X / 8 ≤ y → y ≤ 8 * X → |E y| ≤ B := by
    intro y hy1 hy2
    have hy : 2 ≤ y := by linarith
    have h1 := hE y hy
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hs : Real.sqrt y ≤ 3 * q ^ 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (3 * q ^ 2) ^ 2 = 9 * X := by rw [← hq4]; ring
      rw [this]
      linarith
    have hl : Real.log y ≤ L := Real.log_le_log (by linarith) (by linarith)
    have h3 : Cv * Real.sqrt y * Real.log y ≤ Cv * (3 * q ^ 2) * L :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs hCv) hl hl0 (by positivity)
    rw [hBdef]
    linarith
  have hW : ∀ u : ℝ, X ≤ u → u ≤ 2 * X → (W n u : ℝ) ≤ 2 + 4 * B :=
    fun u hu1 hu2 => W_le_of_abs_E_le n u hn3600 hu1 hu2 B hB
  have hB0 : 0 ≤ B := by rw [hBdef, ← hr2]; positivity
  set T := r ^ 3 / q with hTdef
  have hT0 : 0 < T := by rw [hTdef]; positivity
  have hTq : T * q = r ^ 3 := by rw [hTdef]; field_simp
  set a := X * (1 + T) with hadef
  have hsub : Set.Ico X (2 * X) ⊆ Set.Ico X (min a (2 * X)) ∪ Set.Icc a (2 * X) := by
    intro u hu
    rcases lt_or_ge u a with h1 | h1
    · exact Or.inl ⟨hu.1, lt_min h1 hu.2⟩
    · exact Or.inr ⟨h1, hu.2.le⟩
  have hp1 : (∫⁻ u in Set.Ico X (min a (2 * X)), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ENNReal.ofReal ((2 + 12 * Cv) * q * r ^ 5) := by
    refine (bnd_lint_Ico n _ _ ((2 + 4 * B) / X) (by positivity) ?_).trans ?_
    · intro u hu
      have hu1 : X ≤ u := hu.1
      have hu2 : u ≤ 2 * X := (lt_of_lt_of_le hu.2 (min_le_right _ _)).le
      have hWu := hW u hu1 hu2
      have hu0 : 0 < u := by linarith
      calc (W n u : ℝ) / u ≤ (2 + 4 * B) / u := div_le_div_of_nonneg_right hWu hu0.le
        _ ≤ (2 + 4 * B) / X := div_le_div_of_nonneg_left (by positivity) hX0 hu1
    · apply ENNReal.ofReal_le_ofReal
      have hlen : min a (2 * X) - X ≤ X * T := by
        have := min_le_left a (2 * X)
        rw [hadef] at this
        linarith
      have e1 : (2 + 4 * B) / X * (min a (2 * X) - X) ≤ (2 + 4 * B) / X * (X * T) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      have e2 : (2 + 4 * B) / X * (X * T) = (2 + 4 * B) * T := by field_simp
      have e5 : (2 + 4 * B) * T ≤ (2 + 12 * Cv) * q * r ^ 5 := by
        have := bnd_ineq1 Cv q r T hCv hq1 hr1 hTq
        rw [hBdef, ← hr2]
        exact this
      linarith
  have hp2 : (∫⁻ u in Set.Icc a (2 * X), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ENNReal.ofReal (Cb * q * r ^ 5) := by
    by_cases hT1 : T ≤ 1
    · have hXa : X ≤ a := by
        rw [hadef]
        have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + T by linarith) hX0.le
        linarith
      have hXa2 : X + T * X ≤ a := by rw [hadef]; linarith
      have h2XZ : 2 * X * Z ≤ n := by
        have := hXX (2 * Z) hX2Z
        linarith
      have := hblock X a T le_rfl h2XZ hXa hXa2 hT0 hT1
      refine this.trans (le_of_eq ?_)
      congr 1
      rw [← hr2, div_eq_iff hT0.ne']
      calc Cb * (r ^ 2) ^ 4 = Cb * r ^ 5 * r ^ 3 := by ring
        _ = Cb * r ^ 5 * (T * q) := by rw [hTq]
        _ = Cb * q * r ^ 5 * T := by ring
    · have hemp : Set.Icc a (2 * X) = ∅ := by
        apply Set.Icc_eq_empty
        rw [hadef, not_le]
        have := mul_lt_mul_of_pos_left (show (2 : ℝ) < 1 + T by linarith [not_le.mp hT1]) hX0
        linarith
      rw [hemp]
      simp
  calc (∫⁻ u in Set.Ico X (2 * X), ENNReal.ofReal ((W n u : ℝ) / u))
      ≤ ∫⁻ u in Set.Ico X (min a (2 * X)) ∪ Set.Icc a (2 * X),
          ENNReal.ofReal ((W n u : ℝ) / u) := lintegral_mono_set hsub
    _ ≤ (∫⁻ u in Set.Ico X (min a (2 * X)), ENNReal.ofReal ((W n u : ℝ) / u)) +
          ∫⁻ u in Set.Icc a (2 * X), ENNReal.ofReal ((W n u : ℝ) / u) :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal ((2 + 12 * Cv) * q * r ^ 5) + ENNReal.ofReal (Cb * q * r ^ 5) :=
        add_le_add hp1 hp2
    _ = ENNReal.ofReal ((2 + 12 * Cv) * q * r ^ 5 + Cb * q * r ^ 5) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ = ENNReal.ofReal ((2 + 12 * Cv + Cb) * q * r ^ 5) := by ring_nf

theorem inner_bound (hV : VonKoch) (hS : SelbergMS) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (1 / 8 : ℝ) * (Real.log n) ^ (5 / 2 : ℝ)) := by
  obtain ⟨Cb, Z, hCb, hZ, hblock⟩ := block hS
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
  set N0 : ℝ := 3600 + 4 * Z ^ 2 with hN0
  have hN0p : 0 ≤ N0 := by positivity
  refine ⟨(N0 + 1) * N0 + 1 + (2 + 12 * Cv + Cb), by positivity, ?_⟩
  intro n hn
  have hL : 1 < Real.log n := bnd_one_lt_log hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hq1 : 1 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hq4 : ((n : ℝ) ^ (1 / 8 : ℝ)) ^ 4 = Real.sqrt n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
    norm_num
  have hL52 : (Real.log n) ^ (5 / 2 : ℝ) = (Real.sqrt (Real.log n)) ^ 5 := by
    rw [show (5 / 2 : ℝ) = 1 / 2 * ((5 : ℕ) : ℝ) by norm_num, Real.rpow_mul (by linarith),
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hr2 : (Real.sqrt (Real.log n)) ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hr1 : 1 ≤ Real.sqrt (Real.log n) := Real.one_le_sqrt.mpr hL.le
  rw [hL52]
  set q := (n : ℝ) ^ (1 / 8 : ℝ) with hqdef
  set r := Real.sqrt (Real.log n) with hrdef
  have hqr : 1 ≤ q * r ^ 5 := one_le_mul_of_one_le_of_one_le hq1 (one_le_pow₀ hr1)
  have hq0 : 0 < q := by linarith
  have hA : 0 ≤ (N0 + 1) * N0 + 1 := by positivity
  have e4 : ((N0 + 1) * N0 + 1 + (2 + 12 * Cv + Cb)) * q * r ^ 5 =
      ((N0 + 1) * N0 + 1) * (q * r ^ 5) + (2 + 12 * Cv + Cb) * q * r ^ 5 := by ring
  rw [e4]
  by_cases hsmall : (n : ℝ) < N0
  · have hX2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by linarith)
    have hX1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
    have hXn : Real.sqrt n ≤ n := by
      have := mul_le_mul_of_nonneg_left hX1 (Real.sqrt_nonneg (n : ℝ))
      rw [Real.mul_self_sqrt (by linarith)] at this
      linarith
    calc (∫⁻ u in Set.Ico (Real.sqrt n) (2 * Real.sqrt n), ENNReal.ofReal ((W n u : ℝ) / u))
        ≤ ENNReal.ofReal ((n + 1) * (2 * Real.sqrt n - Real.sqrt n)) :=
          bnd_lint_Ico n _ _ _ (by positivity) (fun u hu => bnd_trivial n u (by linarith [hu.1]))
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have e1 : ((n : ℝ) + 1) * (2 * Real.sqrt n - Real.sqrt n) ≤ ((n : ℝ) + 1) * n :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have e2 : ((n : ℝ) + 1) * n ≤ (N0 + 1) * N0 :=
            mul_le_mul (by linarith) hsmall.le (by positivity) (by positivity)
          have e3 : (N0 + 1) * N0 + 1 ≤ ((N0 + 1) * N0 + 1) * (q * r ^ 5) :=
            le_mul_of_one_le_right hA hqr
          have e5 : 0 ≤ (2 + 12 * Cv + Cb) * q * r ^ 5 := by positivity
          linarith
  · have h := bnd_inner_large n Cb Cv Z hCb.le hCv hZ (fun U a β => hblock n U a β) hE
      (not_lt.mp hsmall) q r hq1 hq4 hr1 hr2
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ ((N0 + 1) * N0 + 1) * (q * r ^ 5) := by positivity
    linarith

end Erdos879
