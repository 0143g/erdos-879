import Mathlib

namespace Erdos879.DoublingSmall

noncomputable def tdAux (n f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih d => Nat.blt n (d * d) || (!(Nat.beq (n % d) 0) && ih (d + 2))) f

lemma tdAux_zero (n d : ℕ) : tdAux n 0 d = true := rfl

lemma tdAux_succ (n f d : ℕ) :
    tdAux n (f + 1) d = (Nat.blt n (d * d) || (!(Nat.beq (n % d) 0) && tdAux n f (d + 2))) := rfl

lemma tdAux_spec (n : ℕ) : ∀ f d, n < (d + 2 * f) * (d + 2 * f) →
    (tdAux n f d = true ↔ ∀ k, d ≤ k → k % 2 = d % 2 → k * k ≤ n → n % k ≠ 0) := by
  intro f
  induction f with
  | zero =>
    intro d hd
    simp only [Nat.mul_zero, Nat.add_zero] at hd
    simp only [tdAux_zero, true_iff]
    intro k hk _ hkn
    exfalso
    have : d * d ≤ k * k := Nat.mul_le_mul hk hk
    omega
  | succ f ih =>
    intro d hd
    rw [tdAux_succ]
    by_cases hlt : n < d * d
    · have : Nat.blt n (d * d) = true := Nat.blt_eq.mpr hlt
      simp only [this, Bool.true_or, true_iff]
      intro k hk _ hkn
      exfalso
      have : d * d ≤ k * k := Nat.mul_le_mul hk hk
      omega
    · have h1 : Nat.blt n (d * d) = false :=
        Bool.eq_false_iff.mpr (fun h => hlt (Nat.blt_eq.mp h))
      have ih' := ih (d + 2) (by
        have : d + 2 + 2 * f = d + 2 * (f + 1) := by ring
        rw [this]
        exact hd)
      simp only [h1, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true', ih']
      constructor
      · rintro ⟨hb, hrest⟩ k hk hpar hkn
        rcases Nat.eq_or_lt_of_le hk with heq | hlt'
        · subst heq
          intro h0
          have : Nat.beq (n % d) 0 = true := Nat.beq_eq.mpr h0
          simp [this] at hb
        · exact hrest k (by omega) (by omega) hkn
      · intro h
        refine ⟨?_, fun k hk hpar hkn => h k (by omega) (by omega) hkn⟩
        have := h d le_rfl rfl (by omega)
        cases hb : Nat.beq (n % d) 0
        · rfl
        · exact absurd (Nat.beq_eq.mp hb) this

noncomputable def isPrimeB (n : ℕ) : Bool :=
  Nat.blt 1 n && (Nat.blt n 4 || (!(Nat.beq (n % 2) 0) && tdAux n n 3))

lemma isPrimeB_iff (n : ℕ) : isPrimeB n = true ↔ n.Prime := by
  unfold isPrimeB
  rw [Nat.prime_def_le_sqrt]
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm2 hms hdvd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    rcases h2 with h4 | ⟨hodd, htd⟩
    · nlinarith
    · have hodd' : n % 2 ≠ 0 := by
        intro h0
        have : Nat.beq (n % 2) 0 = true := Nat.beq_eq.mpr h0
        simp [this] at hodd
      have hspec := (tdAux_spec n n 3 (by nlinarith)).mp htd
      have hm2' : m % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one m with h | h
        · exfalso
          apply hodd'
          exact Nat.mod_eq_zero_of_dvd (dvd_trans (Nat.dvd_of_mod_eq_zero h) hdvd)
        · exact h
      have hm3 : 3 ≤ m := by omega
      exact hspec m hm3 (by omega) hmm (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases h4 : n < 4
    · exact Or.inl h4
    · right
      have h2n : ¬ 2 ∣ n := fun hd => h2 2 le_rfl (Nat.le_sqrt.mpr (by omega)) hd
      refine ⟨?_, ?_⟩
      · cases hb : Nat.beq (n % 2) 0
        · rfl
        · exact absurd (Nat.dvd_of_mod_eq_zero (Nat.beq_eq.mp hb)) h2n
      · rw [tdAux_spec n n 3 (by nlinarith)]
        intro k hk _ hkn hmod
        exact h2 k (by omega) (Nat.le_sqrt.mpr hkn) (Nat.dvd_of_mod_eq_zero hmod)

noncomputable def cnt (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => cond (isPrimeB j) (ih + 1) ih) k

lemma cnt_eq_count (k : ℕ) : cnt k = Nat.count Nat.Prime k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.count_succ, ← ih]
    show cond (isPrimeB k) (cnt k + 1) (cnt k) = _
    by_cases hk : k.Prime
    · have : isPrimeB k = true := (isPrimeB_iff k).mpr hk
      simp [this, hk]
    · have : isPrimeB k = false := by
        cases h : isPrimeB k
        · rfl
        · exact absurd ((isPrimeB_iff k).mp h) hk
      simp [this, hk]

lemma primeCounting_eq_cnt (n : ℕ) : Nat.primeCounting n = cnt (n + 1) := by
  rw [cnt_eq_count]
  rfl

noncomputable def gridOK : List ℕ → Bool
  | g :: g' :: rest => Nat.ble (2 * cnt (g' + 1)) (cnt (4 * g + 1)) && gridOK (g' :: rest)
  | _ => true

lemma pair_spec (g g' m : ℕ) (h : 2 * cnt (g' + 1) ≤ cnt (4 * g + 1)) (h1 : g ≤ m) (h2 : m ≤ g') :
    2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m) := by
  rw [← primeCounting_eq_cnt, ← primeCounting_eq_cnt] at h
  calc 2 * Nat.primeCounting m ≤ 2 * Nat.primeCounting g' := by
        gcongr
        exact Nat.monotone_primeCounting h2
    _ ≤ Nat.primeCounting (4 * g) := h
    _ ≤ Nat.primeCounting (4 * m) := Nat.monotone_primeCounting (by omega)

lemma gridOK_spec : ∀ (l : List ℕ) (g g' : ℕ), gridOK (g :: g' :: l) = true →
    ∀ m, g ≤ m → m ≤ (g' :: l).getLast (List.cons_ne_nil _ _) →
    2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m) := by
  intro l
  induction l with
  | nil =>
    intro g g' h m h1 h2
    simp only [gridOK, Bool.and_eq_true, Nat.ble_eq] at h
    exact pair_spec g g' m h.1 h1 (by simpa using h2)
  | cons g'' rest ih =>
    intro g g' h m h1 h2
    simp only [gridOK, Bool.and_eq_true, Nat.ble_eq] at h
    rcases le_or_gt m g' with hm | hm
    · exact pair_spec g g' m h.1 h1 hm
    · exact ih g' g'' (by simp only [gridOK, Bool.and_eq_true, Nat.ble_eq]; exact h.2) m hm.le
        (by simpa using h2)

theorem small_case (m : ℕ) (hm : m ≤ 4096) :
    2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m) := by
  rcases lt_or_ge m 2 with h | h
  · interval_cases m <;> simp
  have hg : gridOK [2, 4, 6, 10, 16, 28, 46, 78, 136, 232, 400, 700, 1248, 2242, 4048, 4096] = true := by
    decide +kernel
  exact gridOK_spec _ 2 4 hg m h (by simpa using hm)

end Erdos879.DoublingSmall
