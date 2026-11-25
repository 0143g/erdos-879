import Mathlib
import Erdos879.DoublingCheb
import Erdos879.DoublingSmall

namespace Erdos879

namespace DoublingAux

open Real Chebyshev Erdos879.DoublingCheb Erdos879.DoublingSmall

lemma primeCounting_le_third (n : ℕ) : (Nat.primeCounting n : ℝ) ≤ n / 3 + 3 := by
  have h6 : Nat.primeCounting 6 = 3 := by
    rw [primeCounting_eq_cnt]
    decide +kernel
  rcases lt_or_ge n 6 with h | h
  · have h1 : Nat.primeCounting n ≤ 3 := h6 ▸ Nat.monotone_primeCounting h.le
    have h2 : (Nat.primeCounting n : ℝ) ≤ 3 := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ n / 3 := by positivity
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = 6 + k := ⟨n - 6, by omega⟩
    have hb := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl k
    have ht : Nat.totient 6 = 2 := by decide
    rw [h6, ht] at hb
    have hb' : (Nat.primeCounting (6 + k) : ℝ) ≤ 3 + 2 * ((k / 6 : ℕ) + 1 : ℝ) := by
      exact_mod_cast hb
    have hd : ((k / 6 : ℕ) : ℝ) ≤ (k : ℝ) / 6 := Nat.cast_div_le
    push_cast
    linarith

theorem large_case (m : ℕ) (hm : 4096 ≤ m) :
    2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m) := by
  have hx : (4096 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set x : ℝ := (m : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  set r : ℝ := x ^ ((1 : ℝ) / 3) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos hx0 _
  have hr3 : r ^ 3 = x := by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hr16 : 16 ≤ r := by
    by_contra h
    have h' : r < 16 := lt_of_not_ge h
    have : r ^ 3 < 16 ^ 3 := by gcongr
    linarith
  set s : ℝ := √x with hsdef
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hs64 : 64 ≤ s := by
    rw [hsdef]
    exact (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith)
  set L : ℝ := log r with hLdef
  have hlogx : log x = 3 * L := by
    rw [← hr3, Real.log_pow]
    push_cast
    ring
  have hlog16 : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hL1 : 4 * log 2 ≤ L := by
    rw [← hlog16]
    exact Real.log_le_log (by norm_num) hr16
  have hL2 : L ≤ log 2 / 4 * r := by
    have he : Real.exp 1 ≤ 16 := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he)
      (Set.mem_Ici.mpr (he.trans hr16)) hr16
    simp only at h
    rw [div_le_div_iff₀ hr0 (by norm_num), hlog16] at h
    linarith
  have hlog4x : log (4 * x) = 2 * log 2 + 3 * L := by
    rw [Real.log_mul (by norm_num) hx0.ne', hlogx, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hpsi4 := psi_lower (4 * x) (by linarith)
  have htheta4 := psi_sub_le_theta (4 * x) (by linarith)
  have hsq4 : √(4 * x) = 2 * s := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsq4] at htheta4
  rw [hlog4x] at hpsi4
  have hthx : θ x ≤ 1.15 * x := (theta_le_psi x).trans (psi_le_clean x hx0.le)
  have hD := (theta_sub_bounds m 0 (log (4 * x)) (4 * m) (by omega)
    (fun p hp _ h2 => ⟨Real.log_nonneg (by exact_mod_cast hp.one_lt.le),
      Real.log_le_log (by exact_mod_cast hp.pos) (by
        have : (p : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast h2
        push_cast at this
        exact this)⟩)).2
  push_cast at hD
  rw [← hxdef, hlog4x] at hD
  set y : ℕ := ⌊r ^ 2⌋₊ with hydef
  have f2 : r ^ 2 ≤ x / 16 := by
    have h1 := mul_le_mul_of_nonneg_right hr16 (sq_nonneg r)
    have h2 : r * r ^ 2 = x := by rw [← hr3]; ring
    linarith
  have hr2x : r ^ 2 ≤ x := by linarith
  have hym : y ≤ m := by
    have := Nat.floor_le_floor hr2x
    rwa [hxdef, Nat.floor_natCast] at this
  have hP := (theta_sub_bounds y (log (r ^ 2)) (log x) m hym
    (fun p hp h1 h2 => ⟨Real.log_le_log (by positivity) (Nat.lt_of_floor_lt h1).le,
      Real.log_le_log (by exact_mod_cast hp.pos) (by rw [hxdef]; exact_mod_cast h2)⟩)).1
  have hθy : 0 ≤ θ (y : ℝ) := theta_nonneg _
  have hlogr2 : log (r ^ 2) = 2 * L := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogr2] at hP
  have hQ : (Nat.primeCounting y : ℝ) ≤ r ^ 2 / 3 + 3 := by
    refine (primeCounting_le_third y).trans ?_
    have := Nat.floor_le (sq_nonneg r)
    linarith
  have ha := a_bound
  simp only [Set.mem_Icc] at ha
  set P : ℝ := (Nat.primeCounting m : ℝ) with hPdef
  set Q : ℝ := (Nat.primeCounting y : ℝ) with hQdef
  set D : ℝ := (Nat.primeCounting (4 * m) : ℝ) - P with hDdef
  have hA : (P - Q) * (2 * L) ≤ 1.15 * x := by linarith
  have hB : (P - Q) * (8 * log 2) ≤ 1.15 * x := by
    rcases le_or_gt (P - Q) 0 with h | h
    · have : (P - Q) * (8 * log 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (by linarith)
      linarith
    · have : (P - Q) * (8 * log 2) ≤ (P - Q) * (2 * L) := by
        apply mul_le_mul_of_nonneg_left _ h.le
        linarith
      linarith
  have hPl : P * (2 * log 2 + 3 * L) ≤ Q * (2 * log 2 + 3 * L) + 2.0125 * x := by
    have he : P * (2 * log 2 + 3 * L) = Q * (2 * log 2 + 3 * L) + (P - Q) * (8 * log 2) / 4 +
        (P - Q) * (2 * L) * (3 / 2) := by ring
    rw [he]
    linarith
  have f1 : L * r ^ 2 ≤ 0.693148 / 4 * x := by
    have h0 : L ≤ 0.693148 / 4 * r := by
      have : log 2 / 4 * r ≤ 0.693148 / 4 * r :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
      linarith
    have h1 := mul_le_mul_of_nonneg_right h0 (sq_nonneg r)
    have h2 : 0.693148 / 4 * r * r ^ 2 = 0.693148 / 4 * x := by rw [← hr3]; ring
    linarith
  have f3 : log 2 * r ^ 2 ≤ 0.693148 * (x / 16) := by
    have h1 : log 2 * r ^ 2 ≤ 0.693148 * r ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)
    linarith
  have f4 : r ≤ x / 256 := by
    have h1 : (16 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num) hr16 2
    have h2 := mul_le_mul_of_nonneg_right h1 hr0.le
    have h3 : r ^ 2 * r = x := by rw [← hr3]; ring
    linarith
  have f5 : L ≤ 0.693148 / 4 * (x / 256) := by
    have : log 2 / 4 * r ≤ 0.693148 / 4 * r :=
      mul_le_mul_of_nonneg_right (by linarith) hr0.le
    linarith
  have f6 : 0.92129 * x ≤ a * x := mul_le_mul_of_nonneg_right ha.1 hx0.le
  have f7 : s ≤ x / 64 := by
    have h1 := mul_le_mul_of_nonneg_right hs64 hs0
    have h2 : s * s = x := by rw [← hs2]; ring
    linarith
  have hQl : Q * (2 * log 2 + 3 * L) ≤ (r ^ 2 / 3 + 3) * (2 * log 2 + 3 * L) :=
    mul_le_mul_of_nonneg_right hQ (by linarith)
  have hDl : 4 * a * x - 5 * (2 * log 2 + 3 * L) + 5 - 3.45 * (2 * s) - 1.15 * x ≤
      D * (2 * log 2 + 3 * L) := by
    linarith
  have hexp : (r ^ 2 / 3 + 3) * (2 * log 2 + 3 * L) =
      (2 / 3) * (log 2 * r ^ 2) + 6 * log 2 + L * r ^ 2 + 9 * L := by ring
  have hfin : P * (2 * log 2 + 3 * L) ≤ D * (2 * log 2 + 3 * L) := by
    linarith
  have hPD : P ≤ D := le_of_mul_le_mul_right hfin (by linarith)
  have : (2 * Nat.primeCounting m : ℝ) ≤ Nat.primeCounting (4 * m) := by linarith
  exact_mod_cast this

end DoublingAux

theorem two_mul_primeCounting_le (m : ℕ) :
    2 * Nat.primeCounting m ≤ Nat.primeCounting (4 * m) := by
  rcases le_or_gt m 4096 with h | h
  · exact DoublingSmall.small_case m h
  · exact DoublingAux.large_case m h.le

end Erdos879
