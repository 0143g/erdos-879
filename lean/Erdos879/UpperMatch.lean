import Erdos879.Defs

open Finset

namespace Erdos879

def cand (n p : ℕ) (U : Finset ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun q => q.Prime ∧ n < q * q ∧ p * q ≤ n ∧ q ∉ U)

def pick (n p : ℕ) (U : Finset ℕ) : Option ℕ :=
  if h : (cand n p U).Nonempty then some ((cand n p U).max' h) else none

def used (n : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | k + 1 => if k ∈ smallPrimes n then used n k ∪ (pick n k (used n k)).toFinset else used n k

def partner (n p : ℕ) : Option ℕ := pick n p (used n p)

lemma mem_smallPrimes {n p : ℕ} : p ∈ smallPrimes n ↔ p.Prime ∧ p * p ≤ n := by
  simp only [smallPrimes, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have := h.1.two_le
    nlinarith

lemma mem_used (n k q : ℕ) :
    q ∈ used n k ↔ ∃ p' < k, p' ∈ smallPrimes n ∧ partner n p' = some q := by
  induction k with
  | zero => simp [used]
  | succ k ih =>
    by_cases hk : k ∈ smallPrimes n
    · simp only [used, hk, if_true, mem_union, ih, Option.mem_toFinset, Option.mem_def]
      constructor
      · rintro (⟨p', hp', h1, h2⟩ | h)
        · exact ⟨p', by omega, h1, h2⟩
        · exact ⟨k, by omega, hk, h⟩
      · rintro ⟨p', hp', h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with h | h
        · exact Or.inl ⟨p', h, h1, h2⟩
        · subst h
          exact Or.inr h2
    · simp only [used, hk, if_false, ih]
      constructor
      · rintro ⟨p', hp', h1, h2⟩
        exact ⟨p', by omega, h1, h2⟩
      · rintro ⟨p', hp', h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with h | h
        · exact ⟨p', h, h1, h2⟩
        · subst h
          exact absurd h1 hk

lemma partner_spec {n p q : ℕ} (h : partner n p = some q) :
    q.Prime ∧ n < q * q ∧ p * q ≤ n ∧ q ≤ n ∧
      ∀ p' < p, p' ∈ smallPrimes n → partner n p' ≠ some q := by
  unfold partner pick at h
  split_ifs at h with hne
  have hm := (cand n p (used n p)).max'_mem hne
  rw [Option.some_inj] at h
  rw [h] at hm
  simp only [cand, mem_filter, mem_range] at hm
  refine ⟨hm.2.1, hm.2.2.1, hm.2.2.2.1, by omega, ?_⟩
  intro p' hp' hP h'
  exact hm.2.2.2.2 ((mem_used n p q).2 ⟨p', hp', hP, h'⟩)

lemma partner_ge {n p q : ℕ} (hq : q.Prime) (hqq : n < q * q) (hpq : p * q ≤ n) (hqn : q ≤ n)
    (hfree : ∀ p' < p, p' ∈ smallPrimes n → partner n p' ≠ some q) :
    ∃ q', partner n p = some q' ∧ q ≤ q' := by
  have hc : q ∈ cand n p (used n p) := by
    simp only [cand, mem_filter, mem_range]
    refine ⟨by omega, hq, hqq, hpq, ?_⟩
    intro hu
    obtain ⟨p', hp', hP, h'⟩ := (mem_used n p q).1 hu
    exact hfree p' hp' hP h'
  refine ⟨(cand n p (used n p)).max' ⟨q, hc⟩, ?_, le_max' _ _ hc⟩
  unfold partner pick
  rw [dif_pos ⟨q, hc⟩]

lemma partner_inj {n p p' q : ℕ} (hp : p ∈ smallPrimes n) (hp' : p' ∈ smallPrimes n)
    (h : partner n p = some q) (h' : partner n p' = some q) : p = p' := by
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · exact absurd h ((partner_spec h').2.2.2.2 p hlt hp)
  · exact heq
  · exact absurd h' ((partner_spec h).2.2.2.2 p' hgt hp')

noncomputable def apt (n p : ℕ) : ℝ := (partner n p).elim (Real.sqrt n) (fun q => (q : ℝ))

lemma apt_some {n p q : ℕ} (h : partner n p = some q) : apt n p = q := by
  simp [apt, h]

lemma apt_none {n p : ℕ} (h : partner n p = none) : apt n p = Real.sqrt n := by
  simp [apt, h]

noncomputable def Q (n : ℕ) (x : ℝ) : Finset ℕ :=
  (smallPrimes n).filter (fun p => apt n p ≤ x ∧ x < (n : ℝ) / p)

lemma le_div_of_mul_le {n p q : ℕ} (hp : 0 < p) (h : p * q ≤ n) : (q : ℝ) ≤ (n : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hp0]
  have : ((p * q : ℕ) : ℝ) ≤ n := by exact_mod_cast h
  push_cast at this
  linarith

lemma mul_le_of_le_div {n p q : ℕ} (hp : 0 < p) (h : (q : ℝ) ≤ (n : ℝ) / p) : p * q ≤ n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hp0] at h
  have : ((p * q : ℕ) : ℝ) ≤ n := by push_cast; linarith
  exact_mod_cast this

lemma key (n : ℕ) (u : ℝ) (hu : Real.sqrt n ≤ u) :
    ∃ v, u ≤ v ∧ (Q n u).card + primesBetween u v ≤ A n u v := by
  classical
  set V : Finset ℝ := insert u ((smallPrimes n).image (fun p : ℕ => (n : ℝ) / p) ∪
    ((range (n + 1)).filter Nat.Prime).image (fun q : ℕ => (q : ℝ))) with hV
  have hVu : u ∈ V := mem_insert_self _ _
  have hVt : ∀ p ∈ smallPrimes n, (n : ℝ) / p ∈ V := by
    intro p hp
    rw [hV, mem_insert, mem_union, mem_image]
    exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
  have hVle : ∀ x ∈ V, x = u ∨ x ≤ n := by
    intro x hx
    rw [hV, mem_insert, mem_union, mem_image, mem_image] at hx
    rcases hx with h | ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl h
    · right
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_smallPrimes.1 hp).1.one_lt.le
      exact div_le_self (Nat.cast_nonneg _) h1
    · right
      simp only [mem_filter, mem_range] at hq
      exact_mod_cast (by omega : q ≤ n)
  have hV'ne : (V.filter (fun x => u ≤ x ∧ Q n x = ∅)).Nonempty := by
    refine ⟨V.max' ⟨u, hVu⟩, ?_⟩
    rw [mem_filter]
    refine ⟨max'_mem _ _, le_max' _ _ hVu, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Q, mem_filter] at hp
    have := le_max' V _ (hVt p hp.1)
    linarith [hp.2.2]
  set v := (V.filter (fun x => u ≤ x ∧ Q n x = ∅)).min' hV'ne with hvdef
  have hvV' : v ∈ V.filter (fun x => u ≤ x ∧ Q n x = ∅) := min'_mem _ _
  rw [mem_filter] at hvV'
  obtain ⟨hvV, huv, hQv⟩ := hvV'
  have hmin : ∀ x ∈ V, u ≤ x → Q n x = ∅ → v ≤ x := fun x hx h1 h2 =>
    min'_le _ _ (mem_filter.2 ⟨hx, h1, h2⟩)
  have hnotQv : ∀ p ∈ smallPrimes n, apt n p ≤ v → (n : ℝ) / p ≤ v := by
    intro p hp ha
    by_contra h
    push Not at h
    have : p ∈ Q n v := mem_filter.2 ⟨hp, ha, h⟩
    rw [hQv] at this
    exact absurd this (notMem_empty _)
  have hb : ∀ q : ℕ, q.Prime → u < q → (q : ℝ) ≤ v →
      ∃ p ∈ smallPrimes n, partner n p = some q ∧ (n : ℝ) / p ≤ v := by
    intro q hq huq hqv
    have hqn : q ≤ n := by
      rcases hVle v hvV with h | h
      · linarith
      · exact_mod_cast hqv.trans h
    have hqq : n < q * q := by
      have h1 : Real.sqrt n < q := lt_of_le_of_lt hu huq
      have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
      have h3 : (n : ℝ) < (q : ℝ) * q := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
      exact_mod_cast h3
    by_cases hused : ∃ p ∈ smallPrimes n, partner n p = some q
    · obtain ⟨p, hp, hpq⟩ := hused
      refine ⟨p, hp, hpq, hnotQv p hp ?_⟩
      rw [apt_some hpq]
      exact hqv
    · exfalso
      push Not at hused
      have hne : (V.filter (fun x : ℝ => x < (q : ℝ))).Nonempty := ⟨u, mem_filter.2 ⟨hVu, huq⟩⟩
      have hv'm := max'_mem _ hne
      rw [mem_filter] at hv'm
      have huv' : u ≤ (V.filter (fun x : ℝ => x < (q : ℝ))).max' hne :=
        le_max' _ _ (mem_filter.2 ⟨hVu, huq⟩)
      have hQv' : Q n ((V.filter (fun x : ℝ => x < (q : ℝ))).max' hne) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Q, mem_filter] at hp
        obtain ⟨hpP, hap, htp⟩ := hp
        have hqt : (q : ℝ) ≤ (n : ℝ) / p := by
          by_contra h
          push Not at h
          have := le_max' (V.filter (fun x : ℝ => x < (q : ℝ))) _ (mem_filter.2 ⟨hVt p hpP, h⟩)
          linarith
        have hpq : p * q ≤ n := mul_le_of_le_div (mem_smallPrimes.1 hpP).1.pos hqt
        obtain ⟨q', hq', hqq'⟩ := partner_ge hq hqq hpq hqn (fun p' _ hp' => hused p' hp')
        have hne' : q' ≠ q := fun h => hused p hpP (h ▸ hq')
        have : (q : ℝ) < q' := by exact_mod_cast lt_of_le_of_ne hqq' (Ne.symm hne')
        rw [apt_some hq'] at hap
        linarith [hv'm.2]
      have := hmin _ hv'm.1 huv' hQv'
      linarith [hv'm.2]
  refine ⟨v, huv, ?_⟩
  have hv0 : 0 ≤ v := (Real.sqrt_nonneg _).trans (hu.trans huv)
  have h1 : primesBetween u v ≤ ((smallPrimes n).filter
      (fun p : ℕ => (u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v) ∧ u < apt n p)).card := by
    unfold primesBetween
    refine (card_le_card ?_).trans (card_image_le (f := fun p => (partner n p).getD 0))
    intro q hq
    simp only [mem_filter, mem_range] at hq
    have hqv : (q : ℝ) ≤ v := (Nat.le_floor_iff hv0).1 (by omega)
    obtain ⟨p, hp, hpq, htv⟩ := hb q hq.2.1 hq.2.2 hqv
    rw [mem_image]
    refine ⟨p, mem_filter.2 ⟨hp, ⟨?_, htv⟩, ?_⟩, by simp [hpq]⟩
    · have := le_div_of_mul_le (mem_smallPrimes.1 hp).1.pos (partner_spec hpq).2.2.1
      linarith [hq.2.2]
    · rw [apt_some hpq]
      exact hq.2.2
  have h2 : Disjoint (Q n u) ((smallPrimes n).filter
      (fun p : ℕ => (u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v) ∧ u < apt n p)) := by
    rw [disjoint_left]
    intro p hp hs
    rw [Q, mem_filter] at hp
    rw [mem_filter] at hs
    linarith [hp.2.1, hs.2.2]
  have h3 : Q n u ∪ (smallPrimes n).filter
      (fun p : ℕ => (u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v) ∧ u < apt n p) ⊆
      (smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v) := by
    intro p hp
    rw [mem_union] at hp
    rcases hp with hp | hp
    · rw [Q, mem_filter] at hp
      exact mem_filter.2 ⟨hp.1, hp.2.2, hnotQv p hp.1 (hp.2.1.trans huv)⟩
    · rw [mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
  have h4 := card_le_card h3
  rw [card_union_of_disjoint h2] at h4
  unfold A
  omega

lemma card_Q_le (n : ℕ) (u : ℝ) (hu : Real.sqrt n ≤ u) : (Q n u).card ≤ Winf n u := by
  obtain ⟨v, huv, h⟩ := key n u hu
  have hmem : Winf n u ∈ {w : ℕ | ∀ v : ℝ, u ≤ v → A n u v ≤ primesBetween u v + w} :=
    Nat.sInf_mem ⟨(smallPrimes n).card,
      fun v _ => (card_filter_le _ _).trans (Nat.le_add_left _ _)⟩
  have := hmem v huv
  omega

end Erdos879
