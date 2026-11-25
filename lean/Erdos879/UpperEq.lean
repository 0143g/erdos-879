import Erdos879.UpperMatch

open Finset

namespace Erdos879

theorem card_Q_eq (n : ℕ) (u : ℝ) (hu : Real.sqrt n ≤ u) : (Q n u).card = Winf n u := by
  classical
  refine le_antisymm (card_Q_le n u hu) (Nat.sInf_le ?_)
  intro v huv
  unfold A primesBetween
  set S := (smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v) with hS
  rw [← card_filter_add_card_filter_not (s := S) (fun p => p ∈ Q n u), add_comm]
  apply add_le_add
  · apply card_le_card_of_injOn (fun p => (partner n p).getD 0)
    · intro p hp
      simp only [hS, coe_filter, mem_filter, Set.mem_ofPred_eq] at hp
      obtain ⟨⟨hpS, hlo, hhi⟩, hnQ⟩ := hp
      have hapt : ¬ apt n p ≤ u := fun h => hnQ (mem_filter.2 ⟨hpS, h, hlo⟩)
      rcases hpart : partner n p with _ | q
      · exact absurd ((apt_none hpart).le.trans hu) hapt
      · rw [apt_some hpart, not_le] at hapt
        obtain ⟨hq, -, hpq, -, -⟩ := partner_spec hpart
        have hqv : (q : ℝ) ≤ v := (le_div_of_mul_le (mem_smallPrimes.1 hpS).1.pos hpq).trans hhi
        have hqf : q ≤ ⌊v⌋₊ := Nat.le_floor hqv
        simp only [hpart, Option.getD_some, coe_filter, mem_range, Set.mem_ofPred_eq]
        exact ⟨by omega, hq, hapt⟩
    · intro p hp p' hp' heq
      simp only [hS, coe_filter, mem_filter, Set.mem_ofPred_eq] at hp hp'
      obtain ⟨⟨hpS, hlo, -⟩, hnQ⟩ := hp
      obtain ⟨⟨hpS', hlo', -⟩, hnQ'⟩ := hp'
      have hsome : ∀ r, r ∈ smallPrimes n → u < (n : ℝ) / r → r ∉ Q n u →
          ∃ q, partner n r = some q := by
        intro r hr hlr hnr
        rcases hpart : partner n r with _ | q
        · exact absurd (mem_filter.2 ⟨hr, (apt_none hpart).le.trans hu, hlr⟩) hnr
        · exact ⟨q, rfl⟩
      obtain ⟨q, hq⟩ := hsome p hpS hlo hnQ
      obtain ⟨q', hq'⟩ := hsome p' hpS' hlo' hnQ'
      simp only [hq, hq', Option.getD_some] at heq
      subst heq
      exact partner_inj hpS hpS' hq hq'
  · apply card_le_card
    intro p hp
    exact (mem_filter.1 hp).2

end Erdos879
