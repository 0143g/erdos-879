import Mathlib

open Finset
open scoped Nat.Prime

namespace Erdos879

def Admissible (n : ℕ) (S : Finset ℕ) : Prop :=
  (∀ a ∈ S, 1 ≤ a ∧ a ≤ n) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

noncomputable def G (n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ S : Finset ℕ, Admissible n S ∧ ∑ a ∈ S, a = s}

def H (n : ℕ) : ℕ :=
  (∑ p ∈ (range n).filter Nat.Prime, p) + n * Nat.primeCounting (Nat.sqrt n)

def smallPrimes (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p => p.Prime ∧ p * p ≤ n)

noncomputable def A (n : ℕ) (u v : ℝ) : ℕ :=
  ((smallPrimes n).filter (fun p : ℕ => u < (n : ℝ) / p ∧ (n : ℝ) / p ≤ v)).card

noncomputable def primesBetween (u v : ℝ) : ℕ :=
  ((range (⌊v⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧ u < (q : ℝ))).card

noncomputable def W (n : ℕ) (u : ℝ) : ℕ :=
  sInf {w : ℕ | ∀ v : ℝ, u ≤ v → v ≤ 4 * u → A n u v ≤ primesBetween u v + w}

noncomputable def Winf (n : ℕ) (u : ℝ) : ℕ :=
  sInf {w : ℕ | ∀ v : ℝ, u ≤ v → A n u v ≤ primesBetween u v + w}

end Erdos879
