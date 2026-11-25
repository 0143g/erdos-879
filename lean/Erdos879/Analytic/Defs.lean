import Erdos879.Defs

open Finset MeasureTheory

namespace Erdos879

noncomputable def li (y : ℝ) : ℝ := ∫ t in (2 : ℝ)..y, 1 / Real.log t

noncomputable def piR (y : ℝ) : ℝ := (Nat.primeCounting ⌊y⌋₊ : ℝ)

noncomputable def E (y : ℝ) : ℝ := piR y - li y

noncomputable def F (y : ℝ) : ℝ := Chebyshev.theta y - y

def VonKoch : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 2 ≤ y → |piR y - li y| ≤ C * Real.sqrt y * Real.log y

def SelbergMS : Prop :=
  ∃ C x₀ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∫ y in (1 : ℝ)..x, (Chebyshev.theta (y + δ * y) - Chebyshev.theta y - δ * y) ^ 2
      ≤ C * δ * x ^ 2 * (Real.log x) ^ 2

noncomputable def Dp (r : ℝ) (j l : ℕ) (y : ℝ) : ℝ :=
  F (y * Real.exp (((l : ℝ) + 1) * r / 2 ^ j)) - F (y * Real.exp ((l : ℝ) * r / 2 ^ j))

noncomputable def Bp (r : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  2 * ∑ j ∈ range (k + 1), Real.sqrt (∑ l ∈ range (2 ^ j), (Dp r j l y) ^ 2)
    + y * Real.exp r * (Real.exp (r / 2 ^ k) - 1)

noncomputable def Dm (r : ℝ) (j l : ℕ) (y : ℝ) : ℝ :=
  F (y * Real.exp (-((l : ℝ) * r / 2 ^ j))) - F (y * Real.exp (-(((l : ℝ) + 1) * r / 2 ^ j)))

noncomputable def Bm (r : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  2 * ∑ j ∈ range (k + 1), Real.sqrt (∑ l ∈ range (2 ^ j), (Dm r j l y) ^ 2)
    + y * (Real.exp (r / 2 ^ k) - 1)

noncomputable def kOf (Z r : ℝ) : ℕ := ⌈Real.logb 2 (Z * r)⌉₊

noncomputable def rr (i : ℕ) : ℝ := 2 / 2 ^ i

noncomputable def bfun (n : ℕ) (r u : ℝ) : ℝ :=
  r / (2 * Real.log n) * (u - Real.sqrt n + Real.sqrt n * r / 4)

end Erdos879
