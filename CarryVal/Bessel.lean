module

public import Mathlib
public import CarryVal.Basic

@[expose] public section

namespace CarryVal

/-- Bessel polynomial coefficient as a rational. -/
noncomputable def ladderCoeff (n j : ℕ) : ℚ :=
  (Nat.factorial (n + j) : ℚ) /
    ((Nat.factorial (n - j) : ℚ) * (2 : ℚ)^j * (Nat.factorial j : ℚ))

/-- Same coefficient, as a natural number via exact division. -/
def ladderCoeffNat (n j : ℕ) : ℕ :=
  Nat.factorial (n + j) / (Nat.factorial (n - j) * 2^j * Nat.factorial j)

@[simp] lemma ladderCoeff_zero_j (n : ℕ) : ladderCoeff n 0 = 1 := by
  unfold ladderCoeff
  simp only [Nat.sub_zero, Nat.add_zero, pow_zero, Nat.factorial_zero,
             Nat.cast_one, mul_one]
  have h : (Nat.factorial n : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact div_self h

end CarryVal