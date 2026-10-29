module

public import Mathlib

/-!
# CarryVal — Basic definitions

- `s2 n`        : binary digit sum (popcount)
- `carries a b` : number of carries in `a + b` (binary)
-/

@[expose] public section

namespace CarryVal
/-- Binary digit sum (popcount) of `n`. -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- Number of carries when adding `a` and `b` in binary.

    Uses the Legendre/Kummer identity:
    `carries a b = s2 a + s2 b - s2 (a + b)`. -/
def carries (a b : ℕ) : ℕ := s2 a + s2 b - s2 (a + b)

end CarryVal