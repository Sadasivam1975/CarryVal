module

public import Mathlib
public import CarryVal.Basic
public import CarryVal.Bessel

/-!
# V2 UNIT — Intermediate lemmas and main theorem
-/

@[expose] public section

namespace CarryVal

/-- 2-adic valuation of a natural number. -/
def v2 (n : ℕ) : ℕ := padicValNat 2 n
-- ============================================================
-- §1. Helpers
-- ============================================================

/-- Legendre's formula for factorials: v₂(n!) = n - s₂(n). -/
lemma v2_factorial (n : ℕ) : v2 (Nat.factorial n) = n - s2 n := by
  unfold v2 s2
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa using h

/-- Helper: s₂(n) ≤ n (popcount is at most the number itself). -/
lemma s2_le_self (n : ℕ) : s2 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | k + 1 =>
      unfold s2
      have h : k + 1 ≠ 0 := by omega
      have h1lt : 1 < 2 := by norm_num
      rw [Nat.digits_eq_cons_digits_div (b := 2) h1lt h]
      rw [List.sum_cons]
      change (k + 1) % 2 + s2 ((k + 1) / 2) ≤ k + 1
      have ih' := ih ((k + 1) / 2) (by omega)
      have hmod : (k + 1) % 2 ≤ 1 := by omega
      omega

/-- s₂ is subadditive: s₂(a+b) ≤ s₂(a) + s₂(b). -/
lemma s2_add_le (a b : ℕ) : s2 (a + b) ≤ s2 a + s2 b := by
  have ha := s2_le_self a
  have hb := s2_le_self b
  have h_dvd : a.factorial * b.factorial ∣ (a + b).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add a b
  obtain ⟨c, hc⟩ := h_dvd
  have h_ab_ne : a.factorial * b.factorial ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)
  have hc_ne : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact Nat.factorial_ne_zero _ hc
  have h_ab : v2 (a.factorial * b.factorial) = v2 a.factorial + v2 b.factorial := by
    unfold v2
    exact padicValNat.mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)
  have h_v2_le : v2 (a.factorial * b.factorial) ≤ v2 ((a + b).factorial) := by
    have h_v2_abc : v2 ((a + b).factorial) = v2 (a.factorial * b.factorial) + v2 c := by
      rw [hc]
      unfold v2
      exact padicValNat.mul h_ab_ne hc_ne
    omega
  rw [h_ab, v2_factorial, v2_factorial, v2_factorial] at h_v2_le
  have hab := s2_le_self (a + b)
  omega

/-- Shifting left by 1 preserves s₂: s₂(2n) = s₂(n). -/
lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  unfold s2
  cases n with
  | zero => rfl
  | succ k =>
    have h : 2 * (k + 1) ≠ 0 := by omega
    have h1lt : 1 < 2 := by norm_num
    have hmod : 2 * (k + 1) % 2 = 0 := by omega
    have hdiv : 2 * (k + 1) / 2 = k + 1 := by omega
    rw [Nat.digits_eq_cons_digits_div (b := 2) h1lt h, hmod, hdiv]
    simp

/-- Multiplicativity of v₂ for nonzero arguments. -/
lemma v2_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    v2 (a * b) = v2 a + v2 b := by
  unfold v2
  exact padicValNat.mul ha.ne' hb.ne'

/-- Kummer's theorem (Legendre form):
    v₂(C(a+b, a)) = s₂(a) + s₂(b) - s₂(a+b). -/
lemma v2_choose_eq_s2 (a b : ℕ) :
    v2 (Nat.choose (a + b) a) = s2 a + s2 b - s2 (a + b) := by
  have h_sub : a + b - a = b := by omega
  have h_choose : (a + b).choose a = (a + b).factorial / (a.factorial * b.factorial) := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega), h_sub]
  have h_dvd : a.factorial * b.factorial ∣ (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rw [h_sub, mul_assoc] at h
    exact ⟨Nat.choose (a+b) a, by rw [mul_comm]; exact h.symm⟩
  have h_mul : (a + b).choose a * (a.factorial * b.factorial) = (a + b).factorial := by
    rw [h_choose]
    exact Nat.div_mul_cancel h_dvd
  have h_pos_choose : 0 < (a + b).choose a := Nat.choose_pos (by omega)
  have h_pos_fact : 0 < a.factorial * b.factorial := mul_pos (Nat.factorial_pos a) (Nat.factorial_pos b)

  have h_v2_mul : v2 ((a + b).factorial) = v2 ((a + b).choose a) + v2 (a.factorial * b.factorial) := by
    rw [← h_mul]
    exact v2_mul _ _ h_pos_choose h_pos_fact

  rw [v2_mul _ _ (Nat.factorial_pos a) (Nat.factorial_pos b)] at h_v2_mul
  rw [v2_factorial (a + b), v2_factorial a, v2_factorial b] at h_v2_mul

  have ha : s2 a ≤ a := s2_le_self a
  have hb : s2 b ≤ b := s2_le_self b
  have hab : s2 (a + b) ≤ a + b := s2_le_self (a + b)

  unfold v2 at h_v2_mul ⊢
  omega
-- ============================================================
-- §2. Decomposition
-- ============================================================

/-- Lemma: (2j)! = 2^j * j! * (2j-1)!! -/
lemma factorial_two_mul_eq (j : ℕ) :
    (2 * j).factorial = 2^j * j.factorial * Nat.doubleFactorial (2 * j - 1) := by
  induction j with
  | zero => rfl
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1]
    have h2 : 2 * k + 2 = 2 * k + 1 + 1 := by omega
    rw [h2, Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k)]
    rw [ih]
    rw [show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega]
    
    cases k with
    | zero => norm_num [Nat.doubleFactorial]
    | succ m =>
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega]
      rw [Nat.doubleFactorial_add_two (2 * m + 1)]
      -- 1. ih-ல் உள்ள (2*(m+1)-1)!! → (2m+1)!!
      have harg : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      -- 2. RHS-ல் உள்ள (m+1+1)! → (m+2)(m+1)m!
      have hfac : (m + 1 + 1).factorial = (m + 2) * (m + 1) * m.factorial := by
        rw [show m + 1 + 1 = (m + 1) + 1 by omega]
        rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
        ring
      -- 3. RHS-ல் உள்ள 2^(m+1+1) → 2^m * 4
      have hpow : 2 ^ (m + 1 + 1) = 2 ^ m * 4 := by
        rw [show m + 1 + 1 = m + 2 by omega]
        rw [pow_add]
        norm_num
      -- 4. ih-ல் உள்ள (m+1)! → (m+1)·m!  ← இதுதான் இப்போது தேவை
      have hfac2 : (m + 1).factorial = (m + 1) * m.factorial :=
        Nat.factorial_succ m
      rw [harg, hfac, hpow, hfac2]
      ring_nf

/-- The decomposition of `ladderCoeffNat`:
    ladderCoeff(n,j) = C(n+j, n-j) · (2j-1)!! -/
theorem ladderCoeffNat_decomp (n j : ℕ) (h : j ≤ n) :
    ladderCoeffNat n j =
      Nat.choose (n + j) (n - j) * Nat.doubleFactorial (2 * j - 1) := by
  unfold ladderCoeffNat
  have h_sub : n + j - (n - j) = 2 * j := by omega
  have h_fact : (2 * j).factorial = 2^j * j.factorial * Nat.doubleFactorial (2 * j - 1) := factorial_two_mul_eq j
  have h_pos : 0 < (n - j).factorial * 2^j * j.factorial := by positivity
  apply Nat.div_eq_of_eq_mul_left h_pos
  have h_choose := Nat.choose_mul_factorial_mul_factorial (show n - j ≤ n + j by omega)
  rw [h_sub] at h_choose
  rw [← h_choose, h_fact]
  ring

/-- (2j-1)!! is odd, hence has v₂ = 0. -/
lemma doubleFactorial_odd (j : ℕ) :
    v2 (Nat.doubleFactorial (2 * j - 1)) = 0 := by
  have h_odd : ∀ n, Odd (Nat.doubleFactorial (2 * n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨0, by rfl⟩
    | succ k ih =>
      have h_eq : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
      rw [h_eq, Nat.doubleFactorial_add_two]
      exact Odd.mul (by exact ⟨k + 1, by omega⟩) ih
      
  cases j with
  | zero => 
    have h0 : 2 * 0 - 1 = 0 := by rfl
    rw [h0]
    norm_num [v2, Nat.doubleFactorial]
  | succ k =>
    have h_eq : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h_eq]
    unfold v2
    rw [padicValNat.eq_zero_iff]
    right; right
    intro h_dvd
    have ho := h_odd k
    rcases ho with ⟨m, hm⟩
    rw [hm] at h_dvd
    omega

-- ============================================================
-- §3. Main theorem
-- ============================================================

/-- **V2 UNIT**: v₂(ladderCoeff(n,j)) = carries(n-j, 2j). -/
theorem v2_ladderCoeffNat_eq_carries (n j : ℕ) (h : j ≤ n) :
    v2 (ladderCoeffNat n j) = carries (n - j) (2 * j) := by
  rw [ladderCoeffNat_decomp n j h]
  
  have h1 : 0 < Nat.choose (n + j) (n - j) := Nat.choose_pos (by omega)
  have h2 : 0 < Nat.doubleFactorial (2 * j - 1) := Nat.doubleFactorial_pos _
  
  rw [v2_mul _ _ h1 h2]
  
  rw [show n + j = n - j + 2 * j by omega]
  rw [v2_choose_eq_s2 (n - j) (2 * j)]
  rw [doubleFactorial_odd j]
  
  unfold carries
  rw [s2_two_mul j]
  rw [show n - j + 2 * j = n + j by omega]
  omega

end CarryVal