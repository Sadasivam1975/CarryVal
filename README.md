# CarryVal — Value-Free 2-adic Valuation via Binary Carries

## 🔬 Overview
This project formally verifies a novel computational transformation: the **V2 UNIT**. 
It bridges the gap between Bessel Polynomials (Harmonic Ladder) and Binary Carries, proving that the 2-adic valuation of a Bessel coefficient can be computed in **O(log n)** time without evaluating the massive integers.

## 🎯 Main Theorem
**Theorem (`v2_ladderCoeffNat_eq_carries`):**
`v₂(ladderCoeff(n,j)) = carries(n-j, 2j)`

## 🛠️ Status
- **Rigorously Validated**: 100% formally proven in Lean 4 with **0 sorries**.
- **Mathlib4**: Fully integrated.

## 📂 Structure
- `CarryVal/Basic.lean`: Definitions of `s2` (popcount) and `carries`.
- `CarryVal/Bessel.lean`: Definitions of the Bessel coefficient (`ladderCoeff`).
- `CarryVal/V2Unit.lean`: **Main proofs** (Legendre, Kummer, Decomposition, Main Theorem).

## ⚙️ How to Build
```bash
lake exe cache get
lake build CarryVal
