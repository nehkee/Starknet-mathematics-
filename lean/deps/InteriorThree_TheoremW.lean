import MCAChallenge
import InteriorThree_CanonicalReduction

/-!
# Two-Block Cubic Certificate (`M-0934`) and Wronskian Obstruction (`Theorem W`, `M-0958`)
# Closing `SingleMonomialWronskianVanishing` at Every Dyadic `n = 2 ^ r`

Importing `InteriorThree_CanonicalReduction`, this module closes the first named open sub-lemma
`InteriorThreeCanonicalReduction.SingleMonomialWronskianVanishing` across **every dyadic scale**
`n = 2 ^ r` (`5 ≤ r ≤ 31`, `q = 2 ^ (r - 3)`) over the Mersenne circle field `F`
(`Nat.card F = (2 ^ 31 - 1) ^ 2`), and establishes unconditional list-size-`0` (`NativeListBound = 0`)
at full `5n / 8` agreement on the open Wronskian exponent bands `(11n / 16, 7n / 10) ∪ (4n / 5, 13n / 16)`:

1. **Pure Algebraic Cubic & Wronskian Obstructions (`wronskian_cubic_obstruction`,
   `low_e_cubic_obstruction`, `low_h_cubic_obstruction`):**
   For any field `F` and monic `A : F[X]` (`A.natDegree = h`), `B : F[X]` (`B.natDegree ≤ h`,
   `B.eval 0 ≠ 0`), `Q : F[X]` satisfying `A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q`
   with `0 < e`, `0 < f`, `¬ (3 ∣ e)`, and `(Q ≠ 0 → Q.natDegree + f ≤ 2 * h)`:
   - **`low_h_cubic_obstruction` (`M-0934`):** `2 * h < f` is impossible in *every* characteristic.
   - **`low_e_cubic_obstruction` (`M-0934`):** `3 * h < e` is impossible in *every* characteristic.
   - **`wronskian_cubic_obstruction` (`Theorem W`, `M-0958`):** `4 * h < e + f` is impossible
     whenever `ringChar F = 0 ∨ 3 * h < ringChar F` (proved via the polynomial Wronskian
     `W = C 3 * A' * P - A * P'` and Euclidean GCD descent `A ^ 3 ∣ B * Q`).

2. **All-Dyadic Two-Block Locator & GCD-Reduced Cubic Certificate (`M-0934`,
   `two_block_cubic_certificate`):**
   At every `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), for `m = 5 * q + δ` (`1 ≤ δ < q`) and any ambient
   polynomial `P` (`P.natDegree ≤ 4 * q`) agreeing with `C a * X ^ m + R` (`a ≠ 0`,
   `R.natDegree ≤ 4 * q`) on `S ⊆ D` of size `m - h` (`q + h < 3 * δ`), the complement locator
   `H_U = ∏ x ∈ D \ S, (X - C x)` decomposes into two blocks `H_U = X ^ (3 * q - δ) * A₀ + B₀`,
   and dividing out `gcd(A₀, B₀)` produces a reduced triple `(A, B, Q)` (`h' = A.natDegree ≤ h`)
   satisfying `A ^ 3 + X ^ (3 * δ - q) * B ^ 3 = (X ^ (3 * q - δ) * A + B) * Q` with
   `Q ≠ 0 → Q.natDegree + 4 * (q - δ) ≤ 2 * h'`.

3. **Closing `SingleMonomialWronskianVanishing` & Full `5n/8`-Agreement Vanishing
   (`singleMonomialWronskianVanishing`, `nativeListBound_zero_wronskian_band`):**
   - Proves `InteriorThreeCanonicalReduction.SingleMonomialWronskianVanishing.{u}` across all
     universes `u` and all `5 ≤ r ≤ 31`.
   - Proves `MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3)) (C a * X ^ m + R) 0`
     (empty native and ambient list!) for all `a ≠ 0`, `R.natDegree ≤ 2 ^ (r - 1)`, and every
     exponent `m` in `(11n / 16, 7n / 10) ∪ (4n / 5, 13n / 16)` (nonempty for every `r ≥ 7`, e.g.
     `m ∈ {89, 103}` at `n = 128`).
-/

namespace InteriorThreeTheoremW

open Polynomial Finset InteriorThreeCanonicalReduction

/-! ## Part 1: Pure Polynomial Obstructions (`M-0934` & `Theorem W`) -/

private lemma not_dvd_three_pow_two (k : ℕ) : ¬ (3 ∣ 2 ^ k) := by
  intro hdvd
  have hp : Nat.Prime 3 := by decide
  have h2 : 3 ∣ 2 := hp.dvd_of_dvd_pow hdvd
  omega

private lemma not_dvd_three_sub_pow_two {δ k : ℕ} (h : 2 ^ k < 3 * δ) :
    ¬ (3 ∣ (3 * δ - 2 ^ k)) := by
  rintro ⟨c, hc⟩
  apply not_dvd_three_pow_two k
  refine ⟨δ - c, ?_⟩
  calc 2 ^ k = 3 * δ - (3 * δ - 2 ^ k) := (Nat.sub_sub_self h.le).symm
    _ = 3 * δ - 3 * c := by rw [hc]
    _ = 3 * (δ - c) := (Nat.mul_sub 3 δ c).symm

private lemma eval_zero_eq_coeff_zero {R : Type*} [Semiring R] (P : R[X]) :
    P.eval 0 = P.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  simp

/-- Over a field where `ringChar F = 0 ∨ d < ringChar F`, a polynomial `U` of degree
`1 ≤ U.natDegree ≤ d` has `U.derivative ≠ 0` and `U.derivative.natDegree = U.natDegree - 1`. -/
private lemma derivative_ne_zero_and_natDegree {F : Type*} [Field F] {U : F[X]} {d : ℕ}
    (hpos : 0 < U.natDegree) (hle : U.natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F) :
    U.derivative ≠ 0 ∧ U.derivative.natDegree = U.natDegree - 1 := by
  have hUne : U ≠ 0 := by
    rintro rfl
    simp at hpos
  set m := U.natDegree
  have hm_cast_ne : (m : F) ≠ 0 := by
    intro hmz
    have hdvd : ringChar F ∣ m := (CharP.cast_eq_zero_iff F (ringChar F) m).mp hmz
    rcases hchar with hc0 | hclt
    · rw [hc0, zero_dvd_iff] at hdvd
      omega
    · have hle_m : ringChar F ≤ m := Nat.le_of_dvd hpos hdvd
      omega
  have hcoeff : U.derivative.coeff (m - 1) = U.coeff m * (m : F) := by
    have h1 : m - 1 + 1 = m := by omega
    have h1c : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
      calc ((m - 1 : ℕ) : F) + 1
          = ((m - 1 : ℕ) : F) + ((1 : ℕ) : F) := by rw [Nat.cast_one]
        _ = ((m - 1 + 1 : ℕ) : F) := (Nat.cast_add (m - 1) 1).symm
        _ = (m : F) := congrArg Nat.cast h1
    rw [Polynomial.coeff_derivative, h1, h1c]
  have hcm_ne : U.coeff m ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hUne
  have hderiv_coeff_ne : U.derivative.coeff (m - 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero hcm_ne hm_cast_ne
  have hderiv_ne : U.derivative ≠ 0 := fun h0 ↦ hderiv_coeff_ne (by simp [h0])
  refine ⟨hderiv_ne, le_antisymm (Polynomial.natDegree_derivative_le U) ?_⟩
  exact Polynomial.le_natDegree_of_ne_zero hderiv_coeff_ne

/-- Logarithmic-derivative divisibility: if `S ≠ 0`, `S.natDegree ≤ d`,
`ringChar F = 0 ∨ d < ringChar F`, and `S.derivative * P = S * P.derivative`, then `S ∣ P`. -/
theorem dvd_of_derivative_mul_eq {F : Type*} [Field F] [DecidableEq F] {S P : F[X]} {d : ℕ}
    (hS_ne : S ≠ 0) (hS_deg : S.natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F)
    (hwronsk : S.derivative * P = S * P.derivative) :
    S ∣ P := by
  by_cases hP0 : P = 0
  · rw [hP0]; exact dvd_zero S
  set G := EuclideanDomain.gcd S P
  have hGS : G ∣ S := EuclideanDomain.gcd_dvd_left S P
  have hGP : G ∣ P := EuclideanDomain.gcd_dvd_right S P
  obtain ⟨U, hSU⟩ := hGS
  obtain ⟨V, hPV⟩ := hGP
  have hG_ne : G ≠ 0 := fun h0 ↦ hS_ne (by rw [hSU, h0, zero_mul])
  have hU_ne : U ≠ 0 := fun h0 ↦ hS_ne (by rw [hSU, h0, mul_zero])
  have hcop : IsCoprime U V := by
    have hbez := EuclideanDomain.gcd_eq_gcd_ab S P
    refine ⟨EuclideanDomain.gcdA S P, EuclideanDomain.gcdB S P, ?_⟩
    apply mul_left_cancel₀ hG_ne
    calc G * (EuclideanDomain.gcdA S P * U + EuclideanDomain.gcdB S P * V)
        = (G * U) * EuclideanDomain.gcdA S P + (G * V) * EuclideanDomain.gcdB S P := by ring
      _ = S * EuclideanDomain.gcdA S P + P * EuclideanDomain.gcdB S P := by rw [← hSU, ← hPV]
      _ = G := hbez.symm
      _ = G * 1 := (mul_one G).symm
  have hUV_wronsk : U.derivative * V = U * V.derivative := by
    have hw : G ^ 2 * (U.derivative * V - U * V.derivative) = 0 := by
      have hw1 := hwronsk
      rw [hSU, hPV, Polynomial.derivative_mul, Polynomial.derivative_mul] at hw1
      linear_combination hw1
    rcases mul_eq_zero.mp hw with hG2 | hsub
    · exact False.elim ((pow_ne_zero 2 hG_ne) hG2)
    · exact sub_eq_zero.mp hsub
  have hU_dvd_U' : U ∣ U.derivative := by
    have hdvd_prod : U ∣ V * U.derivative := by
      rw [mul_comm V U.derivative, hUV_wronsk]
      exact dvd_mul_right U V.derivative
    exact hcop.dvd_of_dvd_mul_left hdvd_prod
  have hU_deg_zero : U.natDegree = 0 := by
    by_contra hpos
    have hpos' : 0 < U.natDegree := Nat.pos_of_ne_zero hpos
    have hU_le_d : U.natDegree ≤ d := by
      have hdeg_SU : S.natDegree = G.natDegree + U.natDegree := by
        rw [hSU, Polynomial.natDegree_mul hG_ne hU_ne]
      omega
    obtain ⟨hU'ne, hU'deg⟩ := derivative_ne_zero_and_natDegree hpos' hU_le_d hchar
    have hle := Polynomial.natDegree_le_of_dvd hU_dvd_U' hU'ne
    omega
  set u0 : F := U.coeff 0
  have hU_eq_C : U = Polynomial.C u0 := Polynomial.eq_C_of_natDegree_eq_zero hU_deg_zero
  have hc0_ne : u0 ≠ 0 := fun h0 ↦ hU_ne (by rw [hU_eq_C, h0, map_zero])
  refine ⟨Polynomial.C u0⁻¹ * V, ?_⟩
  rw [hPV, hSU, hU_eq_C]
  calc G * V = G * (1 * V) := by ring
    _ = G * (Polynomial.C (u0 * u0⁻¹) * V) := by rw [mul_inv_cancel₀ hc0_ne, map_one]
    _ = G * Polynomial.C u0 * (Polynomial.C u0⁻¹ * V) := by rw [Polynomial.C_mul]; ring

private lemma false_of_A_cube_add_X_pow_B_cube_eq_zero {F : Type*} [Field F]
    {A B : F[X]} {h e : ℕ} (hAm : A.Monic) (hAd : A.natDegree = h)
    (hndvd : ¬ (3 ∣ e)) (heq : A ^ 3 + X ^ e * B ^ 3 = 0) : False := by
  have hA3_monic : (A ^ 3).Monic := hAm.pow 3
  have hA3_deg : (A ^ 3).natDegree = 3 * h := by
    rw [Polynomial.natDegree_pow' (by rw [hAm.leadingCoeff, one_pow]; exact one_ne_zero), hAd]
  have hA3_ne : A ^ 3 ≠ 0 := hA3_monic.ne_zero
  have hXB3_eq : X ^ e * B ^ 3 = -(A ^ 3) := by linear_combination heq
  have hXB3_ne : X ^ e * B ^ 3 ≠ 0 := by
    rw [hXB3_eq]
    exact neg_ne_zero.mpr hA3_ne
  have hB3_ne : B ^ 3 ≠ 0 := right_ne_zero_of_mul hXB3_ne
  have hXe_ne : (X : F[X]) ^ e ≠ 0 := left_ne_zero_of_mul hXB3_ne
  have hdeg_eq : 3 * h = e + 3 * B.natDegree := by
    calc 3 * h = (A ^ 3).natDegree := hA3_deg.symm
      _ = (-(A ^ 3)).natDegree := (Polynomial.natDegree_neg _).symm
      _ = (X ^ e * B ^ 3).natDegree := congrArg Polynomial.natDegree hXB3_eq.symm
      _ = (X ^ e : F[X]).natDegree + (B ^ 3).natDegree := Polynomial.natDegree_mul hXe_ne hB3_ne
      _ = e + 3 * B.natDegree := by
          rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_pow B 3]
  apply hndvd
  exact ⟨B.natDegree, by omega⟩

/-- **`M-0934` Low-`h` Cubic Obstruction (`2 * h < f`):**
Valid over *every* field (arbitrary characteristic). -/
theorem low_h_cubic_obstruction {F : Type*} [Field F]
    {A B Q : F[X]} {h e f : ℕ}
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h)
    (hndvd : ¬ (3 ∣ e)) (h2hf : 2 * h < f)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) : False := by
  by_cases hQ0 : Q = 0
  · rw [hQ0, mul_zero] at hident
    exact false_of_A_cube_add_X_pow_B_cube_eq_zero hAm hAd hndvd hident
  · have hXA_deg : (X ^ (e + f) * A).natDegree = e + f + h := by
      rw [(Polynomial.monic_X_pow (e + f)).natDegree_mul hAm, Polynomial.natDegree_X_pow, hAd]
    have hB_lt : B.natDegree < (X ^ (e + f) * A).natDegree := by rw [hXA_deg]; omega
    have hL_deg : (X ^ (e + f) * A + B).natDegree = e + f + h := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hB_lt, hXA_deg]
    have hL_ne : X ^ (e + f) * A + B ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hL_deg; omega
    have hrhs_deg : ((X ^ (e + f) * A + B) * Q).natDegree = e + f + h + Q.natDegree := by
      rw [Polynomial.natDegree_mul hL_ne hQ0, hL_deg]
    have hlhs_deg : (A ^ 3 + X ^ e * B ^ 3).natDegree ≤ e + 3 * h := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · have h1 : (A ^ 3).natDegree ≤ 3 * h := by
          rw [Polynomial.natDegree_pow A 3, hAd]
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 : (X ^ e : F[X]).natDegree ≤ e := Polynomial.natDegree_X_pow_le e
        have h2 : (B ^ 3).natDegree ≤ 3 * h := by
          rw [Polynomial.natDegree_pow B 3]; omega
        omega
    rw [hident, hrhs_deg] at hlhs_deg
    omega

/-- **`M-0934` Low-`e` Cubic Obstruction (`3 * h < e`):**
Valid over *every* field (arbitrary characteristic) whenever `0 < f`. -/
theorem low_e_cubic_obstruction {F : Type*} [Field F]
    {A B Q : F[X]} {h e f : ℕ}
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hf_pos : 0 < f) (hndvd : ¬ (3 ∣ e))
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (h3he : 3 * h < e)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) : False := by
  by_cases hQ0 : Q = 0
  · rw [hQ0, mul_zero] at hident
    exact false_of_A_cube_add_X_pow_B_cube_eq_zero hAm hAd hndvd hident
  · have hB_ne : B ≠ 0 := fun h0 ↦ hB0 (by simp [h0])
    set P := B * Q
    set R := X ^ f * A * Q - B ^ 3
    have hP_deg : P.natDegree < 3 * h := by
      have hp : P.natDegree = B.natDegree + Q.natDegree := Polynomial.natDegree_mul hB_ne hQ0
      have hq := hQd hQ0
      omega
    have hA3_deg : (A ^ 3).natDegree = 3 * h := by
      rw [Polynomial.natDegree_pow A 3, hAd]
    have hident' : A ^ 3 + X ^ e * B ^ 3 = (X ^ e * X ^ f * A + B) * Q := by
      rw [← pow_add]
      exact hident
    have hdiff_eq : A ^ 3 - P = X ^ e * R := by
      dsimp [P, R]
      linear_combination hident'
    by_cases hR0 : R = 0
    · rw [hR0, mul_zero] at hdiff_eq
      have hA3P : A ^ 3 = P := sub_eq_zero.mp hdiff_eq
      have hd := congrArg Polynomial.natDegree hA3P
      rw [hA3_deg] at hd
      omega
    · have hXe_ne : (X : F[X]) ^ e ≠ 0 := pow_ne_zero e Polynomial.X_ne_zero
      have hrhs_deg : (X ^ e * R).natDegree = e + R.natDegree :=
        (Polynomial.natDegree_mul hXe_ne hR0).trans (by rw [Polynomial.natDegree_X_pow])
      have hlhs_deg : (A ^ 3 - P).natDegree ≤ 3 * h := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_of_eq hA3_deg) (le_of_lt hP_deg))
      rw [hdiff_eq, hrhs_deg] at hlhs_deg
      omega

/-- **`Theorem W` (`M-0958`, Wronskian Derivative Obstruction `4 * h < e + f`):**
Over any field `F` with `ringChar F = 0 ∨ 3 * h < ringChar F`, if `0 < e`, `0 < f`, `¬ (3 ∣ e)`,
and `4 * h < e + f`, there is no solution `(A, B, Q)` to
`A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q` with `A` monic of degree `h`,
`B.natDegree ≤ h`, `B.eval 0 ≠ 0`, and `(Q ≠ 0 → Q.natDegree + f ≤ 2 * h)`. -/
theorem wronskian_cubic_obstruction {F : Type*} [Field F] [DecidableEq F]
    {A B Q : F[X]} {h e f : ℕ}
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (he_pos : 0 < e) (hf_pos : 0 < f) (hndvd : ¬ (3 ∣ e))
    (hchar : ringChar F = 0 ∨ 3 * h < ringChar F)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hW_lt : 4 * h < e + f)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) : False := by
  by_cases hQ0 : Q = 0
  · rw [hQ0, mul_zero] at hident
    exact false_of_A_cube_add_X_pow_B_cube_eq_zero hAm hAd hndvd hident
  · have hQ_bound := hQd hQ0
    have hh_pos : 0 < h := by omega
    have hB_ne : B ≠ 0 := fun h0 ↦ hB0 (by simp [h0])
    set P : F[X] := B * Q
    set R : F[X] := X ^ f * A * Q - B ^ 3
    have hP_ne : P ≠ 0 := mul_ne_zero hB_ne hQ0
    have hP_deg_f : P.natDegree + f ≤ 3 * h := by
      have hp : P.natDegree = B.natDegree + Q.natDegree := Polynomial.natDegree_mul hB_ne hQ0
      omega
    have hP_lt_3h : P.natDegree < 3 * h := by omega
    have hident' : A ^ 3 + X ^ e * B ^ 3 = (X ^ e * X ^ f * A + B) * Q := by
      rw [← pow_add]
      exact hident
    have hP_eq : P = A ^ 3 - X ^ e * R := by
      dsimp [P, R]
      linear_combination -hident'
    set W : F[X] := Polynomial.C 3 * A.derivative * P - A * P.derivative
    obtain ⟨e1, rfl⟩ : ∃ e1, e = e1 + 1 := ⟨e - 1, (Nat.sub_add_cancel he_pos).symm⟩
    have hW_factor :
        W = X ^ e1 * (Polynomial.C ((e1 + 1 : ℕ) : F) * A * R +
              X * (A * R.derivative - Polynomial.C 3 * A.derivative * R)) := by
      have hP_deriv :
          P.derivative =
            Polynomial.C 3 * A ^ 2 * A.derivative -
              (Polynomial.C ((e1 + 1 : ℕ) : F) * X ^ e1 * R + X ^ (e1 + 1) * R.derivative) := by
        rw [hP_eq, Polynomial.derivative_sub, Polynomial.derivative_pow A 3,
          Polynomial.derivative_mul, Polynomial.derivative_X_pow (e1 + 1)]
        simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
      dsimp [W]
      rw [hP_deriv, hP_eq, pow_succ X e1]
      ring
    have hA'_deg : A.derivative.natDegree ≤ h - 1 := by
      rw [← hAd]
      exact Polynomial.natDegree_derivative_le A
    have hW_deg_lt : W = 0 := by
      by_contra hW_ne
      set K : F[X] := Polynomial.C ((e1 + 1 : ℕ) : F) * A * R +
        X * (A * R.derivative - Polynomial.C 3 * A.derivative * R)
      have hK_ne : K ≠ 0 := by
        intro hK0; apply hW_ne; rw [hW_factor, hK0, mul_zero]
      have hXe1_ne : (X : F[X]) ^ e1 ≠ 0 := pow_ne_zero e1 Polynomial.X_ne_zero
      have hW_ge : e1 ≤ W.natDegree := by
        rw [hW_factor, Polynomial.natDegree_mul hXe1_ne hK_ne, Polynomial.natDegree_X_pow]
        omega
      have hterm1 : (Polynomial.C 3 * A.derivative * P).natDegree < e1 := by
        refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
        have h3A' : (Polynomial.C (3 : F) * A.derivative).natDegree ≤ h - 1 :=
          le_trans (Polynomial.natDegree_C_mul_le 3 A.derivative) hA'_deg
        omega
      have hterm2 : (A * P.derivative).natDegree < e1 := by
        by_cases hP'0 : P.derivative = 0
        · rw [hP'0, mul_zero, Polynomial.natDegree_zero]; omega
        · have hP_pos : 0 < P.natDegree := by
            by_contra hp0
            have hpz : P.natDegree = 0 := Nat.eq_zero_of_not_pos hp0
            rw [Polynomial.eq_C_of_natDegree_eq_zero hpz, Polynomial.derivative_C] at hP'0
            exact hP'0 rfl
          have hP'_le : P.derivative.natDegree ≤ P.natDegree - 1 :=
            Polynomial.natDegree_derivative_le P
          refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
          rw [hAd]
          omega
      have hW_lt_e1 : W.natDegree < e1 :=
        lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hterm1 hterm2)
      omega
    have hA3_wronsk : (A ^ 3).derivative * P = A ^ 3 * P.derivative := by
      have hd3 : (A ^ 3).derivative = Polynomial.C 3 * A ^ 2 * A.derivative := by
        rw [Polynomial.derivative_pow A 3]
        simp only [Nat.cast_ofNat]
      rw [hd3]
      have hsub0 : Polynomial.C 3 * A.derivative * P - A * P.derivative = 0 := hW_deg_lt
      linear_combination A ^ 2 * hsub0
    have hA3_monic : (A ^ 3).Monic := hAm.pow 3
    have hA3_deg : (A ^ 3).natDegree = 3 * h := by
      rw [Polynomial.natDegree_pow A 3, hAd]
    have hA3_dvd_P : A ^ 3 ∣ P :=
      dvd_of_derivative_mul_eq hA3_monic.ne_zero (le_of_eq hA3_deg) hchar hA3_wronsk
    have hle_deg := Polynomial.natDegree_le_of_dvd hA3_dvd_P hP_ne
    rw [hA3_deg] at hle_deg
    omega

/-! ## Part 2: Separable Product Coprimality & Two-Block Splitting -/

private lemma dvd_X_sub_C_iff_eval_eq_zero {F : Type*} [Field F] (a : F) (P : F[X]) :
    (X - Polynomial.C a) ∣ P ↔ P.eval a = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩
    simp
  · intro hev
    have hdiv := Polynomial.modByMonic_add_div P (X - Polynomial.C a)
    have hnd : (P %ₘ (X - Polynomial.C a)).natDegree = 0 := by
      by_cases hr0 : P %ₘ (X - Polynomial.C a) = 0
      · simp [hr0]
      · have hm : (X - Polynomial.C a).Monic := Polynomial.monic_X_sub_C a
        have hlt : ((P %ₘ (X - Polynomial.C a)).natDegree : WithBot ℕ) <
            ((X - Polynomial.C a).natDegree : WithBot ℕ) := by
          rw [← Polynomial.degree_eq_natDegree hr0, ← Polynomial.degree_eq_natDegree hm.ne_zero]
          exact Polynomial.degree_modByMonic_lt P hm
        have hlt_nat : (P %ₘ (X - Polynomial.C a)).natDegree < 1 := by
          have h' := WithBot.coe_lt_coe.mp hlt
          rwa [Polynomial.natDegree_X_sub_C] at h'
        omega
    have heqC := Polynomial.eq_C_of_natDegree_eq_zero hnd
    have hevdiv := congrArg (fun Z : F[X] ↦ Z.eval a) hdiv
    change (P %ₘ (X - Polynomial.C a) + (X - Polynomial.C a) * (P /ₘ (X - Polynomial.C a))).eval a =
      P.eval a at hevdiv
    rw [heqC, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero, hev] at hevdiv
    rw [heqC, hevdiv, map_zero, zero_add] at hdiv
    exact ⟨P /ₘ (X - Polynomial.C a), hdiv.symm⟩

private lemma isCoprime_X_sub_C_of_eval_ne_zero {F : Type*} [Field F] {a : F} {L : F[X]}
    (hne : L.eval a ≠ 0) : IsCoprime (X - Polynomial.C a) L := by
  have hdiv := Polynomial.modByMonic_add_div L (X - Polynomial.C a)
  have hnd : (L %ₘ (X - Polynomial.C a)).natDegree = 0 := by
    by_cases hr0 : L %ₘ (X - Polynomial.C a) = 0
    · simp [hr0]
    · have hm : (X - Polynomial.C a).Monic := Polynomial.monic_X_sub_C a
      have hlt : ((L %ₘ (X - Polynomial.C a)).natDegree : WithBot ℕ) <
          ((X - Polynomial.C a).natDegree : WithBot ℕ) := by
        rw [← Polynomial.degree_eq_natDegree hr0, ← Polynomial.degree_eq_natDegree hm.ne_zero]
        exact Polynomial.degree_modByMonic_lt L hm
      have hlt_nat : (L %ₘ (X - Polynomial.C a)).natDegree < 1 := by
        have h' := WithBot.coe_lt_coe.mp hlt
        rwa [Polynomial.natDegree_X_sub_C] at h'
      omega
  have heqC := Polynomial.eq_C_of_natDegree_eq_zero hnd
  set c : F := (L %ₘ (X - Polynomial.C a)).coeff 0
  have hc_eq : c = L.eval a := by
    have hevdiv := congrArg (fun Z : F[X] ↦ Z.eval a) hdiv
    change (L %ₘ (X - Polynomial.C a) + (X - Polynomial.C a) * (L /ₘ (X - Polynomial.C a))).eval a =
      L.eval a at hevdiv
    rw [heqC, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero] at hevdiv
    exact hevdiv
  have hc_ne : c ≠ 0 := hc_eq ▸ hne
  refine ⟨-(Polynomial.C c⁻¹ * (L /ₘ (X - Polynomial.C a))), Polynomial.C c⁻¹, ?_⟩
  have hrem_eq : Polynomial.C c = L - (X - Polynomial.C a) * (L /ₘ (X - Polynomial.C a)) := by
    rw [← heqC]
    exact eq_sub_of_add_eq hdiv
  calc -(Polynomial.C c⁻¹ * (L /ₘ (X - Polynomial.C a))) * (X - Polynomial.C a) + Polynomial.C c⁻¹ * L
      = Polynomial.C c⁻¹ * (L - (X - Polynomial.C a) * (L /ₘ (X - Polynomial.C a))) := by ring
    _ = Polynomial.C c⁻¹ * Polynomial.C c := by rw [← hrem_eq]
    _ = Polynomial.C (c⁻¹ * c) := (map_mul Polynomial.C c⁻¹ c).symm
    _ = 1 := by rw [inv_mul_cancel₀ hc_ne, map_one]

private lemma isCoprime_of_mul_eq_prod_X_sub_C {F : Type*} [Field F] [DecidableEq F]
    (U : Finset F) :
    ∀ {G L : F[X]}, G * L = ∏ x ∈ U, (X - Polynomial.C x) → IsCoprime G L := by
  induction U using Finset.induction_on with
  | empty =>
    intro G L hGL
    rw [Finset.prod_empty] at hGL
    exact ⟨L, 0, by simp [mul_comm L G, hGL]⟩
  | @insert a U ha_notMem ih =>
    intro G L hGL
    rw [Finset.prod_insert ha_notMem] at hGL
    set P_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    have hPU_eval_ne : P_U.eval a ≠ 0 := by
      rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro x hxU
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
      exact fun hax ↦ ha_notMem (hax ▸ hxU)
    have hX_ne : (X : F[X]) - Polynomial.C a ≠ 0 := (Polynomial.monic_X_sub_C a).ne_zero
    have hGL_ev0 : G.eval a * L.eval a = 0 := by
      have hev := congrArg (fun Z : F[X] ↦ Z.eval a) hGL
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, zero_mul] at hev
      exact hev
    rcases mul_eq_zero.mp hGL_ev0 with hGa | hLa
    · obtain ⟨G', hG'⟩ := (dvd_X_sub_C_iff_eval_eq_zero a G).mpr hGa
      have hG'L : G' * L = P_U := by
        apply mul_left_cancel₀ hX_ne
        calc (X - Polynomial.C a) * (G' * L) = ((X - Polynomial.C a) * G') * L := by ring
          _ = G * L := by rw [← hG']
          _ = (X - Polynomial.C a) * P_U := hGL
      have hcop_G'L : IsCoprime G' L := ih hG'L
      have hL_ne0 : L.eval a ≠ 0 := by
        intro h0
        apply hPU_eval_ne
        have hev := congrArg (fun Z : F[X] ↦ Z.eval a) hG'L.symm
        rw [Polynomial.eval_mul, h0, mul_zero] at hev
        exact hev
      rw [hG']
      exact (isCoprime_X_sub_C_of_eval_ne_zero hL_ne0).mul_left hcop_G'L
    · obtain ⟨L', hL'⟩ := (dvd_X_sub_C_iff_eval_eq_zero a L).mpr hLa
      have hGL' : G * L' = P_U := by
        apply mul_left_cancel₀ hX_ne
        calc (X - Polynomial.C a) * (G * L') = G * ((X - Polynomial.C a) * L') := by ring
          _ = G * L := by rw [← hL']
          _ = (X - Polynomial.C a) * P_U := hGL
      have hcop_GL' : IsCoprime G L' := ih hGL'
      have hG_ne0 : G.eval a ≠ 0 := by
        intro h0
        apply hPU_eval_ne
        have hev := congrArg (fun Z : F[X] ↦ Z.eval a) hGL'.symm
        rw [Polynomial.eval_mul, h0, zero_mul] at hev
        exact hev
      rw [hL']
      exact (isCoprime_X_sub_C_of_eval_ne_zero hG_ne0).symm.mul_right hcop_GL'

private lemma two_block_polynomial_split {F : Type*} [Field F]
    {H : F[X]} {N h : ℕ} (hN_pos : 0 < N)
    (hHm : H.Monic) (hHd : H.natDegree = N + h)
    (hgap : ∀ k, h < k → k < N → H.coeff k = 0) :
    ∃ A₀ B₀ : F[X],
      H = X ^ N * A₀ + B₀ ∧
      A₀.Monic ∧
      A₀.natDegree = h ∧
      B₀.natDegree ≤ h ∧
      B₀.eval 0 = H.eval 0 := by
  set A₀ : F[X] := ∑ j ∈ Finset.range (h + 1), Polynomial.C (H.coeff (N + j)) * X ^ j
  set B₀ : F[X] := ∑ j ∈ Finset.range (min (h + 1) N), Polynomial.C (H.coeff j) * X ^ j
  have hA₀_coeff : ∀ j, A₀.coeff j = if j ≤ h then H.coeff (N + j) else 0 := by
    intro j
    simp only [A₀, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h1 h2
    · rfl
    · omega
    · omega
    · rfl
  have hB₀_coeff : ∀ j, B₀.coeff j = if j < min (h + 1) N then H.coeff j else 0 := by
    intro j
    simp only [B₀, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  have hH_eq : H = X ^ N * A₀ + B₀ := by
    ext k
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', hB₀_coeff]
    by_cases hkN : N ≤ k
    · have hk_not_min : ¬ (k < min (h + 1) N) := by omega
      simp only [hkN, ↓reduceIte, hk_not_min, add_zero, hA₀_coeff]
      by_cases hkh : k - N ≤ h
      · simp only [hkh, ↓reduceIte, Nat.add_sub_of_le hkN]
      · simp only [hkh, ↓reduceIte]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · have hk_lt_N : k < N := not_le.mp hkN
      simp only [hkN, ↓reduceIte, zero_add]
      by_cases hkh : k ≤ h
      · have hk_min : k < min (h + 1) N := by omega
        simp only [hk_min, ↓reduceIte]
      · have hk_not_min : ¬ (k < min (h + 1) N) := by omega
        simp only [hk_not_min, ↓reduceIte]
        exact hgap k (not_le.mp hkh) hk_lt_N
  have hA₀_le : A₀.natDegree ≤ h := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hj_not : ¬ (j ≤ h) := by omega
    simp [hA₀_coeff, hj_not]
  have hA₀_top : A₀.coeff h = 1 := by
    simp only [hA₀_coeff, le_rfl, ↓reduceIte, ← hHd]
    exact hHm.leadingCoeff
  have hA₀_deg : A₀.natDegree = h :=
    le_antisymm hA₀_le (Polynomial.le_natDegree_of_ne_zero (by rw [hA₀_top]; exact one_ne_zero))
  have hA₀_monic : A₀.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hA₀_deg, hA₀_top]
  have hB₀_deg : B₀.natDegree ≤ h := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hj_not : ¬ (j < min (h + 1) N) := by omega
    simp [hB₀_coeff, hj_not]
  have hB₀_eval0 : B₀.eval 0 = H.eval 0 := by
    have h0_min : 0 < min (h + 1) N := by omega
    rw [eval_zero_eq_coeff_zero, eval_zero_eq_coeff_zero, hB₀_coeff]
    simp [h0_min]
  exact ⟨A₀, B₀, hH_eq, hA₀_monic, hA₀_deg, hB₀_deg, hB₀_eval0⟩

/-! ## Part 3: All-Dyadic `M-0934` Certificate & `Theorem W` Vanishing Over `M31` -/

/-- **`M-0934` Two-Block Cubic Certificate at Every Dyadic `5 ≤ r ≤ 31` Over `M31`:**
Given `5 ≤ r ≤ 31` (`q := 2 ^ (r - 3)`), `1 ≤ δ < q`, `m := 5 * q + δ`, `a ≠ 0`,
`R.natDegree ≤ 4 * q`, and an ambient codeword `P` (`P.natDegree ≤ 4 * q`) agreeing with
`C a * X ^ m + R` on `S ⊆ D` (`5 * q ≤ S.card`), put `h := m - S.card`.
Whenever `q + h < 3 * δ`, there exists a GCD-reduced triple `(A, B, Q)` and `h' ≤ h` such that:
- `A` is monic of `natDegree h'`, `B.natDegree ≤ h'`, `B.eval 0 ≠ 0`,
- `A ^ 3 + X ^ (3 * δ - q) * B ^ 3 = (X ^ (3 * q - δ) * A + B) * Q`, and
- `Q ≠ 0 → Q.natDegree + 4 * (q - δ) ≤ 2 * h'`. -/
theorem two_block_cubic_certificate {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D S : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (hSD : S ⊆ D)
    {δ : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3))
    {a : F} (ha : a ≠ 0) {R P : F[X]}
    (hR : R.natDegree ≤ 2 ^ (r - 1)) (hP : P.natDegree ≤ 2 ^ (r - 1))
    (_hS_ge : 5 * 2 ^ (r - 3) ≤ S.card)
    (hP_ag : ∀ x ∈ S, P.eval x = (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R).eval x)
    (hqh : 2 ^ (r - 3) + ((5 * 2 ^ (r - 3) + δ) - S.card) < 3 * δ) :
    let q := 2 ^ (r - 3)
    let h := (5 * q + δ) - S.card
    let e := 3 * δ - q
    let f := 4 * (q - δ)
    ∃ (h' : ℕ) (A B Q : F[X]),
      h' ≤ h ∧
      A.Monic ∧
      A.natDegree = h' ∧
      B.natDegree ≤ h' ∧
      B.eval 0 ≠ 0 ∧
      (Q ≠ 0 → Q.natDegree + f ≤ 2 * h') ∧
      A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q := by
  obtain ⟨_, hr1_raw, hr0_raw⟩ := dyadic_octant_identities (by omega : 4 ≤ r)
  set q : ℕ := 2 ^ (r - 3)
  have hq_ge4 : 4 ≤ q := by
    have hsub : 2 ≤ r - 3 := by omega
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (r - 3) := Nat.pow_le_pow_right (by decide) hsub
  have hr1 : 2 ^ (r - 1) = 4 * q := hr1_raw
  have hr0 : 2 ^ r = 8 * q := hr0_raw
  set m : ℕ := 5 * q + δ
  set w : F[X] := Polynomial.C a * X ^ m + R
  have hRP_le : (R - P).natDegree ≤ 4 * q := by
    rw [← hr1]
    exact le_trans (Polynomial.natDegree_sub_le R P) (max_le hR hP)
  have haXm_deg : (Polynomial.C a * (X : F[X]) ^ m).natDegree = m := by
    rw [Polynomial.natDegree_C_mul ha, Polynomial.natDegree_X_pow]
  have hwP_deg : (w - P).natDegree = m := by
    have hwP_eq : w - P = Polynomial.C a * X ^ m + (R - P) := by dsimp [w]; ring
    rw [hwP_eq, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact haXm_deg
    · rw [haXm_deg]; omega
  have hwP_ne : w - P ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hwP_deg; omega
  have hS_le_m : S.card ≤ m := by
    by_contra hgt
    push Not at hgt
    refine hwP_ne (Polynomial.eq_of_degrees_lt_of_eval_finset_eq S ?_ (WithBot.bot_lt_coe S.card) ?_)
    · exact degree_lt_of_natDegree_lt (by rw [hwP_deg]; exact hgt)
    · intro x hx
      rw [Polynomial.eval_sub, hP_ag x hx, sub_self, Polynomial.eval_zero]
  set h : ℕ := m - S.card
  set N : ℕ := 3 * q - δ
  set e : ℕ := 3 * δ - q
  set f : ℕ := 4 * (q - δ)
  have hN_ef : N = e + f := by omega
  set U : Finset F := D \ S
  have hu_eq : U.card = N + h := by
    have hsdiff := Finset.card_sdiff_add_card_eq_card hSD
    change U.card + S.card = D.card at hsdiff
    rw [hD_card, hr0] at hsdiff
    omega
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  obtain ⟨hHm, hHd_u, _, hc0_ne, hcw_rec⟩ :=
    complement_locator_cw_star hF hr_hi hD_pow hSD
  change H_U.Monic at hHm
  change H_U.natDegree = U.card at hHd_u
  change H_U.coeff 0 ≠ 0 at hc0_ne
  change ∀ j ≤ U.card, H_U.coeff (U.card - j) = H_U.coeff 0 * (H_U.coeff j) ^ (2 ^ 31 - 1) at hcw_rec
  have hHd : H_U.natDegree = N + h := hHd_u.trans hu_eq
  have hM_fac : (X : F[X]) ^ (8 * q) - 1 = ∏ x ∈ D, (X - Polynomial.C x) := by
    rw [← hr0]
    exact rootsOfUnity_X_pow_sub_one_eq_prod (by positivity) hD_card hD_pow
  have hM_monic : ((X : F[X]) ^ (8 * q) - 1).Monic := by
    rw [hM_fac]
    exact Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
  have hM_deg : ((X : F[X]) ^ (8 * q) - 1).natDegree = 8 * q := by
    rw [hM_fac, Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
    simp [hD_card, hr0]
  have hrem0 : ((w - P) * H_U) %ₘ ((X : F[X]) ^ (8 * q) - 1) = 0 := by
    set M : F[X] := (X : F[X]) ^ (8 * q) - 1
    have hdiv := Polynomial.modByMonic_add_div ((w - P) * H_U) M
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq D ?_ ?_ ?_
    · rw [hD_card, hr0, ← hM_deg]
      exact lt_of_lt_of_le (Polynomial.degree_modByMonic_lt _ hM_monic) Polynomial.degree_le_natDegree
    · rw [hD_card]; exact WithBot.bot_lt_coe (2 ^ r)
    · intro x hxD
      have hMx : M.eval x = 0 := by simp [M, ← hr0, hD_pow x hxD]
      have prod_zero : ((w - P) * H_U).eval x = 0 := by
        rw [Polynomial.eval_mul]
        by_cases hxS : x ∈ S
        · rw [Polynomial.eval_sub, hP_ag x hxS, sub_self, zero_mul]
        · have hxU : x ∈ U := Finset.mem_sdiff.mpr ⟨hxD, hxS⟩
          have hHx : H_U.eval x = 0 := by
            rw [Polynomial.eval_prod]
            exact Finset.prod_eq_zero hxU (by simp)
          rw [hHx, mul_zero]
      have hev := congrArg (fun Z : F[X] ↦ Z.eval x) hdiv
      change (((w - P) * H_U) %ₘ M + M * (((w - P) * H_U) /ₘ M)).eval x =
        ((w - P) * H_U).eval x at hev
      rw [Polynomial.eval_add, Polynomial.eval_mul, hMx, zero_mul, add_zero, prod_zero] at hev
      rw [Polynomial.eval_zero]
      exact hev
  set S₁ : F[X] := ((w - P) * H_U) /ₘ ((X : F[X]) ^ (8 * q) - 1)
  have hprod_eq : (w - P) * H_U = ((X : F[X]) ^ (8 * q) - 1) * S₁ := by
    have hdiv := Polynomial.modByMonic_add_div ((w - P) * H_U) ((X : F[X]) ^ (8 * q) - 1)
    rw [hrem0, zero_add] at hdiv
    exact hdiv.symm
  have hS₁_deg : S₁.natDegree ≤ h := by
    have hprod_deg : ((w - P) * H_U).natDegree = 8 * q + h := by
      rw [Polynomial.natDegree_mul hwP_ne hHm.ne_zero, hwP_deg, hHd]
      omega
    by_cases hS10 : S₁ = 0
    · rw [hS10]; simp
    · have hrhs_deg : (((X : F[X]) ^ (8 * q) - 1) * S₁).natDegree = 8 * q + S₁.natDegree := by
        rw [Polynomial.natDegree_mul hM_monic.ne_zero hS10, hM_deg]
      rw [hprod_eq, hrhs_deg] at hprod_deg
      omega
  have hupper_gap : ∀ k, 2 * q - 2 * δ + h < k → k < N → H_U.coeff k = 0 := by
    intro k hk_lo hk_hi
    set j := m + k
    have hj_lt_8q : j < 8 * q := by omega
    have hj_gt_RP : (R - P).natDegree + H_U.natDegree < j := by
      rw [hHd]; omega
    have hrhs_j : (((X : F[X]) ^ (8 * q) - 1) * S₁).coeff j = 0 := by
      have hj_not_ge : ¬ (8 * q ≤ j) := by omega
      rw [sub_mul, one_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul']
      simp only [hj_not_ge, ↓reduceIte, zero_sub, neg_eq_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hlhs_j : ((w - P) * H_U).coeff j = a * H_U.coeff k := by
      have hwP_split : (w - P) * H_U = Polynomial.C a * (X ^ m * H_U) + (R - P) * H_U := by
        dsimp [w]; ring
      have hm_le_j : m ≤ j := by omega
      rw [hwP_split, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
      simp only [hm_le_j, ↓reduceIte]
      have hRP0 : ((R - P) * H_U).coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt Polynomial.natDegree_mul_le hj_gt_RP)
      have hsub_mk : j - m = k := by omega
      rw [hRP0, add_zero, hsub_mk]
    have ha_mul_zero : a * H_U.coeff k = 0 := by
      rw [← hlhs_j, hprod_eq, hrhs_j]
    exact (mul_eq_zero.mp ha_mul_zero).resolve_left ha
  have hfull_gap : ∀ k, h < k → k < N → H_U.coeff k = 0 := by
    intro k hk_lo hk_hi
    by_cases hk_upper : 2 * q - 2 * δ + h < k
    · exact hupper_gap k hk_upper hk_hi
    · have hk_le_u : k ≤ U.card := by rw [hu_eq]; omega
      have hrefl_lo : 2 * q - 2 * δ + h < U.card - k := by rw [hu_eq]; omega
      have hrefl_hi : U.card - k < N := by rw [hu_eq]; omega
      have hrefl0 : H_U.coeff (U.card - k) = 0 := hupper_gap (U.card - k) hrefl_lo hrefl_hi
      have hrec := hcw_rec k hk_le_u
      rw [hrefl0] at hrec
      have hpow0 : (H_U.coeff k) ^ (2 ^ 31 - 1) = 0 :=
        (mul_eq_zero.mp hrec.symm).resolve_left hc0_ne
      by_contra hkne
      exact pow_ne_zero (2 ^ 31 - 1) hkne hpow0
  obtain ⟨A₀, B₀, hH_split, hA₀m, hA₀d, hB₀d, hB₀_ev0⟩ :=
    two_block_polynomial_split (by omega : 0 < N) hHm hHd hfull_gap
  have hB₀_ne0 : B₀.eval 0 ≠ 0 := by
    rw [hB₀_ev0, eval_zero_eq_coeff_zero]
    exact hc0_ne
  have h3N_add_e : 3 * N + e = 8 * q := by omega
  have hH_dvd_cubic : H_U ∣ (A₀ ^ 3 + X ^ e * B₀ ^ 3) := by
    set C₀ : F[X] := A₀ ^ 3 + X ^ e * B₀ ^ 3
    have hrem_U : C₀ %ₘ H_U = 0 := by
      have hdiv := Polynomial.modByMonic_add_div C₀ H_U
      refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq U ?_ ?_ ?_
      · rw [← hHd_u]
        exact lt_of_lt_of_le (Polynomial.degree_modByMonic_lt C₀ hHm) Polynomial.degree_le_natDegree
      · exact WithBot.bot_lt_coe U.card
      · intro x hxU
        have hxD : x ∈ D := Finset.sdiff_subset hxU
        have hx8q : x ^ (8 * q) = 1 := by rw [← hr0]; exact hD_pow x hxD
        have hHx : H_U.eval x = 0 := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero hxU (by simp)
        have hrel : x ^ N * A₀.eval x + B₀.eval x = 0 := by
          have hev := congrArg (fun Z : F[X] ↦ Z.eval x) hH_split
          rw [hHx, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X] at hev
          exact hev.symm
        have hxB0 : B₀.eval x = -(x ^ N * A₀.eval x) := eq_neg_of_add_eq_zero_right hrel
        have hCx : C₀.eval x = 0 := by
          simp only [C₀, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, hxB0]
          calc A₀.eval x ^ 3 + x ^ e * (-(x ^ N * A₀.eval x)) ^ 3
              = A₀.eval x ^ 3 * (1 - x ^ (3 * N + e)) := by ring
            _ = 0 := by rw [h3N_add_e, hx8q, sub_self, mul_zero]
        have hev := congrArg (fun Z : F[X] ↦ Z.eval x) hdiv
        change (C₀ %ₘ H_U + H_U * (C₀ /ₘ H_U)).eval x = C₀.eval x at hev
        rw [Polynomial.eval_add, Polynomial.eval_mul, hHx, zero_mul, add_zero, hCx] at hev
        rw [Polynomial.eval_zero]
        exact hev
    refine ⟨C₀ /ₘ H_U, ?_⟩
    have hdiv := Polynomial.modByMonic_add_div C₀ H_U
    rw [hrem_U, zero_add] at hdiv
    exact hdiv.symm
  obtain ⟨Q₀, hQ₀_eq⟩ := hH_dvd_cubic
  set G_raw := EuclideanDomain.gcd A₀ B₀
  have hGraw_dvd_A₀ : G_raw ∣ A₀ := EuclideanDomain.gcd_dvd_left A₀ B₀
  have hGraw_dvd_B₀ : G_raw ∣ B₀ := EuclideanDomain.gcd_dvd_right A₀ B₀
  have hGraw_ne : G_raw ≠ 0 := by
    intro h0
    obtain ⟨U', hU'⟩ := hGraw_dvd_A₀
    rw [h0, zero_mul] at hU'
    exact hA₀m.ne_zero hU'
  set G : F[X] := Polynomial.C (G_raw.leadingCoeff)⁻¹ * G_raw
  have hGm : G.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hGraw_ne)]
  have hG_dvd_A₀ : G ∣ A₀ := by
    obtain ⟨U', hU'⟩ := hGraw_dvd_A₀
    refine ⟨Polynomial.C G_raw.leadingCoeff * U', ?_⟩
    dsimp [G]
    calc A₀ = 1 * (G_raw * U') := by rw [one_mul, ← hU']
      _ = Polynomial.C (G_raw.leadingCoeff⁻¹ * G_raw.leadingCoeff) * (G_raw * U') := by
          rw [inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hGraw_ne), map_one]
      _ = Polynomial.C G_raw.leadingCoeff⁻¹ * G_raw * (Polynomial.C G_raw.leadingCoeff * U') := by
          rw [Polynomial.C_mul]; ring
  have hG_dvd_B₀ : G ∣ B₀ := by
    obtain ⟨V', hV'⟩ := hGraw_dvd_B₀
    refine ⟨Polynomial.C G_raw.leadingCoeff * V', ?_⟩
    dsimp [G]
    calc B₀ = 1 * (G_raw * V') := by rw [one_mul, ← hV']
      _ = Polynomial.C (G_raw.leadingCoeff⁻¹ * G_raw.leadingCoeff) * (G_raw * V') := by
          rw [inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hGraw_ne), map_one]
      _ = Polynomial.C G_raw.leadingCoeff⁻¹ * G_raw * (Polynomial.C G_raw.leadingCoeff * V') := by
          rw [Polynomial.C_mul]; ring
  obtain ⟨A, hA₀_GA⟩ := hG_dvd_A₀
  obtain ⟨B, hB₀_GB⟩ := hG_dvd_B₀
  have hA_ne : A ≠ 0 := fun h0 ↦ hA₀m.ne_zero (by rw [hA₀_GA, h0, mul_zero])
  have hB_ne : B ≠ 0 := fun h0 ↦ (fun hb0 : B₀ = 0 ↦ hB₀_ne0 (by simp [hb0]))
    (by rw [hB₀_GB, h0, mul_zero])
  have hAm : A.Monic := by
    have hlc : (G * A).leadingCoeff = 1 := hA₀_GA ▸ hA₀m.leadingCoeff
    rw [Polynomial.leadingCoeff_mul, hGm.leadingCoeff, one_mul] at hlc
    exact hlc
  set h' : ℕ := A.natDegree
  have hh_sum : h = G.natDegree + h' := by
    rw [← hA₀d, hA₀_GA, Polynomial.natDegree_mul hGm.ne_zero hA_ne]
  have hh'_le : h' ≤ h := by omega
  have hBd : B.natDegree ≤ h' := by
    have hGB_deg : B₀.natDegree = G.natDegree + B.natDegree := by
      rw [hB₀_GB, Polynomial.natDegree_mul hGm.ne_zero hB_ne]
    omega
  have hB_ev0 : B.eval 0 ≠ 0 := by
    intro hb0
    apply hB₀_ne0
    rw [hB₀_GB, Polynomial.eval_mul, hb0, mul_zero]
  set L : F[X] := X ^ N * A + B
  have hGL_eq_H : G * L = H_U := by
    dsimp [L]
    rw [hH_split, hA₀_GA, hB₀_GB]
    ring
  have hcop_GL : IsCoprime G L := isCoprime_of_mul_eq_prod_X_sub_C U hGL_eq_H
  have hcop_G2L : IsCoprime (G ^ 2) L := hcop_GL.pow_left
  have hG2_eq : G ^ 2 * (A ^ 3 + X ^ e * B ^ 3) = L * Q₀ := by
    apply mul_left_cancel₀ hGm.ne_zero
    calc G * (G ^ 2 * (A ^ 3 + X ^ e * B ^ 3))
        = (G * A) ^ 3 + X ^ e * (G * B) ^ 3 := by ring
      _ = A₀ ^ 3 + X ^ e * B₀ ^ 3 := by rw [← hA₀_GA, ← hB₀_GB]
      _ = H_U * Q₀ := hQ₀_eq
      _ = (G * L) * Q₀ := by rw [hGL_eq_H]
      _ = G * (L * Q₀) := by ring
  have hG2_dvd_Q₀ : G ^ 2 ∣ Q₀ := by
    have hdvd_LQ : G ^ 2 ∣ L * Q₀ := ⟨A ^ 3 + X ^ e * B ^ 3, hG2_eq.symm⟩
    exact hcop_G2L.dvd_of_dvd_mul_left hdvd_LQ
  obtain ⟨Q, hQ₀_G2Q⟩ := hG2_dvd_Q₀
  have hred_ident : A ^ 3 + X ^ e * B ^ 3 = L * Q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hGm.ne_zero)
    calc G ^ 2 * (A ^ 3 + X ^ e * B ^ 3) = L * Q₀ := hG2_eq
      _ = L * (G ^ 2 * Q) := by rw [hQ₀_G2Q]
      _ = G ^ 2 * (L * Q) := by ring
  have hQd_bound : Q ≠ 0 → Q.natDegree + f ≤ 2 * h' := by
    intro hQ_ne
    have hL_deg : L.natDegree = N + h' := by
      dsimp [L]
      have hXA_deg : (X ^ N * A).natDegree = N + h' := by
        rw [(Polynomial.monic_X_pow N).natDegree_mul hAm, Polynomial.natDegree_X_pow]
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · exact hXA_deg
      · rw [hXA_deg]; omega
    have hL_ne : L ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hL_deg; omega
    have hrhs_deg : (L * Q).natDegree = N + h' + Q.natDegree := by
      rw [Polynomial.natDegree_mul hL_ne hQ_ne, hL_deg]
    have hlhs_deg : (A ^ 3 + X ^ e * B ^ 3).natDegree ≤ e + 3 * h' := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · have h1 : (A ^ 3).natDegree ≤ 3 * h' := by rw [Polynomial.natDegree_pow A 3]
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 : (X ^ e : F[X]).natDegree ≤ e := Polynomial.natDegree_X_pow_le e
        have h2 : (B ^ 3).natDegree ≤ 3 * h' := by rw [Polynomial.natDegree_pow B 3]; omega
        omega
    rw [hred_ident, hrhs_deg, hN_ef] at hlhs_deg
    omega
  refine ⟨h', A, B, Q, hh'_le, hAm, rfl, hBd, hB_ev0, hQd_bound, ?_⟩
  dsimp [L] at hred_ident
  rw [← hN_ef]
  exact hred_ident

/-- **All-Dyadic Single-Monomial Inner-Band Vanishing (`M-0934` + `Theorem W` `M-0958`):**
Over `M31` (`Nat.card F = (2 ^ 31 - 1) ^ 2`), for every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`),
`1 ≤ δ < q`, `m = 5 * q + δ`, `0 ≤ h ≤ δ` with `q + h < 3 * δ`, if ANY of:
- `4 * h < 3 * q - δ` (`Theorem W` Wronskian regime),
- `h < 2 * (q - δ)` (`M-0934` degree-gap regime), or
- `3 * h < 3 * δ - q` (`M-0934` low-`e` regime)
holds, then **zero** ambient codewords (and hence `NativeListBound = 0`) agree with
`C a * X ^ m + R` (`a ≠ 0`, `R.natDegree ≤ 2 ^ (r - 1)`) on `≥ m - h` points of `D`. -/
theorem ambient_and_native_vanishing_inner_band {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hregime : 4 * h < 3 * 2 ^ (r - 3) - δ ∨
               h < 2 * (2 ^ (r - 3) - δ) ∨
               3 * h < 3 * δ - 2 ^ (r - 3))
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R) 0 := by
  have hno_amb : ¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
      (5 * 2 ^ (r - 3) + δ) - h ≤
        (D.filter fun x ↦
          P.eval x = (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R).eval x).card := by
    rintro ⟨P, hP_deg, hcard_ge⟩
    set q := 2 ^ (r - 3)
    set m := 5 * q + δ
    set S := D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x
    have hSD : S ⊆ D := Finset.filter_subset _ _
    have hS_ge_5q : 5 * q ≤ S.card := by omega
    have hP_ag : ∀ x ∈ S, P.eval x = (Polynomial.C a * X ^ m + R).eval x :=
      fun x hx ↦ (Finset.mem_filter.mp hx).2
    set h₀ := m - S.card
    have hh₀_le_h : h₀ ≤ h := by omega
    have hqh₀ : q + h₀ < 3 * δ := by omega
    obtain ⟨h', A, B, Q, hh'_le_h₀, hAm, hAd, hBd, hB0, hQd, hident⟩ :=
      two_block_cubic_certificate hF hr_lo hr_hi hD_card hD_pow hSD hδ_pos hδ_lt ha hR hP_deg
        hS_ge_5q hP_ag hqh₀
    have hh'_le_h : h' ≤ h := le_trans hh'_le_h₀ hh₀_le_h
    have he_pos : 0 < 3 * δ - q := by omega
    have hf_pos : 0 < 4 * (q - δ) := by omega
    have hndvd : ¬ (3 ∣ (3 * δ - q)) := not_dvd_three_sub_pow_two (by omega : 2 ^ (r - 3) < 3 * δ)
    have hrchar : ringChar F = 2 ^ 31 - 1 := mersenne_ext_ringChar hF
    have h3h'_lt_p : 3 * h' < 2 ^ 31 - 1 := by
      have hq_le : q ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) (by omega : r - 3 ≤ 28)
      omega
    have hchar : ringChar F = 0 ∨ 3 * h' < ringChar F := Or.inr (by rw [hrchar]; exact h3h'_lt_p)
    rcases hregime with hW | hlow_h | hlow_e
    · exact wronskian_cubic_obstruction hAm hAd hBd hB0 he_pos hf_pos hndvd hchar hQd
        (by omega : 4 * h' < (3 * δ - q) + 4 * (q - δ)) hident
    · exact low_h_cubic_obstruction hAm hAd hBd hndvd
        (by omega : 2 * h' < 4 * (q - δ)) hident
    · exact low_e_cubic_obstruction hAm hAd hBd hB0 hf_pos hndvd hQd
        (by omega : 3 * h' < 3 * δ - q) hident
  refine ⟨hno_amb, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
    exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- **Mirror Duality (`m = 7 * q - δ`) for `M-0934` + `Theorem W` (`M-0958`):**
Using Frobenius circle inversion `x ^ p = x⁻¹` (`p = 2 ^ 31 - 1`), any ambient codeword agreeing
with `C a * X ^ (7 * q - δ) + R` on `S ⊆ D` maps to an ambient codeword agreeing with
`C (a ^ p) * X ^ (5 * q + δ) + R_rev` on `S`, extending the exact same vanishing bound to the
mirror exponent `7 * q - δ` across every dyadic `5 ≤ r ≤ 31`. -/
theorem ambient_and_native_vanishing_mirror_band {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hregime : 4 * h < 3 * 2 ^ (r - 3) - δ ∨
               h < 2 * (2 ^ (r - 3) - δ) ∨
               3 * h < 3 * δ - 2 ^ (r - 3))
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (7 * 2 ^ (r - 3) - δ) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ (7 * 2 ^ (r - 3) - δ) + R) 0 := by
  have hrchar : ringChar F = 2 ^ 31 - 1 := mersenne_ext_ringChar hF
  have : CharP F (2 ^ 31 - 1) := ringChar.of_eq hrchar
  have hinv := mersenne_frobenius_inv_on_D hr_hi hD_pow
  obtain ⟨_, hr1_raw, hr0_raw⟩ := dyadic_octant_identities (by omega : 4 ≤ r)
  set p : ℕ := 2 ^ 31 - 1
  set q : ℕ := 2 ^ (r - 3)
  set K : ℕ := 2 ^ (r - 1)
  have hr1 : K = 4 * q := hr1_raw
  have hr0 : 2 ^ r = 8 * q := hr0_raw
  let conjRev : F[X] → F[X] := fun Q ↦
    ∑ j ∈ Finset.range (K + 1), Polynomial.C ((Q.coeff j) ^ p) * X ^ (K - j)
  have hconjRev_deg : ∀ Q : F[X], (conjRev Q).natDegree ≤ K := by
    intro Q
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le K, fun j hj ↦ ?_⟩
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact le_trans (Polynomial.natDegree_X_pow_le _) (by omega)
  have hconjRev_eval : ∀ Q : F[X], Q.natDegree ≤ K → ∀ x ∈ D,
      (conjRev Q).eval x = x ^ K * (Q.eval x) ^ p := by
    intro Q hQd x hxD
    have hxp_inv : x ^ p = x⁻¹ := (hinv x hxD).2
    have hx_ne : x ≠ 0 := fun h0 ↦ by
      have h1 := hD_pow x hxD
      rw [h0, zero_pow (by positivity)] at h1
      exact zero_ne_one h1
    have hQ_sum : Q.eval x = ∑ j ∈ Finset.range (K + 1), Q.coeff j * x ^ j := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQd)]
    have hfrob_sum : (Q.eval x) ^ p = ∑ j ∈ Finset.range (K + 1), (Q.coeff j) ^ p * (x ^ p) ^ j := by
      rw [hQ_sum]
      have hmap := map_sum (frobenius F p) (fun j ↦ Q.coeff j * x ^ j) (Finset.range (K + 1))
      change (∑ j ∈ Finset.range (K + 1), Q.coeff j * x ^ j) ^ p =
        ∑ j ∈ Finset.range (K + 1), (Q.coeff j * x ^ j) ^ p at hmap
      rw [hmap]
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [mul_pow, pow_right_comm]
    rw [hfrob_sum, Finset.mul_sum]
    simp only [conjRev, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, hxp_inv]
    refine Finset.sum_congr rfl (fun j hj ↦ ?_)
    have hj_le : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxk : x ^ K = x ^ (K - j) * x ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj_le]
    have hxinv_j : (x⁻¹) ^ j * x ^ j = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hx_ne, one_pow]
    calc (Q.coeff j) ^ p * x ^ (K - j)
        = (Q.coeff j) ^ p * x ^ (K - j) * ((x⁻¹) ^ j * x ^ j) := by rw [hxinv_j, mul_one]
      _ = (x ^ (K - j) * x ^ j) * ((Q.coeff j) ^ p * (x⁻¹) ^ j) := by ring
      _ = x ^ K * ((Q.coeff j) ^ p * (x⁻¹) ^ j) := by rw [hxk]
  have hap_ne : a ^ p ≠ 0 := pow_ne_zero p ha
  have hno_inner := (ambient_and_native_vanishing_inner_band hF hr_lo hr_hi hD_card hD_pow
    hδ_pos hδ_lt hh_le hqh hregime hap_ne (conjRev R) (hconjRev_deg R)).1
  have hno_mirror : ¬ ∃ P : F[X], P.natDegree ≤ K ∧
      (5 * q + δ) - h ≤
        (D.filter fun x ↦
          P.eval x = (Polynomial.C a * X ^ (7 * q - δ) + R).eval x).card := by
    rintro ⟨P, hPd, hcard⟩
    apply hno_inner
    refine ⟨conjRev P, hconjRev_deg P, ?_⟩
    refine le_trans hcard (Finset.card_le_card (fun x hx ↦ ?_))
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxD, hP_eq_x⟩ := hx
    refine ⟨hxD, ?_⟩
    have hx8q : x ^ (8 * q) = 1 := by rw [← hr0]; exact hD_pow x hxD
    have hxp_inv : x ^ p = x⁻¹ := (hinv x hxD).2
    have hx_ne : x ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow (by positivity)] at hx8q; exact zero_ne_one hx8q
    have hx_mirror_pow : x ^ K * (x ^ (7 * q - δ)) ^ p = x ^ (5 * q + δ) := by
      rw [pow_right_comm, hxp_inv]
      apply mul_right_cancel₀ (pow_ne_zero (7 * q - δ) hx_ne)
      have hexp1 : (5 * q + δ) + (7 * q - δ) = 8 * q + K := by omega
      calc x ^ K * (x⁻¹) ^ (7 * q - δ) * x ^ (7 * q - δ)
          = x ^ K * ((x⁻¹ * x) ^ (7 * q - δ)) := by rw [mul_pow]; ring
        _ = x ^ K := by rw [inv_mul_cancel₀ hx_ne, one_pow, mul_one]
        _ = 1 * x ^ K := (one_mul _).symm
        _ = x ^ (8 * q) * x ^ K := by rw [hx8q]
        _ = x ^ (8 * q + K) := (pow_add x (8 * q) K).symm
        _ = x ^ ((5 * q + δ) + (7 * q - δ)) := by rw [← hexp1]
        _ = x ^ (5 * q + δ) * x ^ (7 * q - δ) := pow_add x (5 * q + δ) (7 * q - δ)
    rw [hconjRev_eval P hPd x hxD, hP_eq_x]
    have hfrob_add :
        ((Polynomial.C a * X ^ (7 * q - δ) + R).eval x) ^ p =
          a ^ p * (x ^ (7 * q - δ)) ^ p + (R.eval x) ^ p := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      have hmap := (frobenius F p).map_add (a * x ^ (7 * q - δ)) (R.eval x)
      change (a * x ^ (7 * q - δ) + R.eval x) ^ p =
        (a * x ^ (7 * q - δ)) ^ p + (R.eval x) ^ p at hmap
      rw [hmap, mul_pow]
    rw [hfrob_add, mul_add, ← mul_assoc (x ^ K), mul_comm (x ^ K) (a ^ p), mul_assoc (a ^ p),
      hx_mirror_pow, ← hconjRev_eval R hR x hxD]
    dsimp [q]
    simp
  refine ⟨hno_mirror, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
    exact hno_mirror ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-! ## Part 4: Closing `SingleMonomialWronskianVanishing` & Full `5n/8`-Agreement Vanishing -/

/-- **Main Sub-Lemma Proof (`SingleMonomialWronskianVanishing`):**
Closes the named open sub-lemma `InteriorThreeCanonicalReduction.SingleMonomialWronskianVanishing`
across all universes `u` and every dyadic `5 ≤ r ≤ 31`. -/
theorem singleMonomialWronskianVanishing.{u} :
    InteriorThreeCanonicalReduction.SingleMonomialWronskianVanishing.{u} := by
  intro F _ _ hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt m hm_eq γ U hu_lt hreg hvalid
  have hr4 : 4 ≤ r := by omega
  obtain ⟨hq_pos, hr1, hr0⟩ := dyadic_octant_identities hr4
  obtain ⟨hUD, hu_le_3q, _, _, hB_deg, _, _⟩ := hvalid
  set S : Finset F := D \ U
  have hSD : S ⊆ D := Finset.sdiff_subset
  have hDS : D \ S = U := Finset.sdiff_sdiff_eq_self hUD
  have hu_add_S : S.card + U.card = 8 * 2 ^ (r - 3) := by
    have hsdiff := Finset.card_sdiff_add_card_eq_card hUD
    change S.card + U.card = D.card at hsdiff
    rw [hD_card, hr0] at hsdiff
    exact hsdiff
  have hS_ge_5q : 5 * 2 ^ (r - 3) ≤ S.card := by omega
  have hB_deg' :
      (((X : F[X]) ^ m * ∏ x ∈ D \ S, (X - Polynomial.C x)) %ₘ
        ((X : F[X]) ^ (2 ^ r) - 1)).natDegree ≤ 2 ^ (r - 1) + (D \ S).card := by
    rwa [hDS]
  obtain ⟨P, hP_deg, hP_ag⟩ :=
    (weierstrass_silent_band_iff hr4 hD_card hD_pow hSD hS_ge_5q ((X : F[X]) ^ m)).1.mpr hB_deg'
  have hS_filt :
      S.card ≤
        (D.filter fun x ↦ P.eval x = (Polynomial.C (1 : F) * X ^ m + 0).eval x).card := by
    refine Finset.card_le_card (fun x hxS ↦ Finset.mem_filter.mpr ⟨hSD hxS, ?_⟩)
    rw [map_one, one_mul, add_zero]
    exact hP_ag x hxS
  by_cases hu_lo : 3 * 2 ^ (r - 3) - δ ≤ U.card
  · set h : ℕ := U.card + δ - 3 * 2 ^ (r - 3)
    have hh_le : h ≤ δ := by omega
    have hqh : 2 ^ (r - 3) + h < 3 * δ := by omega
    have hS_eq : (5 * 2 ^ (r - 3) + δ) - h = S.card := by omega
    have hregime :
        4 * h < 3 * 2 ^ (r - 3) - δ ∨
        h < 2 * (2 ^ (r - 3) - δ) ∨
        3 * h < 3 * δ - 2 ^ (r - 3) := by
      rcases hreg with h1 | h2 | h3
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    rcases hm_eq with rfl | rfl
    · exact (ambient_and_native_vanishing_inner_band hF hr5 hr_hi hD_card hD_pow
        hδ1 hδ_lt hh_le hqh hregime one_ne_zero 0 (by simp)).1
        ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
    · exact (ambient_and_native_vanishing_mirror_band hF hr5 hr_hi hD_card hD_pow
        hδ1 hδ_lt hh_le hqh hregime one_ne_zero 0 (by simp)).1
        ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · have hS_gt : 5 * 2 ^ (r - 3) + δ < S.card := by omega
    rcases hm_eq with rfl | rfl
    · have hP_eq_Xm : P = (X : F[X]) ^ (5 * 2 ^ (r - 3) + δ) := by
        refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq S
          (degree_lt_of_natDegree_lt (by omega))
          (degree_lt_of_natDegree_lt (lt_of_le_of_lt (Polynomial.natDegree_X_pow_le _) hS_gt)) ?_
        exact hP_ag
      have hd := congrArg Polynomial.natDegree hP_eq_Xm
      rw [Polynomial.natDegree_X_pow] at hd
      omega
    · have hmul_deg : ((X : F[X]) ^ (2 ^ (r - 3) + δ) * P).natDegree < S.card := by
        have hle : ((X : F[X]) ^ (2 ^ (r - 3) + δ) * P).natDegree ≤
            (2 ^ (r - 3) + δ) + P.natDegree := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          have hX : ((X : F[X]) ^ (2 ^ (r - 3) + δ)).natDegree ≤ 2 ^ (r - 3) + δ :=
            Polynomial.natDegree_X_pow_le _
          omega
        omega
      have hmul_eq_one : (X : F[X]) ^ (2 ^ (r - 3) + δ) * P = 1 := by
        refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq S
          (degree_lt_of_natDegree_lt hmul_deg)
          (degree_lt_of_natDegree_lt (by rw [Polynomial.natDegree_one]; omega)) ?_
        intro x hxS
        have hx8q : x ^ (8 * 2 ^ (r - 3)) = 1 := by rw [← hr0]; exact hD_pow x (hSD hxS)
        have hpx := hP_ag x hxS
        rw [Polynomial.eval_pow, Polynomial.eval_X] at hpx
        rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hpx, ← pow_add,
          show (2 ^ (r - 3) + δ) + (7 * 2 ^ (r - 3) - δ) = 8 * 2 ^ (r - 3) by omega,
          hx8q, Polynomial.eval_one]
      have hqd_ne : 2 ^ (r - 3) + δ ≠ 0 := (Nat.add_pos_left hq_pos δ).ne'
      have hev0 := congrArg (fun Z : F[X] ↦ Z.eval 0) hmul_eq_one
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        zero_pow hqd_ne, zero_mul, Polynomial.eval_one] at hev0
      exact zero_ne_one hev0

/-- **Unconditional `5n / 8`-Agreement List-Size-`0` Corollary (in terms of `δ`):**
Whenever `2 ^ (r - 3) < 2 * δ` and `5 * δ < 3 * 2 ^ (r - 3)` (`5 ≤ r ≤ 31`, nonempty for every
`7 ≤ r ≤ 31`), `NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3)) (C a * X ^ m + R) 0` holds for
all `a ≠ 0`, `R.natDegree ≤ 2 ^ (r - 1)`, and `m = 5 * 2 ^ (r - 3) + δ` or `7 * 2 ^ (r - 3) - δ`. -/
theorem nativeListBound_zero_wronskian_delta {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ m : ℕ} (hδ_lo : 2 ^ (r - 3) < 2 * δ) (hδ_hi : 5 * δ < 3 * 2 ^ (r - 3))
    (hm_eq : m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        5 * 2 ^ (r - 3) ≤
          (D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3))
      (Polynomial.C a * X ^ m + R) 0 := by
  have hδ1 : 1 ≤ δ := by omega
  have hδ_lt : δ < 2 ^ (r - 3) := by omega
  have hqh : 2 ^ (r - 3) + δ < 3 * δ := by omega
  have hW : 4 * δ < 3 * 2 ^ (r - 3) - δ := by omega
  have hsub : (5 * 2 ^ (r - 3) + δ) - δ = 5 * 2 ^ (r - 3) := by omega
  rcases hm_eq with rfl | rfl
  · have hres := ambient_and_native_vanishing_inner_band hF hr_lo hr_hi hD_card hD_pow
      hδ1 hδ_lt le_rfl hqh (Or.inl hW) ha R hR
    rwa [hsub] at hres
  · have hres := ambient_and_native_vanishing_mirror_band hF hr_lo hr_hi hD_card hD_pow
      hδ1 hδ_lt le_rfl hqh (Or.inl hW) ha R hR
    rwa [hsub] at hres

/-- **Unconditional `5n / 8`-Agreement List-Size-`0` on `(11n / 16, 7n / 10) ∪ (4n / 5, 13n / 16)`:**
For every dyadic `5 ≤ r ≤ 31` (`n = 2 ^ r`, nonempty for every `7 ≤ r ≤ 31`, e.g. `m ∈ {89, 103}`
at `n = 128`), if `m ∈ (11n / 16, 7n / 10) ∪ (4n / 5, 13n / 16)`, `a ≠ 0`, and
`R.natDegree ≤ 2 ^ (r - 1)`, then **zero** ambient or native circle codewords agree with
`C a * X ^ m + R` on `5 * 2 ^ (r - 3) = 5n / 8` points of `D` (`NativeListBound ... 0`). -/
theorem nativeListBound_zero_wronskian_band {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {m : ℕ}
    (hm_band : (11 * 2 ^ r < 16 * m ∧ 10 * m < 7 * 2 ^ r) ∨
               (4 * 2 ^ r < 5 * m ∧ 16 * m < 13 * 2 ^ r))
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        5 * 2 ^ (r - 3) ≤
          (D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3))
      (Polynomial.C a * X ^ m + R) 0 := by
  obtain ⟨_, _, hr0⟩ := dyadic_octant_identities (by omega : 4 ≤ r)
  rcases hm_band with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact nativeListBound_zero_wronskian_delta hF hr_lo hr_hi hD_card hD_pow
      (δ := m - 5 * 2 ^ (r - 3)) (by omega) (by omega) (Or.inl (by omega)) ha R hR
  · exact nativeListBound_zero_wronskian_delta hF hr_lo hr_hi hD_card hD_pow
      (δ := 7 * 2 ^ (r - 3) - m) (by omega) (by omega) (Or.inr (by omega)) ha R hR

end InteriorThreeTheoremW
