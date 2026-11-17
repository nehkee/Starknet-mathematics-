import MCAChallenge
import InteriorThree_CanonicalReduction
import InteriorThree_TheoremW

/-!
# Kummer Fibre Lemma (`M-0959`) and Frobenius-Inversion Boundary Obstruction (`Theorem CW`, `M-0963`)
# Closing `SingleMonomialFrobeniusBoundaryCWVanishing` at Every Dyadic `n = 2 ^ r`

Importing `InteriorThree_CanonicalReduction` and `InteriorThree_TheoremW`, this module closes the
second named open sub-lemma `InteriorThreeCanonicalReduction.SingleMonomialFrobeniusBoundaryCWVanishing`
across **every dyadic scale** `n = 2 ^ r` (`5 ≤ r ≤ 31`, `q = 2 ^ (r - 3)`) over the Mersenne circle
field `F` (`Nat.card F = (2 ^ 31 - 1) ^ 2`):

1. **Pure `F[X]` Kummer Fibre Lemma & Frobenius-Inversion Boundary Obstruction
   (`kummer_circle_dvd_of_boundary_cubic`, `frobenius_boundary_cubic_obstruction`):**
   At the Wronskian boundary `4 * h = e + f` (`e = 2 * h + 2 * k`, `f = 2 * h - 2 * k`, `1 ≤ k`,
   `4 * k + 1 ≤ h`, `¬ (3 ∣ e)`, `4 * h < p = ringChar F`) for
   `A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q` (`A` monic of degree `h`, `B.natDegree ≤ h`,
   `B.eval 0 ≠ 0`, `Q ≠ 0 → Q.natDegree + f ≤ 2 * h`):
   - **Primary & Dual Wronskians (`M-0959`):** Setting `P = B * Q` and `R = X ^ f * A * Q - B ^ 3`
     (`A ^ 3 - P = X ^ e * R`, `R.natDegree ≤ h - 2 * k`), the primary Wronskian
     `W = C 3 * A' * P - A * P'` equals `C c * X ^ (e - 1)` with `c ≠ 0` (`A.eval 0 ≠ 0`), while the
     dual Wronskian `C 3 * B' * R - B * R'` equals `X ^ (f - 1) * S` with `S = C c'` constant.
     Forming `X * W + C 3 * S` cancels `X * A' * B * Q` identically and yields
     `A ∣ X ^ e - C α` with `α = -(3 * c') * c⁻¹ ≠ 0`.
   - **Pure-`F[X]` Frobenius-Reversal Cube Symmetry (`M-0963`, `Theorem CW`):** Whenever
     `(p ^ j + 1) % e = 0` (`p ^ j + 1 = e * M`, `β = α ^ M`), `A` divides
     `X ^ (p ^ j + 1) - C β`, hence divides the degree-`≤ h` Frobenius-reversed polynomial
     `T = revSum h (ψ A)` (`(ψ P).coeff i = (P.coeff i) ^ (p ^ j) * β ^ i`). Comparing degree and
     `X ^ h`-coefficients gives `revSum h (ψ A) = C ((A.coeff 0) ^ (p ^ j)) * A`. Cubing transfers
     the upper coefficient gap `(h + 2 * k, e)` of `A ^ 3` across `3 * h - d` (`4 * k + 1 ≤ h`) to
     force `(B * Q).natDegree ≤ h - 2 * k`, contradicting `W.natDegree = e - 1 = 2 * h + 2 * k - 1`.

2. **Closing `SingleMonomialFrobeniusBoundaryCWVanishing` & Two-Sublemma Master Reduction
   (`singleMonomialFrobeniusBoundaryCWVanishing`, `interiorThree_of_residual_and_multi_sublemmas`,
   `nativeListBound_zero_frobenius_boundary`):**
   - Combines GCD-reduced `two_block_cubic_certificate` (`h' < h` handled by `Theorem W`, `h' = h`
     handled by `Theorem CW`) with Frobenius circle inversion (`m = 7 * q - δ` mirror) to prove
     `SingleMonomialFrobeniusBoundaryCWVanishing.{u}` across all universes `u` and all `5 ≤ r ≤ 31`.
   - Reduces `MCAChallenge.InteriorThree.{u} K` (`1 ≤ K ≤ 2 ^ 20`) to ONLY the two remaining named
     sub-lemmas `SingleMonomialResidualCWBound.{u} K` and `MultiMonomialCanonicalCWBound.{u} K`.
-/

namespace InteriorThreeBoundaryCW

open Polynomial Finset InteriorThreeCanonicalReduction InteriorThreeTheoremW

/-! ## Part 1: Pure `F[X]` Truncated Reversal & Iterated Frobenius Helpers -/

private lemma eval_zero_eq_coeff_zero {R : Type*} [Semiring R] (P : R[X]) :
    P.eval 0 = P.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  simp

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

private lemma false_of_A_cube_add_X_pow_B_cube_eq_zero {F : Type*} [Field F]
    {A B : F[X]} {h e : ℕ} (hAm : A.Monic) (hAd : A.natDegree = h)
    (hndvd : ¬ (3 ∣ e)) (heq : A ^ 3 + X ^ e * B ^ 3 = 0) : False := by
  have hA3_monic : (A ^ 3).Monic := hAm.pow 3
  have hA3_ne : A ^ 3 ≠ 0 := hA3_monic.ne_zero
  have hA3_deg : (A ^ 3).natDegree = 3 * h := by
    rw [Polynomial.natDegree_pow A 3, hAd]
  have hneg : A ^ 3 = -(X ^ e * B ^ 3) := eq_neg_of_add_eq_zero_left heq
  have hB_ne : B ≠ 0 := by
    intro hB0
    rw [hB0, zero_pow (by decide : 3 ≠ 0), mul_zero, neg_zero] at hneg
    exact hA3_ne hneg
  have hB3_ne : B ^ 3 ≠ 0 := pow_ne_zero 3 hB_ne
  have hXe_ne : (X : F[X]) ^ e ≠ 0 := pow_ne_zero e Polynomial.X_ne_zero
  have hrhs_deg : (-(X ^ e * B ^ 3)).natDegree = e + 3 * B.natDegree := by
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_mul hXe_ne hB3_ne,
      Polynomial.natDegree_X_pow, Polynomial.natDegree_pow B 3]
  have hdeg_eq : 3 * h = e + 3 * B.natDegree := by
    rw [← hA3_deg, hneg, hrhs_deg]
  apply hndvd
  exact ⟨h - B.natDegree, by rw [Nat.mul_sub]; omega⟩

private lemma not_dvd_X_pow_of_eval_zero_ne_zero {F : Type*} [Field F] {A : F[X]}
    (hA_deg : 0 < A.natDegree) (hA0 : A.eval 0 ≠ 0) :
    ∀ n : ℕ, ¬ (A ∣ (X : F[X]) ^ n)
  | 0, ⟨Z, hZ⟩ => by
    have hA_ne : A ≠ 0 := fun h0 ↦ by simp [h0] at hA0
    have hZ_ne : Z ≠ 0 := fun h0 ↦ by simp [h0] at hZ
    have hd := congrArg Polynomial.natDegree hZ
    rw [pow_zero, Polynomial.natDegree_one, Polynomial.natDegree_mul hA_ne hZ_ne] at hd
    omega
  | n + 1, ⟨Z, hZ⟩ => by
    have hev := congrArg (fun P : F[X] ↦ P.eval 0) hZ
    rw [pow_succ, Polynomial.eval_mul, Polynomial.eval_X, mul_zero, Polynomial.eval_mul] at hev
    have hZ0 : Z.eval 0 = 0 := (mul_eq_zero.mp hev.symm).resolve_left hA0
    have hXdvd : (X : F[X]) ∣ Z := by
      rw [Polynomial.X_dvd_iff, ← eval_zero_eq_coeff_zero]
      exact hZ0
    obtain ⟨Z', rfl⟩ := hXdvd
    have hZ' : (X : F[X]) ^ n = A * Z' := by
      apply mul_left_cancel₀ Polynomial.X_ne_zero
      calc (X : F[X]) * X ^ n = X ^ n * X := mul_comm _ _
        _ = X ^ (n + 1) := (pow_succ X n).symm
        _ = A * (X * Z') := hZ
        _ = X * (A * Z') := by ring
    exact not_dvd_X_pow_of_eval_zero_ne_zero hA_deg hA0 n ⟨Z', hZ'⟩

private lemma sub_dvd_pow_sub_pow_ring {R : Type*} [CommRing R] (x y : R) :
    ∀ m : ℕ, (x - y) ∣ (x ^ m - y ^ m)
  | 0 => by simp
  | m + 1 => by
    have hsplit : x ^ (m + 1) - y ^ (m + 1) = (x - y) * x ^ m + y * (x ^ m - y ^ m) := by
      rw [pow_succ', pow_succ']
      ring
    rw [hsplit]
    exact dvd_add (dvd_mul_right (x - y) (x ^ m))
      (dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow_ring x y m) y)

private lemma eq_sum_range_of_natDegree_le {R : Type*} [Semiring R] {P : R[X]} {N : ℕ}
    (hPN : P.natDegree ≤ N) :
    P = ∑ i ∈ Finset.range (N + 1), Polynomial.C (P.coeff i) * X ^ i := by
  ext d
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hd : d ≤ N
  · have hmem : d ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
    rw [Finset.sum_eq_single d
      (fun b _ hbd ↦ by simp only [hbd.symm, ↓reduceIte])
      (fun hnot ↦ absurd hmem hnot)]
    simp only [↓reduceIte]
  · rw [Finset.sum_eq_zero]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · intro b hb
      have hb_lt : b < N + 1 := Finset.mem_range.mp hb
      have hne : d ≠ b := by omega
      simp only [hne, ↓reduceIte]

/-- Truncated degree-`N` polynomial reversal `∑_{i=0}^N C (P.coeff i) * X ^ (N - i)`. -/
private noncomputable def revSum {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) : R[X] :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.C (P.coeff i) * X ^ (N - i)

private lemma revSum_zero {R : Type*} [Semiring R] (N : ℕ) :
    revSum N (0 : R[X]) = 0 := by
  simp [revSum]

private lemma revSum_add {R : Type*} [Semiring R] (N : ℕ) (U V : R[X]) :
    revSum N (U + V) = revSum N U + revSum N V := by
  simp only [revSum, Polynomial.coeff_add, map_add, add_mul, Finset.sum_add_distrib]

private lemma revSum_sum {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    (N : ℕ) (s : Finset ι) (g : ι → R[X]) :
    revSum N (∑ x ∈ s, g x) = ∑ x ∈ s, revSum N (g x) := by
  induction s using Finset.induction_on with
  | empty => simp [revSum_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, revSum_add, ih, Finset.sum_insert ha]

private lemma revSum_C_mul_X_pow {R : Type*} [Semiring R] {N s : ℕ} (c : R) (hs : s ≤ N) :
    revSum N (Polynomial.C c * X ^ s) = Polynomial.C c * X ^ (N - s) := by
  unfold revSum
  have hmem : s ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hs)
  rw [Finset.sum_eq_single s]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [↓reduceIte, mul_one]
  · intro i _ his
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [his, ↓reduceIte, mul_zero, map_zero, zero_mul]
  · intro hnot
    exact absurd hmem hnot

private lemma revSum_coeff {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) {d : ℕ} (hd : d ≤ N) :
    (revSum N P).coeff d = P.coeff (N - d) := by
  unfold revSum
  rw [Polynomial.finsetSum_coeff]
  have hmem : N - d ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single (N - d)]
  · have heq : N - (N - d) = d := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, heq]
    simp only [↓reduceIte, mul_one]
  · intro i hi hne
    have hi_le : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hne' : ¬ (d = N - i) := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [hne', ↓reduceIte, mul_zero]
  · intro hnot
    exact absurd hmem hnot

private lemma revSum_natDegree_le {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) :
    (revSum N P).natDegree ≤ N := by
  unfold revSum
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le N, fun i _ ↦ ?_⟩
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  exact le_trans (Polynomial.natDegree_X_pow_le _) (by omega)

private lemma revSum_mul {R : Type*} [CommSemiring R] {P Q : R[X]} {m n : ℕ}
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    revSum (m + n) (P * Q) = revSum m P * revSum n Q := by
  have hP_sum := eq_sum_range_of_natDegree_le hP
  have hQ_sum := eq_sum_range_of_natDegree_le hQ
  conv_lhs => rw [hP_sum, hQ_sum, Finset.sum_mul_sum]
  rw [revSum_sum]
  conv_rhs => rw [revSum, revSum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  rw [revSum_sum]
  refine Finset.sum_congr rfl (fun l hl ↦ ?_)
  have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hl_le : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hterm :
      (Polynomial.C (P.coeff i) * X ^ i) * (Polynomial.C (Q.coeff l) * X ^ l) =
        Polynomial.C (P.coeff i * Q.coeff l) * X ^ (i + l) := by
    rw [map_mul, pow_add]
    ring
  rw [hterm, revSum_C_mul_X_pow (P.coeff i * Q.coeff l) (by omega), map_mul,
    show m + n - (i + l) = (m - i) + (n - l) by omega, pow_add]
  ring

/-- Iterated Frobenius endomorphism `x ↦ x ^ (p ^ j)` on a characteristic-`p` commutative semiring. -/
private def frobPow (R : Type*) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    ℕ → (R →+* R)
  | 0 => RingHom.id R
  | j + 1 => (frobenius R p).comp (frobPow R p j)

private lemma frobPow_apply {R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (j : ℕ) (x : R) :
    frobPow R p j x = x ^ (p ^ j) := by
  induction j with
  | zero => simp [frobPow]
  | succ j ih =>
    change (frobPow R p j x) ^ p = x ^ (p ^ (j + 1))
    rw [ih, ← pow_mul, pow_succ]

/-! ## Part 2: Result 8 Kummer Fibre Lemma (`M-0959`) & Result 12 `Theorem CW` (`M-0963`) -/

/-- **Result 8 Kummer Fibre Lemma (`M-0959`):**
At the Wronskian boundary `4 * h = e + f` (`e = 2 * h + 2 * k`, `f = 2 * h - 2 * k`, `1 ≤ k`,
`4 * k + 1 ≤ h`, `¬ (3 ∣ e)`, `ringChar F = 0 ∨ 4 * h < ringChar F`), any solution `(A, B, Q)` to
`A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q` with `A` monic of degree `h`,
`B.natDegree ≤ h`, `B.eval 0 ≠ 0`, and `(Q ≠ 0 → Q.natDegree + f ≤ 2 * h)` satisfies:
- `A.eval 0 ≠ 0`,
- `W := C 3 * A.derivative * (B * Q) - A * (B * Q).derivative = C c * X ^ (e - 1)` for some `c ≠ 0`,
- `(A ^ 3).coeff m = (B * Q).coeff m` for all `m < e`, and
- **`A ∣ X ^ e - C α`** for some nonzero scalar `α : F` (`α ≠ 0`). -/
theorem kummer_circle_dvd_of_boundary_cubic {F : Type*} [Field F] [DecidableEq F]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h4k_le : 4 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd : ¬ (3 ∣ e))
    (hchar4 : ringChar F = 0 ∨ 4 * h < ringChar F)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) :
    A.eval 0 ≠ 0 ∧
    (∃ c : F, c ≠ 0 ∧
      Polynomial.C (3 : F) * A.derivative * (B * Q) - A * (B * Q).derivative =
        Polynomial.C c * X ^ (e - 1)) ∧
    (∀ m < e, (A ^ 3).coeff m = (B * Q).coeff m) ∧
    (∃ α : F, α ≠ 0 ∧ A ∣ (X ^ e - Polynomial.C α)) := by
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, mul_zero] at hident
    exact false_of_A_cube_add_X_pow_B_cube_eq_zero hAm hAd hndvd hident
  have hQ_le : Q.natDegree ≤ 2 * k := by
    have hqb := hQd hQ_ne
    omega
  have hB_ne : B ≠ 0 := fun h0 ↦ hB0 (by simp [h0])
  set P : F[X] := B * Q
  have hP_ne : P ≠ 0 := mul_ne_zero hB_ne hQ_ne
  have hP_le : P.natDegree ≤ h + 2 * k := by
    rw [Polynomial.natDegree_mul hB_ne hQ_ne]
    omega
  set R : F[X] := X ^ f * A * Q - B ^ 3
  have hident' : A ^ 3 + X ^ e * B ^ 3 = (X ^ e * X ^ f * A + B) * Q := by
    rw [← pow_add]
    exact hident
  have hP_eq : P = A ^ 3 - X ^ e * R := by
    dsimp [P, R]
    linear_combination -hident'
  have hA3_monic : (A ^ 3).Monic := hAm.pow 3
  have hA3_deg : (A ^ 3).natDegree = 3 * h := by
    rw [Polynomial.natDegree_pow A 3, hAd]
  have hR_le : R.natDegree ≤ h - 2 * k := by
    by_cases hR0 : R = 0
    · simp [hR0]
    · have hXe_ne : (X : F[X]) ^ e ≠ 0 := pow_ne_zero e Polynomial.X_ne_zero
      have hXeR_eq : X ^ e * R = A ^ 3 - P := by linear_combination hP_eq
      have hrhs_deg : (A ^ 3 - P).natDegree ≤ 3 * h := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_of_eq hA3_deg) ?_)
        omega
      have hlhs_deg : (X ^ e * R).natDegree = e + R.natDegree :=
        (Polynomial.natDegree_mul hXe_ne hR0).trans (by rw [Polynomial.natDegree_X_pow])
      rw [← hXeR_eq, hlhs_deg] at hrhs_deg
      omega
  set e1 : ℕ := e - 1
  have he1_succ : e1 + 1 = e := by omega
  set W : F[X] := Polynomial.C (3 : F) * A.derivative * P - A * P.derivative
  set V : F[X] := Polynomial.C ((e1 + 1 : ℕ) : F) * A * R +
      X * (A * R.derivative - Polynomial.C (3 : F) * A.derivative * R)
  have hW_factor : W = X ^ e1 * V := by
    have hP_eq1 : P = A ^ 3 - X ^ (e1 + 1) * R := by rw [he1_succ]; exact hP_eq
    have hP_deriv :
        P.derivative =
          Polynomial.C (3 : F) * A ^ 2 * A.derivative -
            (Polynomial.C ((e1 + 1 : ℕ) : F) * X ^ e1 * R + X ^ (e1 + 1) * R.derivative) := by
      rw [hP_eq1, Polynomial.derivative_sub, Polynomial.derivative_pow A 3,
        Polynomial.derivative_mul, Polynomial.derivative_X_pow (e1 + 1)]
      simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
    dsimp [W, V]
    rw [hP_deriv, hP_eq1, pow_succ X e1]
    ring
  have hA'_deg : A.derivative.natDegree ≤ h - 1 := by
    rw [← hAd]
    exact Polynomial.natDegree_derivative_le A
  have hW_le_e1 : W.natDegree ≤ e1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have h3A' : (Polynomial.C (3 : F) * A.derivative).natDegree ≤ h - 1 :=
        le_trans (Polynomial.natDegree_C_mul_le (3 : F) A.derivative) hA'_deg
      omega
    · by_cases hP'0 : P.derivative = 0
      · rw [hP'0, mul_zero, Polynomial.natDegree_zero]; omega
      · have hP_pos : 0 < P.natDegree := by
          by_contra hp0
          have hpz : P.natDegree = 0 := Nat.eq_zero_of_not_pos hp0
          rw [Polynomial.eq_C_of_natDegree_eq_zero hpz, Polynomial.derivative_C] at hP'0
          exact hP'0 rfl
        have hP'_le : P.derivative.natDegree ≤ P.natDegree - 1 :=
          Polynomial.natDegree_derivative_le P
        refine le_trans Polynomial.natDegree_mul_le ?_
        rw [hAd]
        omega
  have hV_deg0 : V.natDegree = 0 := by
    by_cases hV0 : V = 0
    · simp [hV0]
    · have hXe1_ne : (X : F[X]) ^ e1 ≠ 0 := pow_ne_zero e1 Polynomial.X_ne_zero
      have hW_deg : W.natDegree = e1 + V.natDegree := by
        rw [hW_factor, Polynomial.natDegree_mul hXe1_ne hV0, Polynomial.natDegree_X_pow]
      omega
  set c : F := V.coeff 0
  have hV_eq_C : V = Polynomial.C c := Polynomial.eq_C_of_natDegree_eq_zero hV_deg0
  have hW_eq : W = Polynomial.C c * X ^ e1 := by
    rw [hW_factor, hV_eq_C, mul_comm]
  have hchar3 : ringChar F = 0 ∨ 3 * h < ringChar F := by
    rcases hchar4 with hc0 | hlt4
    · exact Or.inl hc0
    · exact Or.inr (by omega)
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hW0 : W = 0 := by rw [hW_eq, hc0, map_zero, zero_mul]
    have hA3_wronsk : (A ^ 3).derivative * P = A ^ 3 * P.derivative := by
      have hd3 : (A ^ 3).derivative = Polynomial.C (3 : F) * A ^ 2 * A.derivative := by
        rw [Polynomial.derivative_pow A 3]
        simp only [Nat.cast_ofNat]
      rw [hd3]
      linear_combination A ^ 2 * hW0
    have hA3_dvd_P : A ^ 3 ∣ P :=
      dvd_of_derivative_mul_eq hA3_monic.ne_zero (le_of_eq hA3_deg) hchar3 hA3_wronsk
    have hle_deg := Polynomial.natDegree_le_of_dvd hA3_dvd_P hP_ne
    rw [hA3_deg] at hle_deg
    omega
  have hA0_ne : A.eval 0 ≠ 0 := by
    intro hA0
    have hev := congrArg (fun Z : F[X] ↦ Z.eval 0) hV_eq_C
    dsimp [V] at hev
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      hA0, mul_zero, zero_mul, Polynomial.eval_mul, Polynomial.eval_X, zero_mul,
      add_zero, Polynomial.eval_C] at hev
    exact hc_ne hev.symm
  have hA3_coeff_lt : ∀ m < e, (A ^ 3).coeff m = P.coeff m := by
    intro m hm_lt
    have hA3_split : A ^ 3 = P + X ^ e * R := by linear_combination -hP_eq
    rw [hA3_split, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
    have hnot : ¬ (e ≤ m) := by omega
    simp only [hnot, ↓reduceIte, add_zero]
  -- Dual Wronskian on `R = X ^ f * A * Q - B ^ 3`
  set f1 : ℕ := f - 1
  have hf1_succ : f1 + 1 = f := by omega
  set W_dual : F[X] := Polynomial.C (3 : F) * B.derivative * R - B * R.derivative
  set S : F[X] :=
    Q * (Polynomial.C (3 : F) * A * X * B.derivative - B * X * A.derivative -
      Polynomial.C ((f1 + 1 : ℕ) : F) * A * B) - A * B * X * Q.derivative
  have hW_dual_factor : W_dual = X ^ f1 * S := by
    have hR_eq1 : R = X ^ (f1 + 1) * A * Q - B ^ 3 := by rw [hf1_succ]
    have hR_deriv :
        R.derivative =
          (Polynomial.C ((f1 + 1 : ℕ) : F) * X ^ f1 * A + X ^ (f1 + 1) * A.derivative) * Q +
            X ^ (f1 + 1) * A * Q.derivative -
            Polynomial.C (3 : F) * B ^ 2 * B.derivative := by
      rw [hR_eq1, Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_mul, Polynomial.derivative_X_pow (f1 + 1),
        Polynomial.derivative_pow B 3]
      simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
    dsimp [W_dual, S]
    rw [hR_deriv, hR_eq1, pow_succ X f1]
    ring
  have hW_dual_le : W_dual.natDegree ≤ f1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · by_cases hB'0 : B.derivative = 0
      · rw [hB'0, mul_zero, zero_mul, Polynomial.natDegree_zero]; omega
      · have hB_pos : 0 < B.natDegree := by
          by_contra hb0
          have hbz : B.natDegree = 0 := Nat.eq_zero_of_not_pos hb0
          rw [Polynomial.eq_C_of_natDegree_eq_zero hbz, Polynomial.derivative_C] at hB'0
          exact hB'0 rfl
        have hB'_le : B.derivative.natDegree ≤ B.natDegree - 1 :=
          Polynomial.natDegree_derivative_le B
        refine le_trans Polynomial.natDegree_mul_le ?_
        have h3B' : (Polynomial.C (3 : F) * B.derivative).natDegree ≤ h - 1 :=
          le_trans (Polynomial.natDegree_C_mul_le (3 : F) B.derivative) (by omega)
        omega
    · by_cases hR'0 : R.derivative = 0
      · rw [hR'0, mul_zero, Polynomial.natDegree_zero]; omega
      · have hR_pos : 0 < R.natDegree := by
          by_contra hr0
          have hrz : R.natDegree = 0 := Nat.eq_zero_of_not_pos hr0
          rw [Polynomial.eq_C_of_natDegree_eq_zero hrz, Polynomial.derivative_C] at hR'0
          exact hR'0 rfl
        have hR'_le : R.derivative.natDegree ≤ R.natDegree - 1 :=
          Polynomial.natDegree_derivative_le R
        refine le_trans Polynomial.natDegree_mul_le ?_
        omega
  have hS_deg0 : S.natDegree = 0 := by
    by_cases hS0 : S = 0
    · simp [hS0]
    · have hXf1_ne : (X : F[X]) ^ f1 ≠ 0 := pow_ne_zero f1 Polynomial.X_ne_zero
      have hWd_deg : W_dual.natDegree = f1 + S.natDegree := by
        rw [hW_dual_factor, Polynomial.natDegree_mul hXf1_ne hS0, Polynomial.natDegree_X_pow]
      omega
  set c' : F := S.coeff 0
  have hS_eq_C : S = Polynomial.C c' := Polynomial.eq_C_of_natDegree_eq_zero hS_deg0
  -- Exact cancellation of `X * A.derivative * B * Q` in `X * W + C 3 * S`
  set K_quot : F[X] :=
    Polynomial.C (8 : F) * X * B.derivative * Q -
      Polynomial.C (3 * ((f1 + 1 : ℕ) : F)) * B * Q -
      Polynomial.C (4 : F) * B * X * Q.derivative
  have hcomb : X * W + Polynomial.C (3 : F) * S = A * K_quot := by
    have hPQ_deriv : P.derivative = B.derivative * Q + B * Q.derivative := by
      dsimp [P]
      exact Polynomial.derivative_mul
    dsimp [W, S, K_quot]
    rw [hPQ_deriv]
    dsimp [P]
    simp only [map_mul, map_ofNat]
    ring
  have hcomb_lhs :
      X * W + Polynomial.C (3 : F) * S = Polynomial.C c * X ^ e + Polynomial.C (3 * c') := by
    rw [hW_eq, hS_eq_C, ← map_mul Polynomial.C (3 : F) c']
    calc X * (Polynomial.C c * X ^ e1) + Polynomial.C (3 * c')
        = Polynomial.C c * (X ^ e1 * X) + Polynomial.C (3 * c') := by ring
      _ = Polynomial.C c * X ^ (e1 + 1) + Polynomial.C (3 * c') := by rw [← pow_succ X e1]
      _ = Polynomial.C c * X ^ e + Polynomial.C (3 * c') := by rw [he1_succ]
  set α : F := -(3 * c') * c⁻¹
  have hA_dvd : A ∣ (X ^ e - Polynomial.C α) := by
    refine ⟨Polynomial.C c⁻¹ * K_quot, ?_⟩
    have hmul :
        Polynomial.C c⁻¹ * (Polynomial.C c * X ^ e + Polynomial.C (3 * c')) =
          X ^ e - Polynomial.C α := by
      dsimp [α]
      calc Polynomial.C c⁻¹ * (Polynomial.C c * X ^ e + Polynomial.C (3 * c'))
          = (Polynomial.C c⁻¹ * Polynomial.C c) * X ^ e +
              Polynomial.C c⁻¹ * Polynomial.C (3 * c') := by ring
        _ = Polynomial.C (c⁻¹ * c) * X ^ e + Polynomial.C (c⁻¹ * (3 * c')) := by
            rw [← map_mul, ← map_mul]
        _ = X ^ e - Polynomial.C (-(3 * c') * c⁻¹) := by
            rw [inv_mul_cancel₀ hc_ne, map_one, one_mul, sub_eq_add_neg, ← map_neg]
            congr 2
            ring
    calc X ^ e - Polynomial.C α
        = Polynomial.C c⁻¹ * (Polynomial.C c * X ^ e + Polynomial.C (3 * c')) := hmul.symm
      _ = Polynomial.C c⁻¹ * (X * W + Polynomial.C (3 : F) * S) := by rw [← hcomb_lhs]
      _ = Polynomial.C c⁻¹ * (A * K_quot) := by rw [hcomb]
      _ = A * (Polynomial.C c⁻¹ * K_quot) := by ring
  have hα_ne : α ≠ 0 := by
    intro hα0
    rw [hα0, map_zero, sub_zero] at hA_dvd
    exact not_dvd_X_pow_of_eval_zero_ne_zero (by rw [hAd]; omega) hA0_ne e hA_dvd
  exact ⟨hA0_ne, ⟨c, hc_ne, hW_eq⟩, hA3_coeff_lt, ⟨α, hα_ne, hA_dvd⟩⟩

/-- **`Theorem CW` (`M-0963`, Frobenius-Inversion Wronskian-Boundary Obstruction):**
Over any field `F` of prime characteristic `p` (`4 * h < p`) where `e = 2 * h + 2 * k`,
`f = 2 * h - 2 * k`, `1 ≤ k`, `4 * k + 1 ≤ h`, `¬ (3 ∣ e)`, and `(p ^ j + 1) % e = 0` for some
`j : ℕ`, there is NO solution `(A, B, Q)` to `A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q`
with `A` monic of degree `h`, `B.natDegree ≤ h`, `B.eval 0 ≠ 0`, and
`(Q ≠ 0 → Q.natDegree + f ≤ 2 * h)`. -/
theorem frobenius_boundary_cubic_obstruction {F : Type*} [Field F] [DecidableEq F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h4k_le : 4 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd : ¬ (3 ∣ e)) (hp_gt : 4 * h < p)
    (hfrob_inv : ∃ j : ℕ, (p ^ j + 1) % e = 0)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) : False := by
  have hrchar : ringChar F = p := CharP.eq F (ringChar.charP F) ‹CharP F p›
  obtain ⟨hA0_ne, ⟨c, hc_ne, hW_eq⟩, hA3_coeff_lt, ⟨α, _, hA_dvd_kummer⟩⟩ :=
    kummer_circle_dvd_of_boundary_cubic hk_pos h4k_le he_eq hf_eq hndvd
      (Or.inr (by rw [hrchar]; exact hp_gt)) hAm hAd hBd hB0 hQd hident
  obtain ⟨j, hj_mod⟩ := hfrob_inv
  obtain ⟨M, hM_eq⟩ := Nat.dvd_of_mod_eq_zero hj_mod
  set β : F := α ^ M
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpj_pos : 0 < p ^ j := pow_pos hp_pos j
  -- Ring hom `ψ : F[X] →+* F[X]` sending `C a ↦ C (a ^ (p ^ j))` and `X ↦ C β * X`
  let ψ : F[X] →+* F[X] :=
    Polynomial.eval₂RingHom (Polynomial.C.comp (frobPow F p j)) (Polynomial.C β * X)
  have hψ_monom : ∀ (a : F) (i : ℕ),
      ψ (Polynomial.C a * X ^ i) = Polynomial.C (a ^ (p ^ j) * β ^ i) * X ^ i := by
    intro a i
    rw [map_mul, map_pow]
    dsimp [ψ]
    simp only [Polynomial.eval₂_C, Polynomial.eval₂_X,
      RingHom.coe_comp, Function.comp_apply, frobPow_apply]
    rw [mul_pow, ← map_pow Polynomial.C β i, ← mul_assoc, ← map_mul]
  have hψ_coeff : ∀ (Z : F[X]) (d : ℕ),
      (ψ Z).coeff d = (Z.coeff d) ^ (p ^ j) * β ^ d := by
    intro Z d
    set N : ℕ := max Z.natDegree d
    have hZN : Z.natDegree ≤ N := le_max_left _ _
    have hdN : d ≤ N := le_max_right _ _
    conv_lhs => rw [eq_sum_range_of_natDegree_le hZN, map_sum]
    rw [Polynomial.finsetSum_coeff]
    have hmem : d ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hdN)
    rw [Finset.sum_eq_single d]
    · rw [hψ_monom, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp only [↓reduceIte, mul_one]
    · intro i _ hid
      rw [hψ_monom, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp only [hid.symm, ↓reduceIte, mul_zero]
    · intro hnot
      exact absurd hmem hnot
  have hψA_deg : (ψ A).natDegree ≤ h := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro d hd_gt
    rw [hψ_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hAd]; exact hd_gt),
      zero_pow hpj_pos.ne', zero_mul]
  -- Show `A ∣ revSum h (ψ A)` in `F[X]`
  set T : F[X] := revSum h (ψ A)
  have hA_dvd_pj1 : A ∣ (X ^ (p ^ j + 1) - Polynomial.C β) := by
    have hdvd_pow : (X ^ e - Polynomial.C α) ∣ ((X ^ e) ^ M - (Polynomial.C α) ^ M) :=
      sub_dvd_pow_sub_pow_ring (X ^ e) (Polynomial.C α) M
    rw [← pow_mul, ← hM_eq, ← map_pow Polynomial.C α M] at hdvd_pow
    exact dvd_trans hA_dvd_kummer hdvd_pow
  have hXh_Apj :
      X ^ h * A ^ (p ^ j) =
        ∑ i ∈ Finset.range (h + 1),
          Polynomial.C ((A.coeff i) ^ (p ^ j)) * X ^ (h - i) * (X ^ (p ^ j + 1)) ^ i := by
    have hA_sum := eq_sum_range_of_natDegree_le (le_of_eq hAd)
    have hApj :
        A ^ (p ^ j) =
          ∑ i ∈ Finset.range (h + 1),
            Polynomial.C ((A.coeff i) ^ (p ^ j)) * (X ^ (p ^ j)) ^ i := by
      rw [← frobPow_apply p j A]
      conv_lhs => rw [hA_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [map_mul, frobPow_apply, frobPow_apply, ← map_pow, pow_right_comm]
    rw [hApj, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi ↦ ?_)
    have hi_le : i ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hX_split :
        (X : F[X]) ^ h * ((X : F[X]) ^ (p ^ j)) ^ i =
          (X : F[X]) ^ (h - i) * ((X : F[X]) ^ (p ^ j + 1)) ^ i := by
      calc (X : F[X]) ^ h * ((X : F[X]) ^ (p ^ j)) ^ i
          = ((X : F[X]) ^ (h - i) * (X : F[X]) ^ i) * ((X : F[X]) ^ (p ^ j)) ^ i := by
              rw [← pow_add, Nat.sub_add_cancel hi_le]
        _ = (X : F[X]) ^ (h - i) * ((X : F[X]) ^ i * ((X : F[X]) ^ (p ^ j)) ^ i) := by ring
        _ = (X : F[X]) ^ (h - i) * ((X : F[X]) * (X : F[X]) ^ (p ^ j)) ^ i := by rw [mul_pow]
        _ = (X : F[X]) ^ (h - i) * ((X : F[X]) ^ (p ^ j + 1)) ^ i := by rw [pow_succ' X (p ^ j)]
    calc X ^ h * (Polynomial.C ((A.coeff i) ^ (p ^ j)) * (X ^ (p ^ j)) ^ i)
        = Polynomial.C ((A.coeff i) ^ (p ^ j)) * (X ^ h * (X ^ (p ^ j)) ^ i) := by ring
      _ = Polynomial.C ((A.coeff i) ^ (p ^ j)) * X ^ (h - i) * (X ^ (p ^ j + 1)) ^ i := by
          rw [hX_split, mul_assoc]
  have hT_expand :
      T = ∑ i ∈ Finset.range (h + 1),
            Polynomial.C ((A.coeff i) ^ (p ^ j)) * X ^ (h - i) * (Polynomial.C β) ^ i := by
    dsimp [T]
    unfold revSum
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [hψ_coeff, map_mul, ← map_pow Polynomial.C β i]
    ring
  have hA_dvd_diff : A ∣ (X ^ h * A ^ (p ^ j) - T) := by
    rw [hXh_Apj, hT_expand, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum (fun i _ ↦ ?_)
    rw [← mul_sub]
    refine dvd_mul_of_dvd_right ?_ _
    exact dvd_trans hA_dvd_pj1 (sub_dvd_pow_sub_pow_ring (X ^ (p ^ j + 1)) (Polynomial.C β) i)
  have hA_dvd_lhs : A ∣ (X ^ h * A ^ (p ^ j)) :=
    dvd_mul_of_dvd_right (dvd_pow_self A hpj_pos.ne') (X ^ h)
  have hA_dvd_T : A ∣ T := by
    obtain ⟨U1, hU1⟩ := hA_dvd_lhs
    obtain ⟨U2, hU2⟩ := hA_dvd_diff
    refine ⟨U1 - U2, ?_⟩
    linear_combination hU1 - hU2
  -- Deduce `T = C c₀ * A` where `c₀ = (A.coeff 0) ^ (p ^ j) ≠ 0`
  set c₀ : F := (A.coeff 0) ^ (p ^ j)
  have hc₀_ne : c₀ ≠ 0 := by
    dsimp [c₀]
    rw [← eval_zero_eq_coeff_zero]
    exact pow_ne_zero (p ^ j) hA0_ne
  have hT_coeff_h : T.coeff h = c₀ := by
    dsimp [T]
    rw [revSum_coeff h (ψ A) le_rfl, Nat.sub_self, hψ_coeff, pow_zero, mul_one]
  have hT_ne : T ≠ 0 := fun h0 ↦ hc₀_ne (by rw [← hT_coeff_h, h0, Polynomial.coeff_zero])
  have hT_deg_le : T.natDegree ≤ h := revSum_natDegree_le h (ψ A)
  obtain ⟨U_T, hUT⟩ := hA_dvd_T
  have hUT_ne : U_T ≠ 0 := fun h0 ↦ hT_ne (by rw [hUT, h0, mul_zero])
  have hUT_deg0 : U_T.natDegree = 0 := by
    have hd : T.natDegree = h + U_T.natDegree := by
      rw [hUT, Polynomial.natDegree_mul hAm.ne_zero hUT_ne, hAd]
    omega
  have hUT_eq_C : U_T = Polynomial.C (U_T.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hUT_deg0
  have hUT_c0 : U_T.coeff 0 = c₀ := by
    have hch := congrArg (fun Z : F[X] ↦ Z.coeff h) hUT
    rw [hT_coeff_h, hUT_eq_C, mul_comm A, Polynomial.coeff_C_mul, ← hAd,
      show A.coeff A.natDegree = 1 from hAm.leadingCoeff, mul_one] at hch
    exact hch.symm
  have hT_eq_A : T = Polynomial.C c₀ * A := by
    rw [hUT, hUT_eq_C, hUT_c0, mul_comm]
  -- Cube `revSum h (ψ A) = C c₀ * A` to obtain coefficient symmetry of `A ^ 3`
  have hrev_cube : revSum (3 * h) (ψ (A ^ 3)) = Polynomial.C (c₀ ^ 3) * A ^ 3 := by
    have hψA2_deg : ((ψ A) ^ 2).natDegree ≤ h + h := by
      rw [sq]
      exact le_trans Polynomial.natDegree_mul_le (by omega)
    have h3h : (h + h) + h = 3 * h := by omega
    calc revSum (3 * h) (ψ (A ^ 3))
        = revSum ((h + h) + h) ((ψ A) ^ 2 * ψ A) := by
            rw [h3h, map_pow, pow_succ (ψ A) 2]
      _ = revSum (h + h) ((ψ A) ^ 2) * revSum h (ψ A) := revSum_mul hψA2_deg hψA_deg
      _ = (revSum h (ψ A) * revSum h (ψ A)) * revSum h (ψ A) := by
            rw [sq, revSum_mul hψA_deg hψA_deg]
      _ = T ^ 3 := by dsimp [T]; ring
      _ = (Polynomial.C c₀ * A) ^ 3 := by rw [hT_eq_A]
      _ = Polynomial.C (c₀ ^ 3) * A ^ 3 := by rw [mul_pow, ← map_pow]
  -- Transfer upper gap `(h + 2 * k, e)` to show `(B * Q).natDegree ≤ h - 2 * k`
  set P : F[X] := B * Q
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, mul_zero] at hident
    exact false_of_A_cube_add_X_pow_B_cube_eq_zero hAm hAd hndvd hident
  have hB_ne : B ≠ 0 := fun h0 ↦ hB0 (by simp [h0])
  have hP_le : P.natDegree ≤ h + 2 * k := by
    have hqb := hQd hQ_ne
    rw [Polynomial.natDegree_mul hB_ne hQ_ne]
    omega
  have hP_low : P.natDegree ≤ h - 2 * k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro d hd_gt
    by_cases hd_hi : h + 2 * k < d
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP_le hd_hi)
    · push Not at hd_hi
      have hd_lt_e : d < e := by omega
      have hd_le_3h : d ≤ 3 * h := by omega
      have hm_gt : h + 2 * k < 3 * h - d := by omega
      have hm_lt_e : 3 * h - d < e := by omega
      have hA3_mirror_zero : (A ^ 3).coeff (3 * h - d) = 0 := by
        rw [hA3_coeff_lt (3 * h - d) hm_lt_e]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP_le hm_gt)
      have hsym := congrArg (fun Z : F[X] ↦ Z.coeff d) hrev_cube
      rw [revSum_coeff (3 * h) (ψ (A ^ 3)) hd_le_3h, hψ_coeff, hA3_mirror_zero,
        zero_pow hpj_pos.ne', zero_mul, Polynomial.coeff_C_mul] at hsym
      have hA3_d_zero : (A ^ 3).coeff d = 0 :=
        (mul_eq_zero.mp hsym.symm).resolve_left (pow_ne_zero 3 hc₀_ne)
      rw [← hA3_coeff_lt d hd_lt_e]
      exact hA3_d_zero
  -- Contradict `W.natDegree = e - 1 = 2 * h + 2 * k - 1`
  set W : F[X] := Polynomial.C (3 : F) * A.derivative * P - A * P.derivative
  have hA'_deg : A.derivative.natDegree ≤ h - 1 := by
    rw [← hAd]
    exact Polynomial.natDegree_derivative_le A
  have hW_deg_small : W.natDegree ≤ 2 * h - 2 * k - 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have h3A' : (Polynomial.C (3 : F) * A.derivative).natDegree ≤ h - 1 :=
        le_trans (Polynomial.natDegree_C_mul_le (3 : F) A.derivative) hA'_deg
      omega
    · by_cases hP'0 : P.derivative = 0
      · rw [hP'0, mul_zero, Polynomial.natDegree_zero]; omega
      · have hP_pos : 0 < P.natDegree := by
          by_contra hp0
          have hpz : P.natDegree = 0 := Nat.eq_zero_of_not_pos hp0
          rw [Polynomial.eq_C_of_natDegree_eq_zero hpz, Polynomial.derivative_C] at hP'0
          exact hP'0 rfl
        have hP'_le : P.derivative.natDegree ≤ P.natDegree - 1 :=
          Polynomial.natDegree_derivative_le P
        refine le_trans Polynomial.natDegree_mul_le ?_
        rw [hAd]
        omega
  have hW_deg_exact : W.natDegree = e - 1 := by
    rw [hW_eq, Polynomial.natDegree_C_mul_X_pow (e - 1) c hc_ne]
  omega

/-! ## Part 3: Inner & Mirror Band Vanishing at the Frobenius-Inversion Wronskian Boundary -/

/-- **All-Dyadic Inner-Band Vanishing (`m = 5 * q + δ`) at `4 * h = 3 * q - δ` (`Theorem CW`):**
Across every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), at `4 * h = 3 * q - δ` with `q + h < 3 * δ`,
`2 * (q - δ) < h`, `3 * h < 8 * (q - δ)`, and `((2 ^ 31 - 1) ^ j + 1) % (3 * δ - q) = 0`, no
ambient polynomial of degree `≤ 2 ^ (r - 1)` agrees with `C a * X ^ (5 * q + δ) + R` (`a ≠ 0`,
`R.natDegree ≤ 2 ^ (r - 1)`) on `(5 * q + δ) - h` points of `D`, and `NativeListBound = 0`. -/
theorem ambient_and_native_vanishing_frobenius_boundary_inner {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3))
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hk_lo : 2 * (2 ^ (r - 3) - δ) < h)
    (hk_hi : 3 * h < 8 * (2 ^ (r - 3) - δ))
    (hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R) 0 := by
  have hno_amb :
      ¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
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
    have : CharP F (2 ^ 31 - 1) := ringChar.of_eq hrchar
    have hq_le : q ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) (by omega : r - 3 ≤ 28)
    rcases lt_or_eq_of_le hh'_le_h with hh'_lt | rfl
    · have h3h'_lt_p : 3 * h' < 2 ^ 31 - 1 := by omega
      have hchar : ringChar F = 0 ∨ 3 * h' < ringChar F := Or.inr (by rw [hrchar]; exact h3h'_lt_p)
      exact wronskian_cubic_obstruction hAm hAd hBd hB0 he_pos hf_pos hndvd hchar hQd
        (by omega : 4 * h' < (3 * δ - q) + 4 * (q - δ)) hident
    · set k : ℕ := h' - 2 * (q - δ)
      exact frobenius_boundary_cubic_obstruction (p := 2 ^ 31 - 1) (k := k)
        (by omega : 1 ≤ k)
        (by omega : 4 * k + 1 ≤ h')
        (by omega : 3 * δ - q = 2 * h' + 2 * k)
        (by omega : 4 * (q - δ) = 2 * h' - 2 * k)
        hndvd
        (by omega : 4 * h' < 2 ^ 31 - 1)
        hfrob hAm hAd hBd hB0 hQd hident
  refine ⟨hno_amb, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
    exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- **Mirror Duality (`m = 7 * q - δ`) at `4 * h = 3 * q - δ` (`Theorem CW`):**
Extends `ambient_and_native_vanishing_frobenius_boundary_inner` to the mirror exponent
`m = 7 * 2 ^ (r - 3) - δ` via Mersenne circle Frobenius inversion `x ^ p = x⁻¹` (`p = 2 ^ 31 - 1`). -/
theorem ambient_and_native_vanishing_frobenius_boundary_mirror {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3))
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hk_lo : 2 * (2 ^ (r - 3) - δ) < h)
    (hk_hi : 3 * h < 8 * (2 ^ (r - 3) - δ))
    (hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0)
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
    refine ⟨Nat.zero_le K, fun j _ ↦ ?_⟩
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
  have hinner := ambient_and_native_vanishing_frobenius_boundary_inner hF hr_lo hr_hi
    hD_card hD_pow hδ_pos hδ_lt hqh hbdry hk_lo hk_hi hfrob hap_ne (conjRev R) (hconjRev_deg R)
  have hno_mirror :
      ¬ ∃ P : F[X], P.natDegree ≤ K ∧
        (5 * q + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (7 * q - δ) + R).eval x).card := by
    rintro ⟨P, hP_deg, hcard⟩
    apply hinner.1
    refine ⟨conjRev P, hconjRev_deg P, le_trans hcard (Finset.card_le_card ?_)⟩
    intro x hx
    obtain ⟨hxD, hx_eq⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
    have hxp_inv : x ^ p = x⁻¹ := (hinv x hxD).2
    have hx8q : x ^ (8 * q) = 1 := by rw [← hr0]; exact hD_pow x hxD
    have hx_ne : x ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow (by omega : 8 * q ≠ 0)] at hx8q
      exact zero_ne_one hx8q
    have hx_mirror_pow : x ^ K * (x ^ (7 * q - δ)) ^ p = x ^ (5 * q + δ) := by
      rw [pow_right_comm, hxp_inv]
      have hprod1 : (x⁻¹) ^ (7 * q - δ) * x ^ (7 * q - δ) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hx_ne, one_pow]
      have hexp_eq : K + 8 * q = (5 * q + δ) + (7 * q - δ) := by omega
      calc x ^ K * (x⁻¹) ^ (7 * q - δ)
          = x ^ K * 1 * (x⁻¹) ^ (7 * q - δ) := by rw [mul_one]
        _ = x ^ K * x ^ (8 * q) * (x⁻¹) ^ (7 * q - δ) := by rw [hx8q]
        _ = x ^ (K + 8 * q) * (x⁻¹) ^ (7 * q - δ) := by rw [← pow_add]
        _ = (x ^ (5 * q + δ) * x ^ (7 * q - δ)) * (x⁻¹) ^ (7 * q - δ) := by
            rw [hexp_eq, pow_add]
        _ = x ^ (5 * q + δ) * ((x⁻¹) ^ (7 * q - δ) * x ^ (7 * q - δ)) := by ring
        _ = x ^ (5 * q + δ) := by rw [hprod1, mul_one]
    rw [hconjRev_eval P hP_deg x hxD, hx_eq]
    have hfrob_add :
        ((Polynomial.C a * X ^ (7 * q - δ) + R).eval x) ^ p =
          a ^ p * (x ^ (7 * q - δ)) ^ p + (R.eval x) ^ p := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hm := map_add (frobenius F p) (a * x ^ (7 * q - δ)) (R.eval x)
      change (a * x ^ (7 * q - δ) + R.eval x) ^ p =
        (a * x ^ (7 * q - δ)) ^ p + (R.eval x) ^ p at hm
      rw [hm, mul_pow]
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

/-! ## Part 4: Closing `SingleMonomialFrobeniusBoundaryCWVanishing` & Two-Sublemma Reduction -/

/-- **Main Sub-Lemma Proof (`SingleMonomialFrobeniusBoundaryCWVanishing`):**
Closes Named Open Sub-Lemma 2 (`InteriorThreeCanonicalReduction.SingleMonomialFrobeniusBoundaryCWVanishing`)
from `InteriorThree_CanonicalReduction` across all universes `u` and every dyadic `5 ≤ r ≤ 31`. -/
theorem singleMonomialFrobeniusBoundaryCWVanishing.{u} :
    InteriorThreeCanonicalReduction.SingleMonomialFrobeniusBoundaryCWVanishing.{u} := by
  intro F _ _ hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt m hm_eq γ U
    hu_lt hbdry_u hk_pos_u hk_hi_u hfrob hvalid
  have hr4 : 4 ≤ r := by omega
  obtain ⟨_, _, hr0⟩ := dyadic_octant_identities hr4
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
  set h : ℕ := U.card + δ - 3 * 2 ^ (r - 3)
  have hqh : 2 ^ (r - 3) + h < 3 * δ := by omega
  have hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ := by omega
  have hk_lo : 2 * (2 ^ (r - 3) - δ) < h := by omega
  have hk_hi : 3 * h < 8 * (2 ^ (r - 3) - δ) := by omega
  have hS_eq : (5 * 2 ^ (r - 3) + δ) - h = S.card := by omega
  rcases hm_eq with rfl | rfl
  · exact (ambient_and_native_vanishing_frobenius_boundary_inner hF hr5 hr_hi hD_card hD_pow
      hδ1 hδ_lt hqh hbdry hk_lo hk_hi hfrob one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · exact (ambient_and_native_vanishing_frobenius_boundary_mirror hF hr5 hr_hi hD_card hD_pow
      hδ1 hδ_lt hqh hbdry hk_lo hk_hi hfrob one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩

/-- **Updated Canonical Complement Reduction (`CanonicalInteriorCWBound K` from Two Remaining Sub-Lemmas):**
Combining `InteriorThreeTheoremW.singleMonomialWronskianVanishing` and
`singleMonomialFrobeniusBoundaryCWVanishing`, `CanonicalInteriorCWBound.{u} K` reduces to ONLY
`SingleMonomialResidualCWBound.{u} K` and `MultiMonomialCanonicalCWBound.{u} K`. -/
theorem canonicalInteriorCWBound_of_residual_and_multi_sublemmas.{u} {K : ℕ}
    (hSingleRem : SingleMonomialResidualCWBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    CanonicalInteriorCWBound.{u} K :=
  canonicalInteriorCWBound_of_named_sublemmas
    InteriorThreeTheoremW.singleMonomialWronskianVanishing
    singleMonomialFrobeniusBoundaryCWVanishing
    hSingleRem
    hMulti

/-- **Updated Master Reduction (`MCAChallenge.InteriorThree K` from Two Remaining Sub-Lemmas):**
With both Named Open Sub-Lemma 1 (`Theorem W`) and Named Open Sub-Lemma 2 (`Theorem CW`) proved across
all dyadic `5 ≤ r ≤ 31`, `MCAChallenge.InteriorThree.{u} K` (`1 ≤ K ≤ 2 ^ 20`) reduces directly to
`SingleMonomialResidualCWBound.{u} K` and `MultiMonomialCanonicalCWBound.{u} K`. -/
theorem interiorThree_of_residual_and_multi_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hSingleRem : SingleMonomialResidualCWBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_named_sublemmas
    hK_pos
    hK_cap
    InteriorThreeTheoremW.singleMonomialWronskianVanishing
    singleMonomialFrobeniusBoundaryCWVanishing
    hSingleRem
    hMulti

/-- **Unified `NativeListBound = 0` Corollary on All Frobenius-Inversion Wronskian-Boundary Cells:**
For every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), whenever `4 * h = 3 * q - δ`, `q + h < 3 * δ`,
`2 * (q - δ) < h`, `3 * h < 8 * (q - δ)`, and `((2 ^ 31 - 1) ^ j + 1) % (3 * δ - q) = 0`, both the
inner exponent `m = 5 * q + δ` and the mirror exponent `m = 7 * q - δ` have **zero** ambient or
native circle codewords at agreement `(5 * q + δ) - h` (`NativeListBound = 0`). -/
theorem nativeListBound_zero_frobenius_boundary {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h m : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3))
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hk_lo : 2 * (2 ^ (r - 3) - δ) < h)
    (hk_hi : 3 * h < 8 * (2 ^ (r - 3) - δ))
    (hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0)
    (hm_eq : m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ m + R) 0 := by
  rcases hm_eq with rfl | rfl
  · exact ambient_and_native_vanishing_frobenius_boundary_inner hF hr_lo hr_hi hD_card hD_pow
      hδ_pos hδ_lt hqh hbdry hk_lo hk_hi hfrob ha R hR
  · exact ambient_and_native_vanishing_frobenius_boundary_mirror hF hr_lo hr_hi hD_card hD_pow
      hδ_pos hδ_lt hqh hbdry hk_lo hk_hi hfrob ha R hR

/-- **Concrete `n = 1024` (`r = 10`) Frobenius-Boundary Instances:**
At `n = 1024` (`q = 128`), `δ = 100, h = 71` (`e = 172 ∣ (2 ^ 31 - 1) ^ 3 + 1`, `k = 15`, agreement
`s = 669`, exponents `m ∈ {740, 796}`) has `NativeListBound D 512 669 (C a * X ^ m + R) 0`. -/
theorem nativeListBound_zero_r10_boundary_740_796 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 1024) (hD_pow : ∀ x ∈ D, x ^ 1024 = 1)
    {m : ℕ} (hm : m = 740 ∨ m = 796)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 512) :
    MCAChallenge.NativeListBound D 512 669 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (10 - 3) + 100 ∨ m = 7 * 2 ^ (10 - 3) - 100 := by omega
  have hres :=
    nativeListBound_zero_frobenius_boundary hF (r := 10) (δ := 100) (h := 71) (m := m)
      (by decide) (by decide)
      (by simpa using hD_card) (by simpa using hD_pow)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ⟨3, by decide⟩ hm' ha R (by simpa using hR)
  exact hres.2

end InteriorThreeBoundaryCW
