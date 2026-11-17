import MCAChallenge
import InteriorThree_CanonicalReduction
import InteriorThree_TheoremW
import InteriorThree_BoundaryCW

/-!
# Full Pure-`F[X]` `Theorem CW*` (`M-0964` Result 13 + `M-0965` Result 14)
# Eliminating All `h / k` Restrictions on Frobenius-Inversion Wronskian-Boundary Cells

Importing `InteriorThree_CanonicalReduction`, `InteriorThree_TheoremW`, and
`InteriorThree_BoundaryCW`, this module establishes the full **root-free, `AlgebraicClosure`-free**
`Theorem CW*` (`@rukafe0x` `M-0964` Result 13 + `M-0965` Result 14) across **every dyadic scale**
`n = 2 ^ r` (`5 ≤ r ≤ 31`, `q = 2 ^ (r - 3)`) over the Mersenne circle field `F`
(`Nat.card F = (2 ^ 31 - 1) ^ 2`):

1. **Pure-`F[X]` Lemma U, Three-Term `θ`-Wronskian, and Full `Theorem CW*`
   (`frobenius_boundary_cw_star_cubic_obstruction`):**
   Removes `4 * k + 1 ≤ h` from `InteriorThreeBoundaryCW.frobenius_boundary_cubic_obstruction`,
   proving that for **all** `1 ≤ k` and `2 * k + 1 ≤ h` (`e = 2 * h + 2 * k`, `f = 2 * h - 2 * k`,
   `¬ (3 ∣ e)`, `4 * h < p = ringChar F`, `∃ j, (p ^ j + 1) % e = 0`), there is no solution
   `(A, B, Q)` to `A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q` with `A` monic of degree `h`,
   `B.natDegree ≤ h`, `B.eval 0 ≠ 0`, and `Q ≠ 0 → Q.natDegree + f ≤ 2 * h`:
   - **`4 * k + 1 ≤ h`:** Closed by `InteriorThreeBoundaryCW.frobenius_boundary_cubic_obstruction`.
   - **Pure-`F[X]` Lemma U (`lemma_U_pure_FX`):** Reversing `A ^ 3 = P + X ^ e * U` at `3 * h`
     yields `X ^ (f - 1) ∣ (C 3 * Ũ * Ã' - Ã * Ũ')`, which reverses at `f` to the exact identity
     `C (e : F) * A * U - C 3 * U * θ A + A * θ U = C c₁` (`c₁ ≠ 0`), giving `U.coeff 0 ≠ 0`,
     `IsCoprime A U`, `IsCoprime U (θ U)`, and `A ∣ (C 3 * U * θ A + C c₁)`.
   - **Three-Term `θ`-Wronskian (`three_block_theta_wronskian_dvd`):** On the 3-block split
     `A ^ 3 = L₀ + X ^ f * M₁ + X ^ e * U` (`M₁ ≠ 0`, `M₁.natDegree ≤ 4 * k - h`), factoring
     `X ^ (e + f)` from the `3 × 3` `θ`-Wronskian `W₃` gives `D₃ = C κ * A` (`κ ≠ 0` at the lowest
     nonzero index `m₀` of `M₁`), yielding `A ∣ (w - C λ * U ^ 2)` (`λ ≠ 0`, `w.natDegree ≤ 2 * k`).
   - **Branches `3 * k < h < 4 * k` (`CW⁺`), `h = 4 * k`, and `2 * k + 1 ≤ h ≤ 3 * k` (`CW*`):**
     Closed purely inside `F[X]`.

2. **Unconditional Boundary Vanishing Under Frobenius Inversion & Narrowed Residual Reduction
   (`singleMonomialFullFrobeniusBoundaryCWStarVanishing`,
   `interiorThree_of_nonFrobenius_and_multi_sublemmas`):**
   Eliminates **both** `3 * U.card + 11 * δ < 17 * 2 ^ (r - 3)` and `5 * 2 ^ (r - 3) < U.card + 3 * δ`
   at `4 * U.card + 5 * δ = 15 * 2 ^ (r - 3)` (combining `Theorem CW*` for `5 * q < u + 3 * δ` and
   `8 * q < 3 * u` with `InteriorThreeTheoremW.singleMonomialWronskianVanishing` for `u + 3 * δ < 5 * q`
   or `3 * u < 8 * q`), and instantiates `NativeListBound = 0` on `@rukafe0x`'s `CW⁺` and `CW*`
   cells at `n = 512`, `n = 1024`, and `n = 4096` (`δ ∈ {416, 436, 440}`).
-/

namespace InteriorThreeTheoremCWStar

open Polynomial Finset InteriorThreeCanonicalReduction InteriorThreeTheoremW InteriorThreeBoundaryCW

/-! ## Part 1: Modular Arithmetic, `θ`-Derivative, & Reversal Helpers -/

private def powModAux (rem j e : Nat) : Nat :=
  match j with
  | 0 => 1 % e
  | j + 1 => (rem * powModAux rem j e) % e

private lemma powModAux_eq (a e : Nat) : ∀ j : Nat, powModAux (a % e) j e = (a ^ j) % e
  | 0 => by simp [powModAux]
  | j + 1 => by rw [powModAux, powModAux_eq a e j, ← Nat.mul_mod, pow_succ']

private lemma pow_mul_add_one_mod_eq_zero {a j₁ j₂ e : Nat}
    (h : (powModAux (powModAux (a % e) j₁ e) j₂ e + 1) % e = 0) :
    (a ^ (j₁ * j₂) + 1) % e = 0 := by
  rw [powModAux_eq a e j₁, powModAux_eq (a ^ j₁) e j₂, ← pow_mul, Nat.mod_add_mod] at h
  exact h

private lemma coeff_X_pow_mul_of_le {R : Type*} [Semiring R] (P : R[X]) {n d : ℕ} (h : n ≤ d) :
    (X ^ n * P).coeff d = P.coeff (d - n) := by
  rw [Polynomial.coeff_X_pow_mul']
  simp only [h, ↓reduceIte]

private lemma coeff_X_pow_mul_of_lt {R : Type*} [Semiring R] (P : R[X]) {n d : ℕ} (h : d < n) :
    (X ^ n * P).coeff d = 0 := by
  have hnot : ¬ (n ≤ d) := by omega
  rw [Polynomial.coeff_X_pow_mul']
  simp only [hnot, ↓reduceIte]

private lemma coeff_X_pow_self {R : Type*} [Semiring R] (n : ℕ) :
    ((X : R[X]) ^ n).coeff n = 1 := by
  rw [Polynomial.coeff_X_pow]
  simp only [↓reduceIte]

private lemma coeff_X_pow_of_ne {R : Type*} [Semiring R] {n d : ℕ} (h : d ≠ n) :
    ((X : R[X]) ^ n).coeff d = 0 := by
  rw [Polynomial.coeff_X_pow]
  simp only [h, ↓reduceIte]

private lemma coeff_C_of_ne_zero {R : Type*} [Semiring R] (c : R) {d : ℕ} (h : d ≠ 0) :
    (Polynomial.C c).coeff d = 0 := by
  rw [Polynomial.coeff_C]
  simp only [h, ↓reduceIte]

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

private lemma not_seven_dvd_five_mul_pow_two (k : ℕ) : ¬ (7 ∣ 5 * 2 ^ k) := by
  intro hdvd
  have hp7 : Nat.Prime 7 := by decide
  rcases hp7.dvd_mul.mp hdvd with h5 | h2k
  · omega
  · have h2 : 7 ∣ 2 := hp7.dvd_of_dvd_pow h2k
    omega

private lemma nat_cast_ne_zero_of_pos_lt {F : Type*} [Field F] {p n : ℕ}
    [CharP F p] (hpos : 0 < n) (hlt : n < p) :
    ((n : ℕ) : F) ≠ 0 := by
  intro h0
  have hdvd : p ∣ n := (CharP.cast_eq_zero_iff F p n).mp h0
  have hle : p ≤ n := Nat.le_of_dvd hpos hdvd
  omega

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

/-- Euler operator `θ(P) = X * P.derivative`. -/
private noncomputable def theta {R : Type*} [Semiring R] (P : R[X]) : R[X] :=
  X * P.derivative

private lemma theta_zero {R : Type*} [Semiring R] : theta (0 : R[X]) = 0 := by
  simp [theta]

private lemma theta_C {R : Type*} [Semiring R] (c : R) : theta (Polynomial.C c) = 0 := by
  simp [theta]

private lemma theta_add {R : Type*} [Semiring R] (P Q : R[X]) :
    theta (P + Q) = theta P + theta Q := by
  unfold theta
  rw [Polynomial.derivative_add, mul_add]

private lemma theta_sub {R : Type*} [Ring R] (P Q : R[X]) :
    theta (P - Q) = theta P - theta Q := by
  unfold theta
  rw [Polynomial.derivative_sub, mul_sub]

private lemma theta_C_mul {R : Type*} [CommSemiring R] (c : R) (P : R[X]) :
    theta (Polynomial.C c * P) = Polynomial.C c * theta P := by
  unfold theta
  rw [Polynomial.derivative_C_mul]
  ring

private lemma theta_mul {R : Type*} [CommSemiring R] (P Q : R[X]) :
    theta (P * Q) = theta P * Q + P * theta Q := by
  unfold theta
  rw [Polynomial.derivative_mul]
  ring

private lemma theta_X_pow {R : Type*} [CommSemiring R] :
    ∀ m : ℕ, theta ((X : R[X]) ^ m) = Polynomial.C ((m : ℕ) : R) * X ^ m
  | 0 => by simp [theta]
  | m + 1 => by
    unfold theta
    rw [Polynomial.derivative_X_pow (m + 1), Nat.add_sub_cancel]
    calc (X : R[X]) * (Polynomial.C ((m + 1 : ℕ) : R) * X ^ m)
        = Polynomial.C ((m + 1 : ℕ) : R) * (X ^ m * X) := by ring
      _ = Polynomial.C ((m + 1 : ℕ) : R) * X ^ (m + 1) := by rw [← pow_succ X m]

private lemma theta_X_pow_mul {R : Type*} [CommSemiring R] (m : ℕ) (G : R[X]) :
    theta ((X : R[X]) ^ m * G) = X ^ m * (Polynomial.C ((m : ℕ) : R) * G + theta G) := by
  rw [theta_mul, theta_X_pow]
  ring

private lemma coeff_theta {R : Type*} [CommSemiring R] (P : R[X]) (i : ℕ) :
    (theta P).coeff i = ((i : ℕ) : R) * P.coeff i := by
  cases i with
  | zero =>
    unfold theta
    simp
  | succ n =>
    unfold theta
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one, mul_comm]

private lemma natDegree_theta_le {R : Type*} [Semiring R] (P : R[X]) :
    (theta P).natDegree ≤ P.natDegree := by
  unfold theta
  by_cases h0 : P.derivative = 0
  · simp [h0]
  · have hpos : 0 < P.natDegree := by
      by_contra hp0
      have hpz : P.natDegree = 0 := Nat.eq_zero_of_not_pos hp0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hpz, Polynomial.derivative_C] at h0
      exact h0 rfl
    have hd : P.derivative.natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
    have hX : (X : R[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
    refine le_trans Polynomial.natDegree_mul_le ?_
    omega

/-- Truncated degree-`N` polynomial reversal. -/
private noncomputable def revSum {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) : R[X] :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.C (P.coeff i) * X ^ (N - i)

private lemma revSum_zero {R : Type*} [Semiring R] (N : ℕ) :
    revSum N (0 : R[X]) = 0 := by
  simp [revSum]

private lemma revSum_add {R : Type*} [Semiring R] (N : ℕ) (U V : R[X]) :
    revSum N (U + V) = revSum N U + revSum N V := by
  simp only [revSum, Polynomial.coeff_add, map_add, add_mul, Finset.sum_add_distrib]

private lemma revSum_sub {R : Type*} [Ring R] (N : ℕ) (U V : R[X]) :
    revSum N (U - V) = revSum N U - revSum N V := by
  simp only [revSum, Polynomial.coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

private lemma revSum_C_mul {R : Type*} [CommSemiring R] (N : ℕ) (c : R) (U : R[X]) :
    revSum N (Polynomial.C c * U) = Polynomial.C c * revSum N U := by
  unfold revSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Polynomial.coeff_C_mul, map_mul, mul_assoc]

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
  · intro i hi _
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

private lemma revSum_revSum {R : Type*} [Semiring R] {N : ℕ} {P : R[X]}
    (hPN : P.natDegree ≤ N) :
    revSum N (revSum N P) = P := by
  ext d
  by_cases hd : d ≤ N
  · rw [revSum_coeff N _ hd, revSum_coeff N P (by omega),
      show N - (N - d) = d by omega]
  · have h1 : (revSum N (revSum N P)).natDegree < d :=
      lt_of_le_of_lt (revSum_natDegree_le N _) (by omega)
    have h2 : P.natDegree < d := lt_of_le_of_lt hPN (by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h1, Polynomial.coeff_eq_zero_of_natDegree_lt h2]

private lemma revSum_theta_revSum {R : Type*} [CommRing R] {N : ℕ} {P : R[X]}
    (hPN : P.natDegree ≤ N) :
    revSum N (theta (revSum N P)) = Polynomial.C ((N : ℕ) : R) * P - theta P := by
  ext d
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_theta]
  by_cases hd : d ≤ N
  · rw [revSum_coeff N _ hd, coeff_theta, revSum_coeff N P (by omega),
      show N - (N - d) = d by omega, Nat.cast_sub hd, sub_mul]
  · have h1 : (revSum N (theta (revSum N P))).natDegree < d :=
      lt_of_le_of_lt (revSum_natDegree_le N _) (by omega)
    have h2 : P.natDegree < d := lt_of_le_of_lt hPN (by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt h1,
      Polynomial.coeff_eq_zero_of_natDegree_lt h2]
    ring

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

private lemma coeff_mul_of_vanish_below {R : Type*} [Semiring R] {U V : R[X]} {m₀ : ℕ}
    (hvan : ∀ i < m₀, U.coeff i = 0) :
    (U * V).coeff m₀ = U.coeff m₀ * V.coeff 0 := by
  rw [Polynomial.coeff_mul]
  have hmem : (m₀, 0) ∈ Finset.antidiagonal m₀ := Finset.mem_antidiagonal.mpr (Nat.add_zero m₀)
  rw [Finset.sum_eq_single (m₀, 0)]
  · intro x hx hne
    have hsum : x.1 + x.2 = m₀ := Finset.mem_antidiagonal.mp hx
    have hlt : x.1 < m₀ := by
      by_contra hge
      have hx1 : x.1 = m₀ := by omega
      have hx2 : x.2 = 0 := by omega
      exact hne (Prod.ext hx1 hx2)
    rw [hvan x.1 hlt, zero_mul]
  · intro hnot
    exact absurd hmem hnot

/-! ## Part 2: Generalized Kummer Fibre & Frobenius-Reversal Setup (`2 * k + 1 ≤ h`) -/

private lemma kummer_and_reversal_setup {F : Type*} [Field F] [DecidableEq F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd : ¬ (3 ∣ e)) (hp_gt : 4 * h < p)
    (hfrob_inv : ∃ j : ℕ, (p ^ j + 1) % e = 0)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) :
    ∃ (P U : F[X]) (α β c c₀ : F) (j : ℕ),
      A.coeff 0 ≠ 0 ∧
      P.natDegree ≤ h + 2 * k ∧
      U.Monic ∧
      U.natDegree = h - 2 * k ∧
      A ^ 3 = P + X ^ e * U ∧
      c ≠ 0 ∧
      Polynomial.C (3 : F) * A.derivative * P - A * P.derivative =
        Polynomial.C c * X ^ (e - 1) ∧
      α ≠ 0 ∧
      A ∣ (X ^ e - Polynomial.C α) ∧
      β ≠ 0 ∧
      c₀ ≠ 0 ∧
      (∀ d ≤ 3 * h,
        ((A ^ 3).coeff (3 * h - d)) ^ (p ^ j) * β ^ (3 * h - d) = c₀ ^ 3 * (A ^ 3).coeff d) := by
  have hrchar : ringChar F = p := CharP.eq F (ringChar.charP F) ‹CharP F p›
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
  set U : F[X] := X ^ f * A * Q - B ^ 3
  have hident' : A ^ 3 + X ^ e * B ^ 3 = (X ^ e * X ^ f * A + B) * Q := by
    rw [← pow_add]
    exact hident
  have hP_eq : P = A ^ 3 - X ^ e * U := by
    dsimp [P, U]
    linear_combination -hident'
  have hA3_split : A ^ 3 = P + X ^ e * U := by linear_combination -hP_eq
  have hA3_monic : (A ^ 3).Monic := hAm.pow 3
  have hA3_deg : (A ^ 3).natDegree = 3 * h := by
    rw [Polynomial.natDegree_pow A 3, hAd]
  have hXeU_eq : X ^ e * U = A ^ 3 - P := by linear_combination hP_eq
  have hP_lt_A3 : P.natDegree < (A ^ 3).natDegree := by omega
  have hXeU_deg : (X ^ e * U).natDegree = 3 * h := by
    rw [hXeU_eq, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hP_lt_A3, hA3_deg]
  have hU_ne : U ≠ 0 := by
    intro hU0
    rw [hU0, mul_zero, Polynomial.natDegree_zero] at hXeU_deg
    omega
  have hXe_ne : (X : F[X]) ^ e ≠ 0 := pow_ne_zero e Polynomial.X_ne_zero
  have hU_deg : U.natDegree = h - 2 * k := by
    have hm : (X ^ e * U).natDegree = e + U.natDegree :=
      (Polynomial.natDegree_mul hXe_ne hU_ne).trans (by rw [Polynomial.natDegree_X_pow])
    omega
  have hU_monic : U.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hU_deg]
    have hc3h : (X ^ e * U).coeff (3 * h) = (A ^ 3 - P).coeff (3 * h) := by
      rw [hXeU_eq]
    rw [coeff_X_pow_mul_of_le U (by omega : e ≤ 3 * h),
      show 3 * h - e = h - 2 * k by omega, Polynomial.coeff_sub (A ^ 3) P,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 3 * h), sub_zero,
      ← hA3_deg] at hc3h
    exact hc3h.trans hA3_monic.leadingCoeff
  set e1 : ℕ := e - 1
  have he1_succ : e1 + 1 = e := by omega
  set W : F[X] := Polynomial.C (3 : F) * A.derivative * P - A * P.derivative
  set V : F[X] := Polynomial.C ((e1 + 1 : ℕ) : F) * A * U +
      X * (A * U.derivative - Polynomial.C (3 : F) * A.derivative * U)
  have hW_factor : W = X ^ e1 * V := by
    have hP_eq1 : P = A ^ 3 - X ^ (e1 + 1) * U := by rw [he1_succ]; exact hP_eq
    have hP_deriv :
        P.derivative =
          Polynomial.C (3 : F) * A ^ 2 * A.derivative -
            (Polynomial.C ((e1 + 1 : ℕ) : F) * X ^ e1 * U + X ^ (e1 + 1) * U.derivative) := by
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
  have hchar3 : ringChar F = 0 ∨ 3 * h < ringChar F :=
    Or.inr (by rw [hrchar]; omega)
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
  have hA0_eval_ne : A.eval 0 ≠ 0 := by
    intro hA0
    have hev := congrArg (fun Z : F[X] ↦ Z.eval 0) hV_eq_C
    dsimp [V] at hev
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      hA0, mul_zero, zero_mul, Polynomial.eval_mul, Polynomial.eval_X, zero_mul,
      add_zero, Polynomial.eval_C] at hev
    exact hc_ne hev.symm
  have hA0_ne : A.coeff 0 ≠ 0 := by rwa [← eval_zero_eq_coeff_zero]
  -- Dual Wronskian on `U = X ^ f * A * Q - B ^ 3`
  set f1 : ℕ := f - 1
  have hf1_succ : f1 + 1 = f := by omega
  set W_dual : F[X] := Polynomial.C (3 : F) * B.derivative * U - B * U.derivative
  set S : F[X] :=
    Q * (Polynomial.C (3 : F) * A * X * B.derivative - B * X * A.derivative -
      Polynomial.C ((f1 + 1 : ℕ) : F) * A * B) - A * B * X * Q.derivative
  have hW_dual_factor : W_dual = X ^ f1 * S := by
    have hU_eq1 : U = X ^ (f1 + 1) * A * Q - B ^ 3 := by rw [hf1_succ]
    have hU_deriv :
        U.derivative =
          (Polynomial.C ((f1 + 1 : ℕ) : F) * X ^ f1 * A + X ^ (f1 + 1) * A.derivative) * Q +
            X ^ (f1 + 1) * A * Q.derivative -
            Polynomial.C (3 : F) * B ^ 2 * B.derivative := by
      rw [hU_eq1, Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_mul, Polynomial.derivative_X_pow (f1 + 1),
        Polynomial.derivative_pow B 3]
      simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
    dsimp [W_dual, S]
    rw [hU_deriv, hU_eq1, pow_succ X f1]
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
    · have hU_pos : 0 < U.natDegree := by omega
      have hU'_le : U.derivative.natDegree ≤ U.natDegree - 1 :=
        Polynomial.natDegree_derivative_le U
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
  have hA_dvd_kummer : A ∣ (X ^ e - Polynomial.C α) := by
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
    rw [hα0, map_zero, sub_zero] at hA_dvd_kummer
    exact not_dvd_X_pow_of_eval_zero_ne_zero (by rw [hAd]; omega) hA0_eval_ne e hA_dvd_kummer
  -- Frobenius-reversal cube symmetry
  obtain ⟨j, hj_mod⟩ := hfrob_inv
  obtain ⟨M, hM_eq⟩ := Nat.dvd_of_mod_eq_zero hj_mod
  set β : F := α ^ M
  have hβ_ne : β ≠ 0 := pow_ne_zero M hα_ne
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpj_pos : 0 < p ^ j := pow_pos hp_pos j
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
  set c₀ : F := (A.coeff 0) ^ (p ^ j)
  have hc₀_ne : c₀ ≠ 0 := pow_ne_zero (p ^ j) hA0_ne
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
  have hsym_coeff : ∀ d ≤ 3 * h,
      ((A ^ 3).coeff (3 * h - d)) ^ (p ^ j) * β ^ (3 * h - d) = c₀ ^ 3 * (A ^ 3).coeff d := by
    intro d hd_le
    have hc := congrArg (fun Z : F[X] ↦ Z.coeff d) hrev_cube
    rwa [revSum_coeff (3 * h) (ψ (A ^ 3)) hd_le, hψ_coeff, Polynomial.coeff_C_mul] at hc
  exact ⟨P, U, α, β, c, c₀, j, hA0_ne, hP_le, hU_monic, hU_deg, hA3_split, hc_ne, hW_eq,
    hα_ne, hA_dvd_kummer, hβ_ne, hc₀_ne, hsym_coeff⟩

/-! ## Part 3: Pure-`F[X]` Lemma U (`M-0964` / `M-0965`) -/

private lemma lemma_U_pure_FX {F : Type*} [Field F]
    {p : ℕ} [CharP F p]
    {A P U : F[X]} {h k e f : ℕ} {α : F}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hp_gt : 4 * h < p)
    (hAd : A.natDegree = h)
    (hP_le : P.natDegree ≤ h + 2 * k)
    (hUm : U.Monic) (hUd : U.natDegree = h - 2 * k)
    (hA3_split : A ^ 3 = P + X ^ e * U)
    (hα_ne : α ≠ 0) (hA_dvd_kummer : A ∣ (X ^ e - Polynomial.C α)) :
    U.coeff 0 ≠ 0 ∧
    IsCoprime A U ∧
    IsCoprime U (theta U) ∧
    (∃ c₁ : F, c₁ ≠ 0 ∧ A ∣ (Polynomial.C (3 : F) * U * theta A + Polynomial.C c₁)) := by
  set A_rev : F[X] := revSum h A
  set U_rev : F[X] := revSum (h - 2 * k) U
  have hA_rev_deg : A_rev.natDegree ≤ h := revSum_natDegree_le h A
  have hU_rev_deg : U_rev.natDegree ≤ h - 2 * k := revSum_natDegree_le (h - 2 * k) U
  have hrev_A3 : revSum (3 * h) (A ^ 3) = A_rev ^ 3 := by
    have hA2_deg : (A ^ 2).natDegree ≤ h + h := by
      rw [sq]
      exact le_trans Polynomial.natDegree_mul_le (by omega)
    calc revSum (3 * h) (A ^ 3)
        = revSum ((h + h) + h) (A ^ 2 * A) := by
            rw [show 3 * h = (h + h) + h by omega, pow_succ A 2]
      _ = revSum (h + h) (A ^ 2) * A_rev := revSum_mul hA2_deg (le_of_eq hAd)
      _ = (A_rev * A_rev) * A_rev := by
            rw [sq, revSum_mul (le_of_eq hAd) (le_of_eq hAd)]
      _ = A_rev ^ 3 := by ring
  have hrev_P : revSum (3 * h) P = X ^ f * revSum (h + 2 * k) P := by
    calc revSum (3 * h) P
        = revSum ((h + 2 * k) + f) (P * (Polynomial.C (1 : F) * X ^ 0)) := by
            rw [show 3 * h = (h + 2 * k) + f by omega]
            simp
      _ = revSum (h + 2 * k) P * revSum f (Polynomial.C (1 : F) * X ^ 0) :=
            revSum_mul hP_le (by simp)
      _ = X ^ f * revSum (h + 2 * k) P := by
            rw [revSum_C_mul_X_pow (1 : F) (Nat.zero_le f), Nat.sub_zero, map_one, one_mul,
              mul_comm]
  have hrev_XeU : revSum (3 * h) (X ^ e * U) = U_rev := by
    calc revSum (3 * h) (X ^ e * U)
        = revSum (e + (h - 2 * k)) ((Polynomial.C (1 : F) * X ^ e) * U) := by
            rw [show 3 * h = e + (h - 2 * k) by omega, map_one, one_mul]
      _ = revSum e (Polynomial.C (1 : F) * X ^ e) * U_rev :=
            revSum_mul (by simp) (le_of_eq hUd)
      _ = U_rev := by
            rw [revSum_C_mul_X_pow (1 : F) le_rfl, Nat.sub_self, pow_zero, map_one, one_mul, one_mul]
  set R₀ : F[X] := revSum (h + 2 * k) P
  have hArev3_eq : A_rev ^ 3 = U_rev + X ^ f * R₀ := by
    rw [← hrev_A3, hA3_split, revSum_add, hrev_P, hrev_XeU, add_comm]
  set f1 : ℕ := f - 1
  have hf1_succ : f1 + 1 = f := by omega
  set W_U : F[X] := Polynomial.C (3 : F) * U_rev * A_rev.derivative - A_rev * U_rev.derivative
  have hWU_factor :
      W_U = X ^ f1 * (Polynomial.C ((f1 + 1 : ℕ) : F) * A_rev * R₀ +
        X * (A_rev * R₀.derivative - Polynomial.C (3 : F) * A_rev.derivative * R₀)) := by
    have hUrev_eq : U_rev = A_rev ^ 3 - X ^ (f1 + 1) * R₀ := by
      rw [hf1_succ]
      linear_combination -hArev3_eq
    have hUrev_deriv :
        U_rev.derivative =
          Polynomial.C (3 : F) * A_rev ^ 2 * A_rev.derivative -
            (Polynomial.C ((f1 + 1 : ℕ) : F) * X ^ f1 * R₀ + X ^ (f1 + 1) * R₀.derivative) := by
      rw [hUrev_eq, Polynomial.derivative_sub, Polynomial.derivative_pow A_rev 3,
        Polynomial.derivative_mul, Polynomial.derivative_X_pow (f1 + 1)]
      simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
    dsimp [W_U]
    rw [hUrev_deriv, hUrev_eq, pow_succ X f1]
    ring
  have hWU_deg : W_U.natDegree ≤ f1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · by_cases hA'0 : A_rev.derivative = 0
      · rw [hA'0, mul_zero, Polynomial.natDegree_zero]; omega
      · have hA_pos : 0 < A_rev.natDegree := by
          by_contra ha0
          have haz : A_rev.natDegree = 0 := Nat.eq_zero_of_not_pos ha0
          rw [Polynomial.eq_C_of_natDegree_eq_zero haz, Polynomial.derivative_C] at hA'0
          exact hA'0 rfl
        have hA'_le : A_rev.derivative.natDegree ≤ A_rev.natDegree - 1 :=
          Polynomial.natDegree_derivative_le A_rev
        refine le_trans Polynomial.natDegree_mul_le ?_
        have h3U : (Polynomial.C (3 : F) * U_rev).natDegree ≤ h - 2 * k :=
          le_trans (Polynomial.natDegree_C_mul_le (3 : F) U_rev) hU_rev_deg
        omega
    · by_cases hU'0 : U_rev.derivative = 0
      · rw [hU'0, mul_zero, Polynomial.natDegree_zero]; omega
      · have hU_pos : 0 < U_rev.natDegree := by
          by_contra hu0
          have huz : U_rev.natDegree = 0 := Nat.eq_zero_of_not_pos hu0
          rw [Polynomial.eq_C_of_natDegree_eq_zero huz, Polynomial.derivative_C] at hU'0
          exact hU'0 rfl
        have hU'_le : U_rev.derivative.natDegree ≤ U_rev.natDegree - 1 :=
          Polynomial.natDegree_derivative_le U_rev
        refine le_trans Polynomial.natDegree_mul_le ?_
        omega
  set Q_U : F[X] := Polynomial.C ((f1 + 1 : ℕ) : F) * A_rev * R₀ +
      X * (A_rev * R₀.derivative - Polynomial.C (3 : F) * A_rev.derivative * R₀)
  have hQU_deg0 : Q_U.natDegree = 0 := by
    by_cases hQ0 : Q_U = 0
    · simp [hQ0]
    · have hXf1_ne : (X : F[X]) ^ f1 ≠ 0 := pow_ne_zero f1 Polynomial.X_ne_zero
      have hd : W_U.natDegree = f1 + Q_U.natDegree := by
        rw [hWU_factor, Polynomial.natDegree_mul hXf1_ne hQ0, Polynomial.natDegree_X_pow]
      omega
  set c₁ : F := Q_U.coeff 0
  have hWU_eq : W_U = Polynomial.C c₁ * X ^ f1 := by
    rw [hWU_factor, Polynomial.eq_C_of_natDegree_eq_zero hQU_deg0, mul_comm]
  have hX_WU :
      Polynomial.C (3 : F) * U_rev * theta A_rev - A_rev * theta U_rev =
        Polynomial.C c₁ * X ^ f := by
    calc Polynomial.C (3 : F) * U_rev * theta A_rev - A_rev * theta U_rev
        = X * W_U := by dsimp [W_U, theta]; ring
      _ = X * (Polynomial.C c₁ * X ^ f1) := by rw [hWU_eq]
      _ = Polynomial.C c₁ * (X ^ f1 * X) := by ring
      _ = Polynomial.C c₁ * X ^ (f1 + 1) := by rw [← pow_succ X f1]
      _ = Polynomial.C c₁ * X ^ f := by rw [hf1_succ]
  -- Apply `revSum f` (`f = (h - 2 * k) + h`) to obtain the exact Lemma U identity in `F[X]`
  have hLemmaU_id :
      Polynomial.C ((e : ℕ) : F) * A * U - Polynomial.C (3 : F) * U * theta A + A * theta U =
        Polynomial.C c₁ := by
    have hrev_both := congrArg (revSum f) hX_WU
    have hf_split1 : f = (h - 2 * k) + h := by omega
    have hf_split2 : f = h + (h - 2 * k) := by omega
    have htA_deg : (theta A_rev).natDegree ≤ h := le_trans (natDegree_theta_le A_rev) hA_rev_deg
    have htU_deg : (theta U_rev).natDegree ≤ h - 2 * k :=
      le_trans (natDegree_theta_le U_rev) hU_rev_deg
    have hterm1 :
        revSum f (Polynomial.C (3 : F) * U_rev * theta A_rev) =
          Polynomial.C (3 : F) * U * (Polynomial.C ((h : ℕ) : F) * A - theta A) := by
      rw [mul_assoc, revSum_C_mul]
      conv_lhs => rw [hf_split1]
      rw [revSum_mul hU_rev_deg htA_deg, revSum_revSum (le_of_eq hUd),
        revSum_theta_revSum (le_of_eq hAd), ← mul_assoc]
    have hterm2 :
        revSum f (A_rev * theta U_rev) =
          A * (Polynomial.C ((h - 2 * k : ℕ) : F) * U - theta U) := by
      conv_lhs => rw [hf_split2]
      rw [revSum_mul hA_rev_deg htU_deg, revSum_revSum (le_of_eq hAd),
        revSum_theta_revSum (le_of_eq hUd)]
    have hrhs : revSum f (Polynomial.C c₁ * X ^ f) = Polynomial.C c₁ := by
      rw [revSum_C_mul_X_pow c₁ le_rfl, Nat.sub_self, pow_zero, mul_one]
    rw [revSum_sub, hterm1, hterm2, hrhs] at hrev_both
    have he_cast :
        ((e : ℕ) : F) = 3 * ((h : ℕ) : F) - ((h - 2 * k : ℕ) : F) := by
      have hsub_le : h - 2 * k ≤ 3 * h := by omega
      have he_nat : e = 3 * h - (h - 2 * k) := by omega
      rw [he_nat, Nat.cast_sub hsub_le, Nat.cast_mul, Nat.cast_ofNat]
    rw [← hrev_both, he_cast, map_sub, map_mul, map_ofNat]
    ring
  -- Prove `IsCoprime A (theta A)` from `A ∣ X ^ e - C α` (`α ≠ 0`, `(e : F) ≠ 0`)
  have he_ne_F : ((e : ℕ) : F) ≠ 0 :=
    nat_cast_ne_zero_of_pos_lt (by omega : 0 < e) (by omega : e < p)
  have h3_ne_F : (3 : F) ≠ 0 := by
    have h3 : ((3 : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by decide : 0 < 3) (by omega : 3 < p)
    simpa using h3
  have hcop_A_tA : IsCoprime A (theta A) := by
    obtain ⟨Q_A, hQA⟩ := hA_dvd_kummer
    have htQA := congrArg theta hQA
    rw [theta_sub, theta_X_pow, theta_C, sub_zero, theta_mul] at htQA
    set eα : F := ((e : ℕ) : F) * α
    have heα_ne : eα ≠ 0 := mul_ne_zero he_ne_F hα_ne
    have hbez_raw :
        (theta Q_A - Polynomial.C ((e : ℕ) : F) * Q_A) * A + Q_A * theta A =
          Polynomial.C eα := by
      have hXe_eq : (X : F[X]) ^ e = A * Q_A + Polynomial.C α := eq_add_of_sub_eq hQA
      have heXe :
          Polynomial.C ((e : ℕ) : F) * (X : F[X]) ^ e =
            Polynomial.C ((e : ℕ) : F) * A * Q_A + Polynomial.C eα := by
        rw [hXe_eq, mul_add, ← mul_assoc, ← map_mul]
      linear_combination heXe - htQA
    refine ⟨Polynomial.C eα⁻¹ * (theta Q_A - Polynomial.C ((e : ℕ) : F) * Q_A),
      Polynomial.C eα⁻¹ * Q_A, ?_⟩
    calc Polynomial.C eα⁻¹ * (theta Q_A - Polynomial.C ((e : ℕ) : F) * Q_A) * A +
          Polynomial.C eα⁻¹ * Q_A * theta A
        = Polynomial.C eα⁻¹ *
            ((theta Q_A - Polynomial.C ((e : ℕ) : F) * Q_A) * A + Q_A * theta A) := by ring
      _ = Polynomial.C eα⁻¹ * Polynomial.C eα := by rw [hbez_raw]
      _ = Polynomial.C (eα⁻¹ * eα) := (map_mul Polynomial.C eα⁻¹ eα).symm
      _ = 1 := by rw [inv_mul_cancel₀ heα_ne, map_one]
  have hc₁_ne : c₁ ≠ 0 := by
    intro hc1_0
    rw [hc1_0, map_zero] at hLemmaU_id
    have hdvd_prod : A ∣ theta A * (Polynomial.C (3 : F) * U) := by
      refine ⟨Polynomial.C ((e : ℕ) : F) * U + theta U, ?_⟩
      linear_combination -hLemmaU_id
    have hdvd_3U : A ∣ Polynomial.C (3 : F) * U := hcop_A_tA.dvd_of_dvd_mul_left hdvd_prod
    obtain ⟨Z_U, hZU⟩ := hdvd_3U
    have hA_dvd_U : A ∣ U := by
      refine ⟨Polynomial.C (3 : F)⁻¹ * Z_U, ?_⟩
      calc U = Polynomial.C ((3 : F)⁻¹ * 3) * U := by rw [inv_mul_cancel₀ h3_ne_F, map_one, one_mul]
        _ = Polynomial.C (3 : F)⁻¹ * (Polynomial.C (3 : F) * U) := by rw [map_mul, mul_assoc]
        _ = Polynomial.C (3 : F)⁻¹ * (A * Z_U) := by rw [hZU]
        _ = A * (Polynomial.C (3 : F)⁻¹ * Z_U) := by ring
    have hdeg_le := Polynomial.natDegree_le_of_dvd hA_dvd_U hUm.ne_zero
    omega
  have hU0_ne : U.coeff 0 ≠ 0 := by
    intro hU0
    have htU0 : (theta U).coeff 0 = 0 := by rw [coeff_theta]; simp
    have h1 : (Polynomial.C ((e : ℕ) : F) * A * U).coeff 0 = 0 := by
      rw [← eval_zero_eq_coeff_zero]
      simp [eval_zero_eq_coeff_zero, hU0]
    have h2 : (Polynomial.C (3 : F) * U * theta A).coeff 0 = 0 := by
      rw [← eval_zero_eq_coeff_zero]
      simp [eval_zero_eq_coeff_zero, hU0]
    have h3 : (A * theta U).coeff 0 = 0 := by
      rw [← eval_zero_eq_coeff_zero, Polynomial.eval_mul, eval_zero_eq_coeff_zero (theta U),
        htU0, mul_zero]
    have h0eq := congrArg (fun Z : F[X] ↦ Z.coeff 0) hLemmaU_id
    rw [Polynomial.coeff_add, Polynomial.coeff_sub, h1, h2, h3, sub_zero, add_zero,
      Polynomial.coeff_C_zero] at h0eq
    exact hc₁_ne h0eq.symm
  have hcop_AU : IsCoprime A U := by
    refine ⟨Polynomial.C c₁⁻¹ * (Polynomial.C ((e : ℕ) : F) * U + theta U),
      Polynomial.C c₁⁻¹ * (-Polynomial.C (3 : F) * theta A), ?_⟩
    calc Polynomial.C c₁⁻¹ * (Polynomial.C ((e : ℕ) : F) * U + theta U) * A +
          Polynomial.C c₁⁻¹ * (-Polynomial.C (3 : F) * theta A) * U
        = Polynomial.C c₁⁻¹ *
            (Polynomial.C ((e : ℕ) : F) * A * U - Polynomial.C (3 : F) * U * theta A + A * theta U) := by
            ring
      _ = Polynomial.C c₁⁻¹ * Polynomial.C c₁ := by rw [hLemmaU_id]
      _ = Polynomial.C (c₁⁻¹ * c₁) := (map_mul Polynomial.C c₁⁻¹ c₁).symm
      _ = 1 := by rw [inv_mul_cancel₀ hc₁_ne, map_one]
  have hcop_UtU : IsCoprime U (theta U) := by
    refine ⟨Polynomial.C c₁⁻¹ * (Polynomial.C ((e : ℕ) : F) * A - Polynomial.C (3 : F) * theta A),
      Polynomial.C c₁⁻¹ * A, ?_⟩
    calc Polynomial.C c₁⁻¹ * (Polynomial.C ((e : ℕ) : F) * A - Polynomial.C (3 : F) * theta A) * U +
          Polynomial.C c₁⁻¹ * A * theta U
        = Polynomial.C c₁⁻¹ *
            (Polynomial.C ((e : ℕ) : F) * A * U - Polynomial.C (3 : F) * U * theta A + A * theta U) := by
            ring
      _ = Polynomial.C c₁⁻¹ * Polynomial.C c₁ := by rw [hLemmaU_id]
      _ = Polynomial.C (c₁⁻¹ * c₁) := (map_mul Polynomial.C c₁⁻¹ c₁).symm
      _ = 1 := by rw [inv_mul_cancel₀ hc₁_ne, map_one]
  have hmod_A : A ∣ (Polynomial.C (3 : F) * U * theta A + Polynomial.C c₁) := by
    refine ⟨Polynomial.C ((e : ℕ) : F) * U + theta U, ?_⟩
    linear_combination -hLemmaU_id
  exact ⟨hU0_ne, hcop_AU, hcop_UtU, ⟨c₁, hc₁_ne, hmod_A⟩⟩

/-! ## Part 4: Three-Term `θ`-Wronskian Identity (`w ≡ λ * U ^ 2 (mod A)`, `λ ≠ 0`) -/

private noncomputable def det3 {R : Type*} [CommRing R]
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : R) : R :=
  a00 * (a11 * a22 - a12 * a21) -
  a01 * (a10 * a22 - a12 * a20) +
  a02 * (a10 * a21 - a11 * a20)

private lemma three_block_theta_wronskian_dvd {F : Type*} [Field F] [DecidableEq F]
    {p : ℕ} [CharP F p]
    {A L₀ M₁ U : F[X]} {h k e f : ℕ} {c₁ : F}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h) (hh_le_4k : h ≤ 4 * k)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hp_gt : 4 * h < p)
    (hAm : A.Monic) (hAd : A.natDegree = h)
    (hL₀_le : L₀.natDegree ≤ h - 2 * k) (hL₀_0 : L₀.coeff 0 ≠ 0)
    (hM₁_ne : M₁ ≠ 0) (hM₁_le : M₁.natDegree ≤ 4 * k - h)
    (hUd : U.natDegree = h - 2 * k) (hU0 : U.coeff 0 ≠ 0)
    (hc₁_ne : c₁ ≠ 0)
    (hmod_U_tA : A ∣ (Polynomial.C (3 : F) * U * theta A + Polynomial.C c₁))
    (hA3_3block : A ^ 3 = L₀ + X ^ f * M₁ + X ^ e * U) :
    let w : F[X] :=
      Polynomial.C ((4 * k : ℕ) : F) * M₁ * U + M₁ * theta U - U * theta M₁
    w.natDegree ≤ 2 * k ∧
    ∃ lam : F, lam ≠ 0 ∧ A ∣ (w - Polynomial.C lam * U ^ 2) := by
  intro w
  have hw_deg : w.natDegree ≤ 2 * k := by
    dsimp [w]
    have htU : (theta U).natDegree ≤ h - 2 * k := le_trans (natDegree_theta_le U) (le_of_eq hUd)
    have htM : (theta M₁).natDegree ≤ 4 * k - h := le_trans (natDegree_theta_le M₁) hM₁_le
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 : (Polynomial.C ((4 * k : ℕ) : F) * M₁).natDegree ≤ 4 * k - h :=
          le_trans (Polynomial.natDegree_C_mul_le _ _) hM₁_le
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      omega
  -- Construct `W₃` and `D₃`
  let P₁ : F[X] := L₀
  let P₂ : F[X] := X ^ f * M₁
  let P₃ : F[X] := X ^ e * U
  let c2_0 : F[X] := M₁
  let c2_1 : F[X] := Polynomial.C ((f : ℕ) : F) * M₁ + theta M₁
  let c2_2 : F[X] :=
    Polynomial.C ((f : ℕ) : F) ^ 2 * M₁ +
      Polynomial.C (2 * ((f : ℕ) : F)) * theta M₁ + theta (theta M₁)
  let c3_0 : F[X] := U
  let c3_1 : F[X] := Polynomial.C ((e : ℕ) : F) * U + theta U
  let c3_2 : F[X] :=
    Polynomial.C ((e : ℕ) : F) ^ 2 * U +
      Polynomial.C (2 * ((e : ℕ) : F)) * theta U + theta (theta U)
  have htP₂ : theta P₂ = X ^ f * c2_1 := by
    dsimp [P₂, c2_1]
    exact theta_X_pow_mul f M₁
  have httP₂ : theta (theta P₂) = X ^ f * c2_2 := by
    rw [htP₂, theta_X_pow_mul]
    dsimp [c2_1, c2_2]
    rw [theta_add, theta_C_mul, map_mul, map_ofNat]
    ring
  have htP₃ : theta P₃ = X ^ e * c3_1 := by
    dsimp [P₃, c3_1]
    exact theta_X_pow_mul e U
  have httP₃ : theta (theta P₃) = X ^ e * c3_2 := by
    rw [htP₃, theta_X_pow_mul]
    dsimp [c3_1, c3_2]
    rw [theta_add, theta_C_mul, map_mul, map_ofNat]
    ring
  set W₃ : F[X] :=
    det3 P₁ P₂ P₃ (theta P₁) (theta P₂) (theta P₃)
      (theta (theta P₁)) (theta (theta P₂)) (theta (theta P₃))
  set D₃ : F[X] :=
    det3 L₀ c2_0 c3_0 (theta L₀) c2_1 c3_1 (theta (theta L₀)) c2_2 c3_2
  have hW₃_eq_Xef_D₃ : W₃ = X ^ (e + f) * D₃ := by
    dsimp [W₃, D₃, det3]
    rw [httP₂, httP₃, htP₂, htP₃]
    dsimp [P₁, P₂, P₃, c2_0, c3_0]
    rw [pow_add]
    ring
  -- Column-sum identity `P₁ = A ^ 3 - P₂ - P₃`
  have hP₁_sub : P₁ = A ^ 3 - P₂ - P₃ := by
    dsimp [P₁, P₂, P₃]
    linear_combination -hA3_3block
  have htA3 : theta (A ^ 3) = Polynomial.C (3 : F) * A ^ 2 * theta A := by
    calc theta (A ^ 3) = theta (A ^ 2 * A) := by rw [pow_succ A 2]
      _ = theta (A * A) * A + A ^ 2 * theta A := by rw [sq, theta_mul, ← sq]
      _ = (theta A * A + A * theta A) * A + A ^ 2 * theta A := by rw [theta_mul]
      _ = Polynomial.C (3 : F) * A ^ 2 * theta A := by simp only [map_ofNat]; ring
  have httA3 :
      theta (theta (A ^ 3)) =
        Polynomial.C (6 : F) * A * (theta A) ^ 2 +
          Polynomial.C (3 : F) * A ^ 2 * theta (theta A) := by
    rw [htA3, mul_assoc, theta_C_mul, theta_mul, sq A, theta_mul]
    simp only [map_ofNat]
    ring
  have htP₁_sub : theta P₁ = Polynomial.C (3 : F) * A ^ 2 * theta A - theta P₂ - theta P₃ := by
    rw [hP₁_sub, theta_sub, theta_sub, htA3]
  have httP₁_sub :
      theta (theta P₁) =
        Polynomial.C (6 : F) * A * (theta A) ^ 2 +
          Polynomial.C (3 : F) * A ^ 2 * theta (theta A) -
          theta (theta P₂) - theta (theta P₃) := by
    rw [htP₁_sub, theta_sub, theta_sub, ← htA3, httA3]
  let R_D : F[X] :=
    A * (c2_1 * c3_2 - c3_1 * c2_2) -
      Polynomial.C (3 : F) * theta A * (c2_0 * c3_2 - c3_0 * c2_2) +
      Polynomial.C (3 : F) * theta (theta A) * (c2_0 * c3_1 - c3_0 * c2_1)
  have hw_ef :
      w = (Polynomial.C ((e : ℕ) : F) - Polynomial.C ((f : ℕ) : F)) * c2_0 * c3_0 +
            c2_0 * theta U - c3_0 * theta M₁ := by
    have hef : ((4 * k : ℕ) : F) = ((e : ℕ) : F) - ((f : ℕ) : F) := by
      have hf_le_e : f ≤ e := by omega
      have h4k_eq : 4 * k = e - f := by omega
      rw [h4k_eq, Nat.cast_sub hf_le_e]
    dsimp [w, c2_0, c3_0]
    rw [hef, map_sub]
  have hW₃_eq_A :
      W₃ = X ^ (e + f) * (A * (Polynomial.C (6 : F) * (theta A) ^ 2 * w + A * R_D)) := by
    dsimp [W₃]
    rw [httP₁_sub, htP₁_sub, hP₁_sub, httP₂, httP₃, htP₂, htP₃, hw_ef]
    dsimp [P₂, P₃, R_D, c2_0, c2_1, c3_0, c3_1, det3]
    rw [pow_add]
    simp only [map_ofNat]
    ring
  have hD₃_eq_A : D₃ = A * (Polynomial.C (6 : F) * (theta A) ^ 2 * w + A * R_D) := by
    apply mul_left_cancel₀ (pow_ne_zero (e + f) Polynomial.X_ne_zero)
    rw [← hW₃_eq_Xef_D₃, hW₃_eq_A]
  -- Bound `D₃.natDegree ≤ h`
  have hc2_0_deg : c2_0.natDegree ≤ 4 * k - h := hM₁_le
  have hc2_1_deg : c2_1.natDegree ≤ 4 * k - h := by
    dsimp [c2_1]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hM₁_le
    · exact le_trans (natDegree_theta_le M₁) hM₁_le
  have hc2_2_deg : c2_2.natDegree ≤ 4 * k - h := by
    dsimp [c2_2]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · rw [← map_pow]
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) hM₁_le
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _)
          (le_trans (natDegree_theta_le M₁) hM₁_le)
    · exact le_trans (natDegree_theta_le _) (le_trans (natDegree_theta_le M₁) hM₁_le)
  have hc3_0_deg : c3_0.natDegree ≤ h - 2 * k := le_of_eq hUd
  have hc3_1_deg : c3_1.natDegree ≤ h - 2 * k := by
    dsimp [c3_1]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hUd)
    · exact le_trans (natDegree_theta_le U) (le_of_eq hUd)
  have hc3_2_deg : c3_2.natDegree ≤ h - 2 * k := by
    dsimp [c3_2]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · rw [← map_pow]
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hUd)
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _)
          (le_trans (natDegree_theta_le U) (le_of_eq hUd))
    · exact le_trans (natDegree_theta_le _) (le_trans (natDegree_theta_le U) (le_of_eq hUd))
  have htL₀_deg : (theta L₀).natDegree ≤ h - 2 * k := le_trans (natDegree_theta_le L₀) hL₀_le
  have httL₀_deg : (theta (theta L₀)).natDegree ≤ h - 2 * k :=
    le_trans (natDegree_theta_le _) htL₀_deg
  have hD₃_deg : D₃.natDegree ≤ h := by
    dsimp [D₃, det3]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have hsub : (c2_1 * c3_2 - c3_1 * c2_2).natDegree ≤ 2 * k := by
          refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
          · exact le_trans Polynomial.natDegree_mul_le (by omega)
          · exact le_trans Polynomial.natDegree_mul_le (by omega)
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have hsub : (theta L₀ * c3_2 - c3_1 * theta (theta L₀)).natDegree ≤ 2 * h - 4 * k := by
          refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
          · exact le_trans Polynomial.natDegree_mul_le (by omega)
          · exact le_trans Polynomial.natDegree_mul_le (by omega)
        omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have hsub : (theta L₀ * c2_2 - c2_1 * theta (theta L₀)).natDegree ≤ 2 * k := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
        · exact le_trans Polynomial.natDegree_mul_le (by omega)
        · exact le_trans Polynomial.natDegree_mul_le (by omega)
      omega
  -- Prove `D₃ ≠ 0` by evaluating `.coeff m₀` at the minimal nonzero index `m₀` of `M₁`
  have hex_m₀ : ∃ m : ℕ, M₁.coeff m ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hM₁_ne (Polynomial.ext (fun m ↦ by rw [hall m, Polynomial.coeff_zero]))
  set m₀ : ℕ := Nat.find hex_m₀
  have hm₀_ne : M₁.coeff m₀ ≠ 0 := Nat.find_spec hex_m₀
  have hm₀_min : ∀ i < m₀, M₁.coeff i = 0 :=
    fun i hi ↦ not_not.mp (Nat.find_min hex_m₀ hi)
  have hm₀_le : m₀ ≤ 4 * k - h := by
    by_contra hgt
    exact hm₀_ne (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hc2_1_coeff : ∀ i : ℕ, c2_1.coeff i = ((f + i : ℕ) : F) * M₁.coeff i := by
    intro i
    dsimp [c2_1]
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_theta, Nat.cast_add, add_mul]
  have hc2_2_coeff : ∀ i : ℕ, c2_2.coeff i = ((f + i : ℕ) : F) ^ 2 * M₁.coeff i := by
    intro i
    dsimp [c2_2]
    rw [← map_pow, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, coeff_theta, coeff_theta, coeff_theta, Nat.cast_add]
    ring
  have hc2_0_van : ∀ i < m₀, c2_0.coeff i = 0 := hm₀_min
  have hc2_1_van : ∀ i < m₀, c2_1.coeff i = 0 := fun i hi ↦ by
    rw [hc2_1_coeff, hm₀_min i hi, mul_zero]
  have hc2_2_van : ∀ i < m₀, c2_2.coeff i = 0 := fun i hi ↦ by
    rw [hc2_2_coeff, hm₀_min i hi, mul_zero]
  have hD₃_laplace :
      D₃ = c2_0 * (c3_1 * theta (theta L₀) - c3_2 * theta L₀) +
           c2_1 * (c3_2 * L₀ - c3_0 * theta (theta L₀)) +
           c2_2 * (c3_0 * theta L₀ - c3_1 * L₀) := by
    dsimp [D₃, det3]
    ring
  have hD₃_m₀_ne : D₃.coeff m₀ ≠ 0 := by
    have htL₀_0 : (theta L₀).coeff 0 = 0 := by rw [coeff_theta]; simp
    have httL₀_0 : (theta (theta L₀)).coeff 0 = 0 := by rw [coeff_theta]; simp
    have hc3_1_0 : c3_1.coeff 0 = ((e : ℕ) : F) * U.coeff 0 := by
      dsimp [c3_1]
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_theta]
      simp
    have hc3_2_0 : c3_2.coeff 0 = ((e : ℕ) : F) ^ 2 * U.coeff 0 := by
      dsimp [c3_2]
      rw [← map_pow, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul, coeff_theta, coeff_theta]
      simp
    have hf1_0 : (c3_1 * theta (theta L₀) - c3_2 * theta L₀).coeff 0 = 0 := by
      rw [← eval_zero_eq_coeff_zero]
      simp [eval_zero_eq_coeff_zero, htL₀_0, httL₀_0]
    have hf2_0 : (c3_2 * L₀ - c3_0 * theta (theta L₀)).coeff 0 =
        ((e : ℕ) : F) ^ 2 * U.coeff 0 * L₀.coeff 0 := by
      rw [← eval_zero_eq_coeff_zero]
      simp [eval_zero_eq_coeff_zero, httL₀_0, hc3_2_0]
    have hf3_0 : (c3_0 * theta L₀ - c3_1 * L₀).coeff 0 =
        -(((e : ℕ) : F) * U.coeff 0 * L₀.coeff 0) := by
      rw [← eval_zero_eq_coeff_zero]
      simp [eval_zero_eq_coeff_zero, htL₀_0, hc3_1_0]
    have hcm :
        D₃.coeff m₀ =
          L₀.coeff 0 * M₁.coeff m₀ * U.coeff 0 * ((e : ℕ) : F) *
            ((f + m₀ : ℕ) : F) * (((e - (f + m₀) : ℕ) : F)) := by
      rw [hD₃_laplace, Polynomial.coeff_add, Polynomial.coeff_add,
        coeff_mul_of_vanish_below hc2_0_van,
        coeff_mul_of_vanish_below hc2_1_van,
        coeff_mul_of_vanish_below hc2_2_van,
        hf1_0, hf2_0, hf3_0, hc2_1_coeff, hc2_2_coeff,
        Nat.cast_sub (by omega : f + m₀ ≤ e)]
      ring
    rw [hcm]
    have he_ne : ((e : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by omega : 0 < e) (by omega : e < p)
    have hfm_ne : ((f + m₀ : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by omega : 0 < f + m₀) (by omega : f + m₀ < p)
    have hdiff_ne : ((e - (f + m₀) : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by omega : 0 < e - (f + m₀)) (by omega : e - (f + m₀) < p)
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hL₀_0 hm₀_ne) hU0) he_ne) hfm_ne)
      hdiff_ne
  have hD₃_ne : D₃ ≠ 0 := fun h0 ↦ hD₃_m₀_ne (by simp [h0])
  set Q_D : F[X] := Polynomial.C (6 : F) * (theta A) ^ 2 * w + A * R_D
  have hQD_ne : Q_D ≠ 0 := fun h0 ↦ hD₃_ne (by rw [hD₃_eq_A, h0, mul_zero])
  have hQD_deg0 : Q_D.natDegree = 0 := by
    have hd : D₃.natDegree = h + Q_D.natDegree := by
      rw [hD₃_eq_A, Polynomial.natDegree_mul hAm.ne_zero hQD_ne, hAd]
    omega
  set κ : F := Q_D.coeff 0
  have hQD_eq_C : Q_D = Polynomial.C κ := Polynomial.eq_C_of_natDegree_eq_zero hQD_deg0
  have hκ_ne : κ ≠ 0 := fun h0 ↦ hQD_ne (by rw [hQD_eq_C, h0, map_zero])
  -- Eliminate `(theta A) ^ 2` modulo `A` via `A ∣ (C 3 * U * theta A + C c₁)`
  obtain ⟨Z_u, hZu⟩ := hmod_U_tA
  have hA_dvd_comb :
      A ∣ (Polynomial.C (2 * c₁ ^ 2) * w - Polynomial.C (3 * κ) * U ^ 2) := by
    refine ⟨-Polynomial.C (3 : F) * U ^ 2 * R_D -
      Polynomial.C (2 : F) * w * Z_u *
        (Polynomial.C (3 : F) * U * theta A - Polynomial.C c₁), ?_⟩
    have h1 : Polynomial.C (6 : F) * (theta A) ^ 2 * w + A * R_D = Polynomial.C κ := hQD_eq_C
    simp only [map_mul, map_pow, map_ofNat] at h1 hZu ⊢
    linear_combination 3 * U ^ 2 * h1 -
      2 * w * (3 * U * theta A - Polynomial.C c₁) * hZu
  have h2_ne : (2 : F) ≠ 0 := by
    have h2 : ((2 : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by decide : 0 < 2) (by omega : 2 < p)
    simpa using h2
  have h3_ne : (3 : F) ≠ 0 := by
    have h3 : ((3 : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by decide : 0 < 3) (by omega : 3 < p)
    simpa using h3
  have h2c1_ne : 2 * c₁ ^ 2 ≠ 0 := mul_ne_zero h2_ne (pow_ne_zero 2 hc₁_ne)
  set lam : F := (3 * κ) * (2 * c₁ ^ 2)⁻¹
  have hlam_ne : lam ≠ 0 := mul_ne_zero (mul_ne_zero h3_ne hκ_ne) (inv_ne_zero h2c1_ne)
  obtain ⟨Z_c, hZc⟩ := hA_dvd_comb
  refine ⟨hw_deg, lam, hlam_ne, Polynomial.C (2 * c₁ ^ 2)⁻¹ * Z_c, ?_⟩
  have hscale :
      Polynomial.C (2 * c₁ ^ 2)⁻¹ *
          (Polynomial.C (2 * c₁ ^ 2) * w - Polynomial.C (3 * κ) * U ^ 2) =
        w - Polynomial.C lam * U ^ 2 := by
    dsimp [lam]
    calc Polynomial.C (2 * c₁ ^ 2)⁻¹ *
            (Polynomial.C (2 * c₁ ^ 2) * w - Polynomial.C (3 * κ) * U ^ 2)
        = (Polynomial.C (2 * c₁ ^ 2)⁻¹ * Polynomial.C (2 * c₁ ^ 2)) * w -
            (Polynomial.C (2 * c₁ ^ 2)⁻¹ * Polynomial.C (3 * κ)) * U ^ 2 := by ring
      _ = Polynomial.C ((2 * c₁ ^ 2)⁻¹ * (2 * c₁ ^ 2)) * w -
            Polynomial.C ((2 * c₁ ^ 2)⁻¹ * (3 * κ)) * U ^ 2 := by rw [← map_mul, ← map_mul]
      _ = w - Polynomial.C ((3 * κ) * (2 * c₁ ^ 2)⁻¹) * U ^ 2 := by
            rw [inv_mul_cancel₀ h2c1_ne, map_one, one_mul, mul_comm (2 * c₁ ^ 2)⁻¹ (3 * κ)]
  calc w - Polynomial.C lam * U ^ 2
      = Polynomial.C (2 * c₁ ^ 2)⁻¹ *
          (Polynomial.C (2 * c₁ ^ 2) * w - Polynomial.C (3 * κ) * U ^ 2) := hscale.symm
    _ = Polynomial.C (2 * c₁ ^ 2)⁻¹ * (A * Z_c) := by rw [hZc]
    _ = A * (Polynomial.C (2 * c₁ ^ 2)⁻¹ * Z_c) := by ring

/-! ## Part 5: Closing Branch B (`h = 4 * k`) and Branch C (`2 * k + 1 ≤ h ≤ 3 * k`) -/

private lemma branch_h_eq_4k_false {F : Type*} [Field F]
    {p : ℕ} [CharP F p]
    {A P M₁ U : F[X]} {k : ℕ} {α lam : F}
    (hk_pos : 1 ≤ k) (hp_gt : 16 * k < p)
    (hAm : A.Monic) (hAd : A.natDegree = 4 * k) (hA0 : A.coeff 0 ≠ 0)
    (hP_le : P.natDegree ≤ 6 * k)
    (hM₁_ne : M₁ ≠ 0) (hM₁_deg0 : M₁.natDegree = 0)
    (hUm : U.Monic) (hUd : U.natDegree = 2 * k)
    (hA3_split : A ^ 3 = P + X ^ (10 * k) * U)
    (hA_dvd_kummer : A ∣ (X ^ (10 * k) - Polynomial.C α))
    (hlam_ne : lam ≠ 0)
    (hA_dvd_w :
      A ∣ (Polynomial.C ((4 * k : ℕ) : F) * M₁ * U + M₁ * theta U - U * theta M₁ -
            Polynomial.C lam * U ^ 2)) : False := by
  set μ : F := M₁.coeff 0
  have hM₁_eq : M₁ = Polynomial.C μ := Polynomial.eq_C_of_natDegree_eq_zero hM₁_deg0
  have hμ_ne : μ ≠ 0 := fun h0 ↦ hM₁_ne (by rw [hM₁_eq, h0, map_zero])
  set L_U : F[X] := Polynomial.C ((4 * k : ℕ) : F) * U + theta U
  have hLU_deg : L_U.natDegree ≤ 2 * k := by
    dsimp [L_U]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hUd)
    · exact le_trans (natDegree_theta_le U) (le_of_eq hUd)
  have hw_simp :
      Polynomial.C ((4 * k : ℕ) : F) * M₁ * U + M₁ * theta U - U * theta M₁ =
        Polynomial.C μ * L_U := by
    rw [hM₁_eq, theta_C, mul_zero, sub_zero]
    dsimp [L_U]
    ring
  set Z_B : F[X] := Polynomial.C lam * U ^ 2 - Polynomial.C μ * L_U
  have hA_dvd_ZB : A ∣ Z_B := by
    obtain ⟨Q_z, hQz⟩ := hA_dvd_w
    refine ⟨-Q_z, ?_⟩
    rw [hw_simp] at hQz
    dsimp [Z_B]
    linear_combination -hQz
  have hU2_monic : (U ^ 2).Monic := hUm.pow 2
  have hU2_deg : (U ^ 2).natDegree = 4 * k := by
    rw [Polynomial.natDegree_pow U 2, hUd]
    omega
  have hμLU_deg : (Polynomial.C μ * L_U).natDegree ≤ 2 * k :=
    le_trans (Polynomial.natDegree_C_mul_le _ _) hLU_deg
  have hZB_deg : Z_B.natDegree ≤ 4 * k := by
    dsimp [Z_B]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ (by omega))
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hU2_deg)
  have hZB_coeff_4k : Z_B.coeff (4 * k) = lam := by
    have hU2_lc : (U ^ 2).coeff (4 * k) = 1 := by
      rw [← hU2_deg]
      exact hU2_monic.leadingCoeff
    dsimp [Z_B]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hU2_lc, mul_one,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (Polynomial.C μ * L_U).natDegree < 4 * k),
      sub_zero]
  have hZB_ne : Z_B ≠ 0 := fun h0 ↦ hlam_ne (by rw [← hZB_coeff_4k, h0, Polynomial.coeff_zero])
  obtain ⟨Q_B, hQB⟩ := hA_dvd_ZB
  have hQB_ne : Q_B ≠ 0 := fun h0 ↦ hZB_ne (by rw [hQB, h0, mul_zero])
  have hQB_deg0 : Q_B.natDegree = 0 := by
    have hd : Z_B.natDegree = 4 * k + Q_B.natDegree := by
      rw [hQB, Polynomial.natDegree_mul hAm.ne_zero hQB_ne, hAd]
    omega
  have hQB_eq_C : Q_B = Polynomial.C (Q_B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQB_deg0
  have hQB_c0 : Q_B.coeff 0 = lam := by
    have hA_lc : A.coeff (4 * k) = 1 := by
      rw [← hAd]
      exact hAm.leadingCoeff
    have hc4 := congrArg (fun Z : F[X] ↦ Z.coeff (4 * k)) hQB
    rw [hZB_coeff_4k, hQB_eq_C, mul_comm A, Polynomial.coeff_C_mul, hA_lc, mul_one] at hc4
    exact hc4.symm
  set ν : F := lam⁻¹ * μ
  set D_B : F[X] := Polynomial.C ν * L_U
  have hDB_deg : D_B.natDegree ≤ 2 * k :=
    le_trans (Polynomial.natDegree_C_mul_le _ _) hLU_deg
  have hA_eq_U2 : A = U ^ 2 - D_B := by
    have hZB_eq : Z_B = Polynomial.C lam * A := by rw [hQB, hQB_eq_C, hQB_c0, mul_comm]
    have hscale := congrArg (fun Z : F[X] ↦ Polynomial.C lam⁻¹ * Z) hZB_eq
    dsimp [Z_B] at hscale
    have hlhs :
        Polynomial.C lam⁻¹ * (Polynomial.C lam * U ^ 2 - Polynomial.C μ * L_U) = U ^ 2 - D_B := by
      dsimp [D_B, ν]
      calc Polynomial.C lam⁻¹ * (Polynomial.C lam * U ^ 2 - Polynomial.C μ * L_U)
          = (Polynomial.C lam⁻¹ * Polynomial.C lam) * U ^ 2 -
              (Polynomial.C lam⁻¹ * Polynomial.C μ) * L_U := by ring
        _ = Polynomial.C (lam⁻¹ * lam) * U ^ 2 - Polynomial.C (lam⁻¹ * μ) * L_U := by
              rw [← map_mul, ← map_mul]
        _ = U ^ 2 - Polynomial.C (lam⁻¹ * μ) * L_U := by
              rw [inv_mul_cancel₀ hlam_ne, map_one, one_mul]
    have hrhs : Polynomial.C lam⁻¹ * (Polynomial.C lam * A) = A := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hlam_ne, map_one, one_mul]
    rw [hlhs, hrhs] at hscale
    exact hscale.symm
  -- Show `(U ^ 6 - X ^ (10 * k) * U).natDegree ≤ 10 * k`
  have hU6_sub_A3_deg : (U ^ 6 - A ^ 3).natDegree ≤ 10 * k := by
    have hexp :
        U ^ 6 - A ^ 3 =
          Polynomial.C (3 : F) * U ^ 4 * D_B -
            Polynomial.C (3 : F) * U ^ 2 * D_B ^ 2 + D_B ^ 3 := by
      rw [hA_eq_U2]
      simp only [map_ofNat]
      ring
    rw [hexp]
    have hU4_deg : (U ^ 4).natDegree ≤ 8 * k := by
      rw [Polynomial.natDegree_pow U 4, hUd]; omega
    have hDB2_deg : (D_B ^ 2).natDegree ≤ 4 * k := by
      rw [sq]; exact le_trans Polynomial.natDegree_mul_le (by omega)
    have hDB3_deg : (D_B ^ 3).natDegree ≤ 6 * k := by
      rw [pow_succ D_B 2]; exact le_trans Polynomial.natDegree_mul_le (by omega)
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ (by omega))
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have h3U4 : (Polynomial.C (3 : F) * U ^ 4).natDegree ≤ 8 * k :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) hU4_deg
      omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have h3U2 : (Polynomial.C (3 : F) * U ^ 2).natDegree ≤ 4 * k :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hU2_deg)
      omega
  have hU6_top_deg : (U ^ 6 - X ^ (10 * k) * U).natDegree ≤ 10 * k := by
    have hrew : U ^ 6 - X ^ (10 * k) * U = (U ^ 6 - A ^ 3) + P := by
      linear_combination hA3_split
    rw [hrew]
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hU6_sub_A3_deg (by omega))
  -- Deduce `U = X ^ (2 * k) + C u₀`
  set U₀ : F[X] := U - X ^ (2 * k)
  have hU_eq_U0 : U = X ^ (2 * k) + U₀ := by dsimp [U₀]; ring
  have hU0_lt_2k : U₀.natDegree < 2 * k := by
    have hU_lc : U.coeff (2 * k) = 1 := by
      rw [← hUd]
      exact hUm.leadingCoeff
    have hle : U₀.natDegree ≤ 2 * k - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro d hd
      dsimp [U₀]
      rw [Polynomial.coeff_sub]
      rcases eq_or_lt_of_le (by omega : 2 * k ≤ d) with rfl | hgt
      · rw [hU_lc, coeff_X_pow_self, sub_self]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : U.natDegree < d),
          coeff_X_pow_of_ne (by omega : d ≠ 2 * k), sub_zero]
    omega
  have h5_ne : (5 : F) ≠ 0 := by
    have h5 : ((5 : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by decide : 0 < 5) (by omega : 5 < p)
    simpa using h5
  have h3_ne : (3 : F) ≠ 0 := by
    have h3 : ((3 : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by decide : 0 < 3) (by omega : 3 < p)
    simpa using h3
  have hU0_deg0 : U₀.natDegree = 0 := by
    by_contra hm_ne0
    have hU0_ne : U₀ ≠ 0 := fun h0 ↦ by simp [h0] at hm_ne0
    have hm_pos : 1 ≤ U₀.natDegree := by omega
    set m : ℕ := U₀.natDegree
    set E_hi : F[X] :=
      Polynomial.C (15 : F) * X ^ (8 * k) * U₀ ^ 2 +
      Polynomial.C (20 : F) * X ^ (6 * k) * U₀ ^ 3 +
      Polynomial.C (15 : F) * X ^ (4 * k) * U₀ ^ 4 +
      Polynomial.C (6 : F) * X ^ (2 * k) * U₀ ^ 5 +
      U₀ ^ 6
    have hU6_binom :
        U ^ 6 - X ^ (10 * k) * U = Polynomial.C (5 : F) * X ^ (10 * k) * U₀ + E_hi := by
      rw [hU_eq_U0]
      dsimp [E_hi]
      have hp12 : ((X : F[X]) ^ (2 * k)) ^ 6 = X ^ (10 * k) * X ^ (2 * k) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      have hp10 : ((X : F[X]) ^ (2 * k)) ^ 5 = X ^ (10 * k) := by
        rw [← pow_mul]; congr 1; omega
      have hp8 : ((X : F[X]) ^ (2 * k)) ^ 4 = X ^ (8 * k) := by
        rw [← pow_mul]; congr 1; omega
      have hp6 : ((X : F[X]) ^ (2 * k)) ^ 3 = X ^ (6 * k) := by
        rw [← pow_mul]; congr 1; omega
      have hp4 : ((X : F[X]) ^ (2 * k)) ^ 2 = X ^ (4 * k) := by
        rw [← pow_mul]; congr 1; omega
      simp only [map_ofNat]
      linear_combination hp12 + 6 * U₀ * hp10 + 15 * U₀ ^ 2 * hp8 +
        20 * U₀ ^ 3 * hp6 + 15 * U₀ ^ 4 * hp4
    have hpow_le : ∀ r_p : ℕ, (U₀ ^ r_p).natDegree ≤ r_p * m := by
      intro r_p
      induction r_p with
      | zero => simp
      | succ r_p ih =>
        rw [pow_succ, Nat.succ_mul]
        exact le_trans Polynomial.natDegree_mul_le (Nat.add_le_add_right ih m)
    have hterm_lt : ∀ (c_f : F) (s r_p : ℕ), s + r_p * m < 10 * k + m →
        (Polynomial.C c_f * X ^ s * U₀ ^ r_p).natDegree < 10 * k + m := by
      intro c_f s r_p hlt
      refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
      have h1 : (Polynomial.C c_f * X ^ s).natDegree ≤ s :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) (Polynomial.natDegree_X_pow_le s)
      have h2 := hpow_le r_p
      omega
    have hE_hi_lt : E_hi.natDegree < 10 * k + m := by
      dsimp [E_hi]
      refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
      · refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
        · refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
          · refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
            · exact hterm_lt 15 (8 * k) 2 (by omega)
            · exact hterm_lt 20 (6 * k) 3 (by omega)
          · exact hterm_lt 15 (4 * k) 4 (by omega)
        · exact hterm_lt 6 (2 * k) 5 (by omega)
      · exact lt_of_le_of_lt (hpow_le 6) (by omega)
    have hcoeff_top :
        (U ^ 6 - X ^ (10 * k) * U).coeff (10 * k + m) = 5 * U₀.leadingCoeff := by
      rw [hU6_binom, Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt hE_hi_lt,
        add_zero, mul_assoc, Polynomial.coeff_C_mul, Nat.add_comm (10 * k) m,
        Polynomial.coeff_X_pow_mul]
      rfl
    have h5lc_ne : (5 : F) * U₀.leadingCoeff ≠ 0 :=
      mul_ne_zero h5_ne (Polynomial.leadingCoeff_ne_zero.mpr hU0_ne)
    have hzero_top : (U ^ 6 - X ^ (10 * k) * U).coeff (10 * k + m) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact h5lc_ne (hcoeff_top.symm.trans hzero_top)
  set u₀ : F := U₀.coeff 0
  have hU_binom : U = X ^ (2 * k) + Polynomial.C u₀ := by
    rw [hU_eq_U0, Polynomial.eq_C_of_natDegree_eq_zero hU0_deg0]
  have htU_binom : theta U = Polynomial.C ((2 * k : ℕ) : F) * X ^ (2 * k) := by
    rw [hU_binom, theta_add, theta_X_pow, theta_C, add_zero]
  set a_B : F := 2 * u₀ - ν * (((4 * k : ℕ) : F) + ((2 * k : ℕ) : F))
  set b_B : F := u₀ ^ 2 - ν * ((4 * k : ℕ) : F) * u₀
  have hA_biquad : A = X ^ (4 * k) + Polynomial.C a_B * X ^ (2 * k) + Polynomial.C b_B := by
    rw [hA_eq_U2]
    dsimp [D_B, L_U, a_B, b_B]
    rw [htU_binom, hU_binom]
    have hx4k : ((X : F[X]) ^ (2 * k)) ^ 2 = X ^ (4 * k) := by
      rw [← pow_mul]; congr 1; omega
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    linear_combination -hx4k
  have hb_B_ne : b_B ≠ 0 := by
    have hc0 := congrArg (fun Z : F[X] ↦ Z.coeff 0) hA_biquad
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      coeff_X_pow_of_ne (by omega : 0 ≠ 4 * k),
      Polynomial.coeff_C_mul, coeff_X_pow_of_ne (by omega : 0 ≠ 2 * k),
      mul_zero, zero_add, zero_add, Polynomial.coeff_C_zero] at hc0
    rwa [← hc0]
  -- Evaluate `(A ^ 3).coeff (8 * k) = 3 * b_B + 3 * a_B ^ 2 = 0`
  have hA3_8k_zero : (A ^ 3).coeff (8 * k) = 0 := by
    rw [hA3_split, Polynomial.coeff_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 8 * k),
      coeff_X_pow_mul_of_lt U (by omega : 8 * k < 10 * k), add_zero]
  have hA3_expand :
      A ^ 3 =
        X ^ (12 * k) +
        Polynomial.C (3 * a_B) * X ^ (10 * k) +
        Polynomial.C (3 * b_B + 3 * a_B ^ 2) * X ^ (8 * k) +
        Polynomial.C (6 * a_B * b_B + a_B ^ 3) * X ^ (6 * k) +
        Polynomial.C (3 * b_B ^ 2 + 3 * a_B ^ 2 * b_B) * X ^ (4 * k) +
        Polynomial.C (3 * a_B * b_B ^ 2) * X ^ (2 * k) +
        Polynomial.C (b_B ^ 3) := by
    rw [hA_biquad]
    have h4 : (X : F[X]) ^ (4 * k) = (X ^ (2 * k)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    have h6 : (X : F[X]) ^ (6 * k) = (X ^ (2 * k)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    have h8 : (X : F[X]) ^ (8 * k) = (X ^ (2 * k)) ^ 4 := by rw [← pow_mul]; congr 1; omega
    have h10 : (X : F[X]) ^ (10 * k) = (X ^ (2 * k)) ^ 5 := by rw [← pow_mul]; congr 1; omega
    have h12 : (X : F[X]) ^ (12 * k) = (X ^ (2 * k)) ^ 6 := by rw [← pow_mul]; congr 1; omega
    rw [h4, h6, h8, h10, h12]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  have hA3_coeff_8k : (A ^ 3).coeff (8 * k) = 3 * b_B + 3 * a_B ^ 2 := by
    have hne12 : 8 * k ≠ 12 * k := by omega
    have hne10 : 8 * k ≠ 10 * k := by omega
    have hne6 : 8 * k ≠ 6 * k := by omega
    have hne4 : 8 * k ≠ 4 * k := by omega
    have hne2 : 8 * k ≠ 2 * k := by omega
    have hne0 : 8 * k ≠ 0 := by omega
    rw [hA3_expand]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, hne12, hne10, hne6, hne4, hne2, hne0, ↓reduceIte]
    ring
  have hb_eq_neg_a2 : b_B = -a_B ^ 2 := by
    have hsum0 : 3 * (b_B + a_B ^ 2) = 0 := by
      calc 3 * (b_B + a_B ^ 2) = 3 * b_B + 3 * a_B ^ 2 := by ring
        _ = (A ^ 3).coeff (8 * k) := hA3_coeff_8k.symm
        _ = 0 := hA3_8k_zero
    have hba0 : b_B + a_B ^ 2 = 0 := (mul_eq_zero.mp hsum0).resolve_left h3_ne
    exact eq_neg_of_add_eq_zero_left hba0
  have ha_B_ne : a_B ≠ 0 := by
    intro ha0
    rw [ha0, sq, zero_mul, neg_zero] at hb_eq_neg_a2
    exact hb_B_ne hb_eq_neg_a2
  -- Exact degree-5 division identity in `X ^ (2 * k)`
  set Q_5 : F[X] :=
    X ^ (6 * k) - Polynomial.C a_B * X ^ (4 * k) +
      Polynomial.C (2 * a_B ^ 2) * X ^ (2 * k) - Polynomial.C (3 * a_B ^ 3)
  set rem_5 : F[X] :=
    Polynomial.C (5 * a_B ^ 4) * X ^ (2 * k) - Polynomial.C (3 * a_B ^ 5 + α)
  have hdiv_5 : X ^ (10 * k) - Polynomial.C α = A * Q_5 + rem_5 := by
    rw [hA_biquad, hb_eq_neg_a2]
    dsimp [Q_5, rem_5]
    have h4 : (X : F[X]) ^ (4 * k) = (X ^ (2 * k)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    have h6 : (X : F[X]) ^ (6 * k) = (X ^ (2 * k)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    have h10 : (X : F[X]) ^ (10 * k) = (X ^ (2 * k)) ^ 5 := by rw [← pow_mul]; congr 1; omega
    rw [h4, h6, h10]
    simp only [map_neg, map_add, map_mul, map_pow, map_ofNat]
    ring
  obtain ⟨Q_kum, hQkum⟩ := hA_dvd_kummer
  have hA_dvd_rem : A ∣ rem_5 := by
    refine ⟨Q_kum - Q_5, ?_⟩
    linear_combination hQkum - hdiv_5
  have hrem_coeff_2k : rem_5.coeff (2 * k) = 5 * a_B ^ 4 := by
    dsimp [rem_5]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_X_pow_self,
      mul_one, coeff_C_of_ne_zero _ (by omega : 2 * k ≠ 0), sub_zero]
  have hrem_ne : rem_5 ≠ 0 := fun h0 ↦
    mul_ne_zero h5_ne (pow_ne_zero 4 ha_B_ne) (by rw [← hrem_coeff_2k, h0, Polynomial.coeff_zero])
  have hrem_deg : rem_5.natDegree ≤ 2 * k := by
    dsimp [rem_5]
    refine le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le ?_ (by rw [Polynomial.natDegree_C]; exact Nat.zero_le _))
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (Polynomial.natDegree_X_pow_le (2 * k))
  have hle_deg := Polynomial.natDegree_le_of_dvd hA_dvd_rem hrem_ne
  omega

private lemma branch_h_le_3k_false {F : Type*} [Field F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {A L₀ M₁ U : F[X]} {h k e f j : ℕ} {β c₀ lam : F}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h) (hh_le_3k : h ≤ 3 * k)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hp_gt : 4 * h < p)
    (hL₀_le : L₀.natDegree ≤ h - 2 * k)
    (hM₁_ne : M₁ ≠ 0) (hM₁_le : M₁.natDegree ≤ 4 * k - h)
    (hUm : U.Monic) (hUd : U.natDegree = h - 2 * k) (hU0 : U.coeff 0 ≠ 0)
    (hcop_AU : IsCoprime A U) (hcop_UtU : IsCoprime U (theta U))
    (hA3_3block : A ^ 3 = L₀ + X ^ f * M₁ + X ^ e * U)
    (hc₀_ne : c₀ ≠ 0)
    (hsym_coeff : ∀ d ≤ 3 * h,
      ((A ^ 3).coeff (3 * h - d)) ^ (p ^ j) * β ^ (3 * h - d) = c₀ ^ 3 * (A ^ 3).coeff d)
    (hw_eq :
      Polynomial.C ((4 * k : ℕ) : F) * M₁ * U + M₁ * theta U - U * theta M₁ =
        Polynomial.C lam * U ^ 2) : False := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hpj_pos : 0 < p ^ j := pow_pos hp_pos j
  -- Deduce `U ∣ M₁` and `M₁ = C ν * U` (`ν ≠ 0`)
  have hU_dvd_M1_tU : U ∣ theta U * M₁ := by
    refine ⟨Polynomial.C lam * U - Polynomial.C ((4 * k : ℕ) : F) * M₁ + theta M₁, ?_⟩
    linear_combination hw_eq
  have hU_dvd_M1 : U ∣ M₁ := hcop_UtU.dvd_of_dvd_mul_left hU_dvd_M1_tU
  obtain ⟨N_poly, hM1_UN⟩ := hU_dvd_M1
  have hN_ne : N_poly ≠ 0 := fun h0 ↦ hM₁_ne (by rw [hM1_UN, h0, mul_zero])
  have hN_le : N_poly.natDegree ≤ 6 * k - 2 * h := by
    have hd : M₁.natDegree = (h - 2 * k) + N_poly.natDegree := by
      rw [hM1_UN, Polynomial.natDegree_mul hUm.ne_zero hN_ne, hUd]
    omega
  have hN_ode : Polynomial.C ((4 * k : ℕ) : F) * N_poly - theta N_poly = Polynomial.C lam := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hUm.ne_zero)
    have hlhs :
        U ^ 2 * (Polynomial.C ((4 * k : ℕ) : F) * N_poly - theta N_poly) =
          Polynomial.C ((4 * k : ℕ) : F) * M₁ * U + M₁ * theta U - U * theta M₁ := by
      rw [hM1_UN, theta_mul]
      ring
    rw [hlhs, hw_eq, mul_comm]
  have hN_deg0 : N_poly.natDegree = 0 := by
    by_contra hN_pos
    set m : ℕ := N_poly.natDegree
    have hm_pos : 1 ≤ m := by omega
    have hm_lt_4k : m < 4 * k := by omega
    have h4k_lt_p : 4 * k < p := by omega
    have hcm := congrArg (fun Z : F[X] ↦ Z.coeff m) hN_ode
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_theta,
      coeff_C_of_ne_zero _ (by omega : m ≠ 0)] at hcm
    have hdiff_mul : (((4 * k - m : ℕ) : F)) * N_poly.coeff m = 0 := by
      rw [Nat.cast_sub (le_of_lt hm_lt_4k), sub_mul]
      exact hcm
    have h4km_ne : ((4 * k - m : ℕ) : F) ≠ 0 :=
      nat_cast_ne_zero_of_pos_lt (by omega : 0 < 4 * k - m) (by omega : 4 * k - m < p)
    have hlc_zero : N_poly.leadingCoeff = 0 := (mul_eq_zero.mp hdiff_mul).resolve_left h4km_ne
    exact (Polynomial.leadingCoeff_ne_zero.mpr hN_ne) hlc_zero
  set ν : F := N_poly.coeff 0
  have hN_eq_C : N_poly = Polynomial.C ν := Polynomial.eq_C_of_natDegree_eq_zero hN_deg0
  have hν_ne : ν ≠ 0 := fun h0 ↦ hN_ne (by rw [hN_eq_C, h0, map_zero])
  have hM1_eq_νU : M₁ = Polynomial.C ν * U := by rw [hM1_UN, hN_eq_C, mul_comm]
  -- Support-disjoint block coefficients of `A ^ 3 = L₀ + C ν * X ^ f * U + X ^ e * U`
  have hA3_ν : A ^ 3 = L₀ + Polynomial.C ν * (X ^ f * U) + X ^ e * U := by
    rw [hA3_3block, hM1_eq_νU]
    ring
  rcases lt_or_eq_of_le hh_le_3k with hh_lt_3k | rfl
  · -- Subcase `2 * k + 1 ≤ h < 3 * k`: evaluate symmetry at `d = f` (`3 * h - f = h + 2 * k`)
    have hf_le_3h : f ≤ 3 * h := by omega
    have hA3_at_f : (A ^ 3).coeff f = ν * U.coeff 0 := by
      rw [hA3_ν, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : L₀.natDegree < f),
        Polynomial.coeff_C_mul, coeff_X_pow_mul_of_le U le_rfl, Nat.sub_self,
        coeff_X_pow_mul_of_lt U (by omega : f < e), zero_add, add_zero]
    have hA3_at_mirror : (A ^ 3).coeff (3 * h - f) = 0 := by
      rw [hA3_ν, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : L₀.natDegree < 3 * h - f),
        Polynomial.coeff_C_mul, coeff_X_pow_mul_of_le U (by omega : f ≤ 3 * h - f),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : U.natDegree < (3 * h - f) - f),
        mul_zero, coeff_X_pow_mul_of_lt U (by omega : 3 * h - f < e), add_zero, add_zero]
    have hsym_f := hsym_coeff f hf_le_3h
    rw [hA3_at_mirror, zero_pow hpj_pos.ne', zero_mul, hA3_at_f] at hsym_f
    exact mul_ne_zero (pow_ne_zero 3 hc₀_ne) (mul_ne_zero hν_ne hU0) hsym_f.symm
  · -- Subcase `h = 3 * k`: `f = 4 * k`, `e = 8 * k`, `U.natDegree = k ≥ 1`, deduce `L₀ = C ρ * U`
    have hf_4k : f = 4 * k := by omega
    have he_8k : e = 8 * k := by omega
    have hUd_k : U.natDegree = k := by omega
    have hL₀_k : L₀.natDegree ≤ k := by omega
    set ρ : F := (ν ^ (p ^ j))⁻¹ * β ^ (4 * k) * ν
    have hL₀_eq_ρU : L₀ = Polynomial.C ρ * U := by
      ext i
      rw [Polynomial.coeff_C_mul]
      by_cases hi : i ≤ k
      · -- Compare `hsym_coeff i` (`3 * h - i = 9 * k - i`) and `hsym_coeff (4 * k + i)`
        have hsym1 := hsym_coeff i (by omega : i ≤ 3 * (3 * k))
        have hsym2 := hsym_coeff (4 * k + i) (by omega : 4 * k + i ≤ 3 * (3 * k))
        have hA3_i : (A ^ 3).coeff i = L₀.coeff i := by
          rw [hA3_ν, Polynomial.coeff_add, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, coeff_X_pow_mul_of_lt U (by omega : i < f), mul_zero,
            coeff_X_pow_mul_of_lt U (by omega : i < e), add_zero, add_zero]
        have hA3_9ki : (A ^ 3).coeff (3 * (3 * k) - i) = U.coeff (k - i) := by
          rw [hA3_ν, Polynomial.coeff_add, Polynomial.coeff_add,
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : L₀.natDegree < 3 * (3 * k) - i),
            Polynomial.coeff_C_mul, coeff_X_pow_mul_of_le U (by omega : f ≤ 3 * (3 * k) - i),
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by omega : U.natDegree < 3 * (3 * k) - i - f),
            mul_zero, coeff_X_pow_mul_of_le U (by omega : e ≤ 3 * (3 * k) - i),
            show 3 * (3 * k) - i - e = k - i by omega, zero_add, zero_add]
        have hA3_4ki : (A ^ 3).coeff (4 * k + i) = ν * U.coeff i := by
          rw [hA3_ν, Polynomial.coeff_add, Polynomial.coeff_add,
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : L₀.natDegree < 4 * k + i),
            Polynomial.coeff_C_mul, coeff_X_pow_mul_of_le U (by omega : f ≤ 4 * k + i),
            show 4 * k + i - f = i by omega,
            coeff_X_pow_mul_of_lt U (by omega : 4 * k + i < e),
            zero_add, add_zero]
        have hA3_5ki : (A ^ 3).coeff (3 * (3 * k) - (4 * k + i)) = ν * U.coeff (k - i) := by
          rw [hA3_ν, Polynomial.coeff_add, Polynomial.coeff_add,
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by omega : L₀.natDegree < 3 * (3 * k) - (4 * k + i)),
            Polynomial.coeff_C_mul,
            coeff_X_pow_mul_of_le U (by omega : f ≤ 3 * (3 * k) - (4 * k + i)),
            show 3 * (3 * k) - (4 * k + i) - f = k - i by omega,
            coeff_X_pow_mul_of_lt U (by omega : 3 * (3 * k) - (4 * k + i) < e),
            zero_add, add_zero]
        rw [hA3_i, hA3_9ki] at hsym1
        rw [hA3_4ki, hA3_5ki, mul_pow] at hsym2
        have hβ_split :
            β ^ (3 * (3 * k) - i) = β ^ (4 * k) * β ^ (3 * (3 * k) - (4 * k + i)) := by
          rw [← pow_add]
          congr 1
          omega
        have hrel :
            ν ^ (p ^ j) * (c₀ ^ 3 * L₀.coeff i) = β ^ (4 * k) * (c₀ ^ 3 * (ν * U.coeff i)) := by
          calc ν ^ (p ^ j) * (c₀ ^ 3 * L₀.coeff i)
              = ν ^ (p ^ j) * ((U.coeff (k - i)) ^ (p ^ j) * β ^ (3 * (3 * k) - i)) := by
                  rw [hsym1]
            _ = β ^ (4 * k) *
                  (ν ^ (p ^ j) * (U.coeff (k - i)) ^ (p ^ j) *
                    β ^ (3 * (3 * k) - (4 * k + i))) := by
                  rw [hβ_split]; ring
            _ = β ^ (4 * k) * (c₀ ^ 3 * (ν * U.coeff i)) := by rw [hsym2]
        have hc03_ne : c₀ ^ 3 ≠ 0 := pow_ne_zero 3 hc₀_ne
        have hνpj_ne : ν ^ (p ^ j) ≠ 0 := pow_ne_zero (p ^ j) hν_ne
        have hrel2 : ν ^ (p ^ j) * L₀.coeff i = β ^ (4 * k) * ν * U.coeff i := by
          apply mul_left_cancel₀ hc03_ne
          linear_combination hrel
        dsimp [ρ]
        apply mul_left_cancel₀ hνpj_ne
        calc ν ^ (p ^ j) * L₀.coeff i = β ^ (4 * k) * ν * U.coeff i := hrel2
          _ = (ν ^ (p ^ j) * (ν ^ (p ^ j))⁻¹) * (β ^ (4 * k) * ν * U.coeff i) := by
                rw [mul_inv_cancel₀ hνpj_ne, one_mul]
          _ = ν ^ (p ^ j) * ((ν ^ (p ^ j))⁻¹ * β ^ (4 * k) * ν * U.coeff i) := by ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : L₀.natDegree < i),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : U.natDegree < i), mul_zero]
    have hU_dvd_A3 : U ∣ A ^ 3 := by
      refine ⟨Polynomial.C ρ + Polynomial.C ν * X ^ f + X ^ e, ?_⟩
      rw [hA3_ν, hL₀_eq_ρU]
      ring
    have hcop_A3U : IsCoprime (A ^ 3) U := hcop_AU.pow_left
    obtain ⟨u_bez, v_bez, hbez⟩ := hcop_A3U
    obtain ⟨Z_A3, hZA3⟩ := hU_dvd_A3
    have hU_dvd_one : U ∣ (1 : F[X]) := by
      refine ⟨u_bez * Z_A3 + v_bez, ?_⟩
      calc (1 : F[X]) = u_bez * A ^ 3 + v_bez * U := hbez.symm
        _ = u_bez * (U * Z_A3) + v_bez * U := by rw [hZA3]
        _ = U * (u_bez * Z_A3 + v_bez) := by ring
    have hdeg_le := Polynomial.natDegree_le_of_dvd hU_dvd_one one_ne_zero
    rw [Polynomial.natDegree_one, hUd_k] at hdeg_le
    omega

/-! ## Part 6: Master Pure-`F[X]` `Theorem CW*` Cubic Obstruction -/

/-- **`Theorem CW*` (`M-0964` Result 13 + `M-0965` Result 14, Full Frobenius-Boundary Obstruction):**
Over any field `F` of prime characteristic `p` (`4 * h < p`) where `e = 2 * h + 2 * k`,
`f = 2 * h - 2 * k`, `1 ≤ k`, **`2 * k + 1 ≤ h`** (with NO upper bound on `k / h` beyond `h > 2 * k`),
`¬ (3 ∣ e)`, and `(p ^ j + 1) % e = 0` for some `j : ℕ`, there is NO solution `(A, B, Q)` to
`A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q` with `A` monic of degree `h`,
`B.natDegree ≤ h`, `B.eval 0 ≠ 0`, and `(Q ≠ 0 → Q.natDegree + f ≤ 2 * h)`. -/
theorem frobenius_boundary_cw_star_cubic_obstruction {F : Type*} [Field F] [DecidableEq F]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd : ¬ (3 ∣ e)) (hp_gt : 4 * h < p)
    (hfrob_inv : ∃ j : ℕ, (p ^ j + 1) % e = 0)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) : False := by
  by_cases h4k_lt : 4 * k + 1 ≤ h
  · exact frobenius_boundary_cubic_obstruction hk_pos h4k_lt he_eq hf_eq hndvd hp_gt
      hfrob_inv hAm hAd hBd hB0 hQd hident
  · have hh_le_4k : h ≤ 4 * k := by omega
    obtain ⟨P, U, α, β, c, c₀, j, hA0_ne, hP_le, hUm, hUd, hA3_split, hc_ne, hW_eq,
        hα_ne, hA_dvd_kummer, hβ_ne, hc₀_ne, hsym_coeff⟩ :=
      kummer_and_reversal_setup hk_pos h2k_lt he_eq hf_eq hndvd hp_gt hfrob_inv
        hAm hAd hBd hB0 hQd hident
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    have hpj_pos : 0 < p ^ j := pow_pos hp_pos j
    -- Lower gap `[h - 2 * k + 1, f - 1]` of `P` via Frobenius-reversal cube symmetry
    have hA3_coeff_lt : ∀ m < e, (A ^ 3).coeff m = P.coeff m := by
      intro m hm_lt
      rw [hA3_split, Polynomial.coeff_add, coeff_X_pow_mul_of_lt U hm_lt, add_zero]
    have hP_low_gap : ∀ d, h - 2 * k < d → d < f → P.coeff d = 0 := by
      intro d hd_lo hd_hi
      have hd_le_3h : d ≤ 3 * h := by omega
      have hm_gt : h + 2 * k < 3 * h - d := by omega
      have hm_lt_e : 3 * h - d < e := by omega
      have hA3_mirror_zero : (A ^ 3).coeff (3 * h - d) = 0 := by
        rw [hA3_coeff_lt (3 * h - d) hm_lt_e]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP_le hm_gt)
      have hsym := hsym_coeff d hd_le_3h
      rw [hA3_mirror_zero, zero_pow hpj_pos.ne', zero_mul] at hsym
      have hA3_d_zero : (A ^ 3).coeff d = 0 :=
        (mul_eq_zero.mp hsym.symm).resolve_left (pow_ne_zero 3 hc₀_ne)
      rw [← hA3_coeff_lt d (by omega : d < e)]
      exact hA3_d_zero
    -- Split `P = L₀ + X ^ f * M₁`
    set L₀ : F[X] := ∑ i ∈ Finset.range (h - 2 * k + 1), Polynomial.C (P.coeff i) * X ^ i
    set M₁ : F[X] := ∑ i ∈ Finset.range (4 * k - h + 1), Polynomial.C (P.coeff (f + i)) * X ^ i
    have hL₀_le : L₀.natDegree ≤ h - 2 * k := by
      dsimp [L₀]
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun i hi ↦ ?_⟩
      have hi_lt : i < h - 2 * k + 1 := Finset.mem_range.mp hi
      exact le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_trans (Polynomial.natDegree_X_pow_le i) (by omega))
    have hM₁_le : M₁.natDegree ≤ 4 * k - h := by
      dsimp [M₁]
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun i hi ↦ ?_⟩
      have hi_lt : i < 4 * k - h + 1 := Finset.mem_range.mp hi
      exact le_trans (Polynomial.natDegree_C_mul_le _ _)
        (le_trans (Polynomial.natDegree_X_pow_le i) (by omega))
    have hL₀_coeff : ∀ d, L₀.coeff d = if d ≤ h - 2 * k then P.coeff d else 0 := by
      intro d
      dsimp [L₀]
      rw [Polynomial.finsetSum_coeff]
      by_cases hd : d ≤ h - 2 * k
      · simp only [hd, ↓reduceIte]
        rw [Finset.sum_eq_single d]
        · rw [Polynomial.coeff_C_mul, coeff_X_pow_self, mul_one]
        · intro i _ hid
          rw [Polynomial.coeff_C_mul, coeff_X_pow_of_ne hid.symm, mul_zero]
        · intro hnot
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hd)) hnot
      · simp only [hd, ↓reduceIte]
        rw [Finset.sum_eq_zero]
        intro i hi
        have hi_lt : i < h - 2 * k + 1 := Finset.mem_range.mp hi
        rw [Polynomial.coeff_C_mul, coeff_X_pow_of_ne (by omega : d ≠ i), mul_zero]
    have hM₁_coeff : ∀ d, M₁.coeff d = if d ≤ 4 * k - h then P.coeff (f + d) else 0 := by
      intro d
      dsimp [M₁]
      rw [Polynomial.finsetSum_coeff]
      by_cases hd : d ≤ 4 * k - h
      · simp only [hd, ↓reduceIte]
        rw [Finset.sum_eq_single d]
        · rw [Polynomial.coeff_C_mul, coeff_X_pow_self, mul_one]
        · intro i _ hid
          rw [Polynomial.coeff_C_mul, coeff_X_pow_of_ne hid.symm, mul_zero]
        · intro hnot
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hd)) hnot
      · simp only [hd, ↓reduceIte]
        rw [Finset.sum_eq_zero]
        intro i hi
        have hi_lt : i < 4 * k - h + 1 := Finset.mem_range.mp hi
        rw [Polynomial.coeff_C_mul, coeff_X_pow_of_ne (by omega : d ≠ i), mul_zero]
    have hP_split : P = L₀ + X ^ f * M₁ := by
      ext d
      rw [Polynomial.coeff_add, hL₀_coeff]
      by_cases hd_lo : d ≤ h - 2 * k
      · simp only [hd_lo, ↓reduceIte]
        rw [coeff_X_pow_mul_of_lt M₁ (by omega : d < f), add_zero]
      · simp only [hd_lo, ↓reduceIte]
        by_cases hd_f : f ≤ d
        · rw [coeff_X_pow_mul_of_le M₁ hd_f, hM₁_coeff, zero_add]
          by_cases hd_hi : d - f ≤ 4 * k - h
          · simp only [hd_hi, ↓reduceIte]
            rw [Nat.add_sub_of_le hd_f]
          · simp only [hd_hi, ↓reduceIte]
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < d)
        · rw [coeff_X_pow_mul_of_lt M₁ (by omega : d < f), add_zero]
          exact hP_low_gap d (by omega) (by omega)
    have hA3_3block : A ^ 3 = L₀ + X ^ f * M₁ + X ^ e * U := by
      rw [hA3_split, hP_split]
    -- Case `M₁ = 0` contradicts `W.natDegree = e - 1` immediately
    by_cases hM₁_zero : M₁ = 0
    · have hP_low : P.natDegree ≤ h - 2 * k := by
        rw [hP_split, hM₁_zero, mul_zero, add_zero]
        exact hL₀_le
      set W : F[X] := Polynomial.C (3 : F) * A.derivative * P - A * P.derivative
      have hA'_deg : A.derivative.natDegree ≤ h - 1 := by
        rw [← hAd]
        exact Polynomial.natDegree_derivative_le A
      have hW_small : W.natDegree ≤ 2 * h - 2 * k - 1 := by
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
      have hW_exact : W.natDegree = e - 1 := by
        rw [hW_eq, Polynomial.natDegree_C_mul_X_pow (e - 1) c hc_ne]
      omega
    · -- `M₁ ≠ 0`: apply Lemma U + 3-term `θ`-Wronskian
      have hL₀_0 : L₀.coeff 0 ≠ 0 := by
        have hz_le : 0 ≤ h - 2 * k := Nat.zero_le _
        rw [hL₀_coeff]
        simp only [hz_le, ↓reduceIte]
        rw [← hA3_coeff_lt 0 (by omega : 0 < e),
          ← eval_zero_eq_coeff_zero, Polynomial.eval_pow, eval_zero_eq_coeff_zero]
        exact pow_ne_zero 3 hA0_ne
      obtain ⟨hU0, hcop_AU, hcop_UtU, ⟨c₁, hc₁_ne, hmod_U_tA⟩⟩ :=
        lemma_U_pure_FX hk_pos h2k_lt he_eq hf_eq hp_gt hAd hP_le hUm hUd
          hA3_split hα_ne hA_dvd_kummer
      obtain ⟨hw_deg, lam, hlam_ne, hA_dvd_w⟩ :=
        three_block_theta_wronskian_dvd hk_pos h2k_lt hh_le_4k he_eq hf_eq hp_gt hAm hAd
          hL₀_le hL₀_0 hM₁_zero hM₁_le hUd hU0 hc₁_ne hmod_U_tA hA3_3block
      set w : F[X] :=
        Polynomial.C ((4 * k : ℕ) : F) * M₁ * U + M₁ * theta U - U * theta M₁
      have hU2_monic : (U ^ 2).Monic := hUm.pow 2
      have hU2_deg : (U ^ 2).natDegree = 2 * h - 4 * k := by
        rw [Polynomial.natDegree_pow U 2, hUd]
        omega
      have hlamU2_deg : (Polynomial.C lam * U ^ 2).natDegree = 2 * h - 4 * k := by
        rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hlam_ne) hU2_monic.ne_zero,
          Polynomial.natDegree_C, zero_add, hU2_deg]
      -- Dispatch into Branch B (`h = 4 * k`), Branch A (`3 * k < h < 4 * k`), or Branch C (`h ≤ 3 * k`)
      rcases lt_or_eq_of_le hh_le_4k with hh_lt_4k | rfl
      · -- Both `3 * k < h < 4 * k` and `h ≤ 3 * k` satisfy `(w - C lam * U ^ 2).natDegree < h`,
        -- forcing `w = C lam * U ^ 2`!
        have hw_sub_lt_h : (w - Polynomial.C lam * U ^ 2).natDegree < h := by
          refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt ?_ ?_)
          · omega
          · omega
        have hw_eq_lamU2 : w = Polynomial.C lam * U ^ 2 := by
          by_contra hne
          have hsub_ne : w - Polynomial.C lam * U ^ 2 ≠ 0 := sub_ne_zero.mpr hne
          have hle := Polynomial.natDegree_le_of_dvd hA_dvd_w hsub_ne
          omega
        by_cases h3k_lt : 3 * k < h
        · -- Branch A (`CW⁺`: `3 * k < h < 4 * k`): `2 * h - 4 * k = w.natDegree ≤ 2 * k` contradicts `3 * k < h`!
          have hd_eq : w.natDegree = 2 * h - 4 * k := by rw [hw_eq_lamU2, hlamU2_deg]
          omega
        · -- Branch C (`2 * k + 1 ≤ h ≤ 3 * k`):
          exact branch_h_le_3k_false hk_pos h2k_lt (by omega : h ≤ 3 * k) he_eq hf_eq hp_gt
            hL₀_le hM₁_zero hM₁_le hUm hUd hU0 hcop_AU hcop_UtU hA3_3block
            hc₀_ne hsym_coeff hw_eq_lamU2
      · -- Branch B (`h = 4 * k`):
        exact branch_h_eq_4k_false hk_pos (by omega : 16 * k < p) hAm hAd hA0_ne
          (by omega : P.natDegree ≤ 6 * k) hM₁_zero (by omega : M₁.natDegree = 0)
          hUm (by omega : U.natDegree = 2 * k)
          (by rw [show 2 * (4 * k) + 2 * k = 10 * k by omega] at he_eq; subst he_eq; exact hA3_split)
          (by rw [show 2 * (4 * k) + 2 * k = 10 * k by omega] at he_eq; subst he_eq; exact hA_dvd_kummer)
          hlam_ne hA_dvd_w

/-! ## Part 7: Unconditional Frobenius-Boundary Vanishing Across All `5 ≤ r ≤ 31` -/

/-- **All-Dyadic Inner-Band Vanishing (`m = 5 * q + δ`) at `4 * h = 3 * q - δ` (`Theorem CW*`):**
Across every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), at `4 * h = 3 * q - δ` (`h ≤ δ`,
`q + h < 3 * δ`) with **NO** `h / k` side-conditions, whenever
`∃ j, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - q) = 0`, zero ambient or native circle codewords agree
with `C a * X ^ (5 * q + δ) + R` (`a ≠ 0`, `R.natDegree ≤ 2 ^ (r - 1)`) on `(5 * q + δ) - h` points
of `D`. -/
theorem ambient_and_native_vanishing_frobenius_boundary_cw_star_inner
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ (5 * 2 ^ (r - 3) + δ) + R) 0 := by
  by_cases hlow_h : h < 2 * (2 ^ (r - 3) - δ)
  · exact ambient_and_native_vanishing_inner_band hF hr_lo hr_hi hD_card hD_pow
      hδ_pos hδ_lt hh_le hqh (Or.inr (Or.inl hlow_h)) ha R hR
  · by_cases hlow_e : 3 * h < 3 * δ - 2 ^ (r - 3)
    · exact ambient_and_native_vanishing_inner_band hF hr_lo hr_hi hD_card hD_pow
        hδ_pos hδ_lt hh_le hqh (Or.inr (Or.inr hlow_e)) ha R hR
    · -- Exclude `h = 2 * (q - δ)` (`7 ∣ 5 * q`) and `3 * h = 3 * δ - q` (`3 ∣ q`)
      have hh_ne_2qd : h ≠ 2 * (2 ^ (r - 3) - δ) := by
        intro heq
        have h7 : 7 ∣ 5 * 2 ^ (r - 3) := ⟨δ, by omega⟩
        exact not_seven_dvd_five_mul_pow_two (r - 3) h7
      have h3h_ne_e : 3 * h ≠ 3 * δ - 2 ^ (r - 3) := by
        intro heq
        have h3 : 3 ∣ 2 ^ (r - 3) := ⟨δ - h, by rw [Nat.mul_sub]; omega⟩
        exact not_dvd_three_pow_two (r - 3) h3
      have hk_lo : 2 * (2 ^ (r - 3) - δ) < h := by omega
      have h3h_gt_e : 3 * δ - 2 ^ (r - 3) < 3 * h := by omega
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
        have hndvd : ¬ (3 ∣ (3 * δ - q)) :=
          not_dvd_three_sub_pow_two (by omega : 2 ^ (r - 3) < 3 * δ)
        have hrchar : ringChar F = 2 ^ 31 - 1 := mersenne_ext_ringChar hF
        have : CharP F (2 ^ 31 - 1) := ringChar.of_eq hrchar
        have hq_le : q ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) (by omega : r - 3 ≤ 28)
        rcases lt_or_eq_of_le hh'_le_h with hh'_lt | rfl
        · have hchar : ringChar F = 0 ∨ 3 * h' < ringChar F :=
            Or.inr (by rw [hrchar]; omega)
          exact wronskian_cubic_obstruction hAm hAd hBd hB0 he_pos hf_pos hndvd hchar hQd
            (by omega : 4 * h' < (3 * δ - q) + 4 * (q - δ)) hident
        · set k : ℕ := h' - 2 * (q - δ)
          exact frobenius_boundary_cw_star_cubic_obstruction (p := 2 ^ 31 - 1) (k := k)
            (by omega : 1 ≤ k)
            (by omega : 2 * k + 1 ≤ h')
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

/-- **Mirror Duality (`m = 7 * q - δ`) at `4 * h = 3 * q - δ` (`Theorem CW*`):**
Extends `ambient_and_native_vanishing_frobenius_boundary_cw_star_inner` to `m = 7 * 2 ^ (r - 3) - δ`
via Mersenne circle Frobenius inversion `x ^ p = x⁻¹` (`p = 2 ^ 31 - 1`). -/
theorem ambient_and_native_vanishing_frobenius_boundary_cw_star_mirror
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
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
  have hinner := ambient_and_native_vanishing_frobenius_boundary_cw_star_inner hF hr_lo hr_hi
    hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry hfrob hap_ne (conjRev R) (hconjRev_deg R)
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

/-! ## Part 8: Full Frobenius-Boundary Stratum, Narrowed Residual Sub-Lemma, & Instantiations -/

/-- Full parameter stratum for Wronskian-boundary Frobenius-inversion vanishing (`Theorem CW*`,
`M-0964` + `M-0965`), removing BOTH `5 * 2 ^ (r - 3) < u + 3 * δ` and
`3 * u + 11 * δ < 17 * 2 ^ (r - 3)` from `InSingleFrobeniusBoundaryStratum`. -/
def InSingleFullFrobeniusBoundaryStratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u < 2 * (2 ^ (r - 3) + δ) ∧
    4 * u + 5 * δ = 15 * 2 ^ (r - 3) ∧
    (∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0)

/-- Full `Theorem CW*` complement-vanishing proposition across all dyadic `5 ≤ r ≤ 31`. -/
def SingleMonomialFullFrobeniusBoundaryCWStarVanishing.{u} : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 5 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ δ : ℕ, 1 ≤ δ → δ < 2 ^ (r - 3) →
        ∀ m : ℕ, (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) →
          ∀ (γ : F) (U : Finset F),
            U.card < 2 * (2 ^ (r - 3) + δ) →
            4 * U.card + 5 * δ = 15 * 2 ^ (r - 3) →
            (∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0) →
            ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U

/-- **Main Full-Boundary Theorem (`SingleMonomialFullFrobeniusBoundaryCWStarVanishing`):**
Proves `¬ IsValidCWComplement D r (X ^ m) γ U` on **every** Wronskian-boundary cell
`4 * U.card + 5 * δ = 15 * 2 ^ (r - 3)` (`U.card < 2 * (2 ^ (r - 3) + δ)`) where `-1` is a power
of `2 ^ 31 - 1` modulo `3 * δ - 2 ^ (r - 3)` across all universes `u` and all `5 ≤ r ≤ 31`. -/
theorem singleMonomialFullFrobeniusBoundaryCWStarVanishing.{u} :
    SingleMonomialFullFrobeniusBoundaryCWStarVanishing.{u} := by
  intro F _ _ hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry_u hfrob hvalid
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
  have hh_le : h ≤ δ := by omega
  have hqh : 2 ^ (r - 3) + h < 3 * δ := by omega
  have hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ := by omega
  have hS_eq : (5 * 2 ^ (r - 3) + δ) - h = S.card := by omega
  rcases hm_eq with rfl | rfl
  · exact (ambient_and_native_vanishing_frobenius_boundary_cw_star_inner hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry hfrob one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · exact (ambient_and_native_vanishing_frobenius_boundary_cw_star_mirror hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry hfrob one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩

/-- Narrowed single-monomial residual complement bound excluding ALL `Theorem W` (`M-0934` / `M-0958`)
strata AND ALL full Frobenius-inversion Wronskian-boundary (`Theorem CW*`, `M-0964` / `M-0965`)
strata. -/
def SingleMonomialNonFrobeniusCWBound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ m : ℕ, 5 * 2 ^ (r - 3) ≤ m → m ≤ 7 * 2 ^ (r - 3) → ∀ γ : F,
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r ((X : F[X]) ^ m) γ U ∧
            ¬ InSingleWronskianStratum r m U.card ∧
            ¬ InSingleFullFrobeniusBoundaryStratum r m U.card) →
          𝒰.card ≤ K * 2 ^ r

/-- `SingleMonomialNonFrobeniusCWBound K` implies `SingleMonomialResidualCWBound K`. -/
theorem singleMonomialResidualCWBound_of_nonFrobenius.{u} {K : ℕ}
    (hNonFrob : SingleMonomialNonFrobeniusCWBound.{u} K) :
    SingleMonomialResidualCWBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 h𝒰
  refine hNonFrob F hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
  obtain ⟨hvalid, hnotW, _⟩ := h𝒰 U hUm
  refine ⟨hvalid, hnotW, ?_⟩
  rintro ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hbdry, hfrob⟩
  exact singleMonomialFullFrobeniusBoundaryCWStarVanishing F hF r hr5 hr_hi D hD_card hD_pow
    δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry hfrob hvalid

/-- Reduces `CanonicalInteriorCWBound.{u} K` to `SingleMonomialNonFrobeniusCWBound.{u} K` and
`MultiMonomialCanonicalCWBound.{u} K`. -/
theorem canonicalInteriorCWBound_of_nonFrobenius_and_multi_sublemmas.{u} {K : ℕ}
    (hNonFrob : SingleMonomialNonFrobeniusCWBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    CanonicalInteriorCWBound.{u} K :=
  canonicalInteriorCWBound_of_residual_and_multi_sublemmas
    (singleMonomialResidualCWBound_of_nonFrobenius hNonFrob)
    hMulti

/-- **Master `Theorem CW*`-Reduced Theorem (`MCAChallenge.InteriorThree K`):**
Reduces `MCAChallenge.InteriorThree.{u} K` (`1 ≤ K ≤ 2 ^ 20`) across all dyadic `4 ≤ r ≤ 31` directly
to `SingleMonomialNonFrobeniusCWBound.{u} K` and `MultiMonomialCanonicalCWBound.{u} K`. -/
theorem interiorThree_of_nonFrobenius_and_multi_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hNonFrob : SingleMonomialNonFrobeniusCWBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_residual_and_multi_sublemmas
    hK_pos
    hK_cap
    (singleMonomialResidualCWBound_of_nonFrobenius hNonFrob)
    hMulti

/-- **Unified `NativeListBound = 0` Corollary on All Full `Theorem CW*` Boundary Cells:**
For every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), whenever `4 * h = 3 * q - δ`, `h ≤ δ`,
`q + h < 3 * δ`, and `((2 ^ 31 - 1) ^ j + 1) % (3 * δ - q) = 0`, both `m = 5 * q + δ` and
`m = 7 * q - δ` satisfy `NativeListBound D (2 ^ (r - 1)) ((5 * q + δ) - h) (C a * X ^ m + R) 0`. -/
theorem nativeListBound_zero_frobenius_boundary_cw_star {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h m : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0)
    (hm_eq : m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ m + R) 0 := by
  rcases hm_eq with rfl | rfl
  · exact ambient_and_native_vanishing_frobenius_boundary_cw_star_inner hF hr_lo hr_hi
      hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry hfrob ha R hR
  · exact ambient_and_native_vanishing_frobenius_boundary_cw_star_mirror hF hr_lo hr_hi
      hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry hfrob ha R hR

/-- **Concrete `n = 512` (`r = 9`) `CW⁺` Cell `(δ, h) = (52, 35)` (`k = 11`, `3k < h < 4k`, `j = 11`):**
Proves `NativeListBound D 256 337 (C a * X ^ m + R) 0` for `m ∈ {372, 396}`. -/
theorem nativeListBound_zero_r9_cw_plus_372_396 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 512) (hD_pow : ∀ x ∈ D, x ^ 512 = 1)
    {m : ℕ} (hm : m = 372 ∨ m = 396)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 256) :
    MCAChallenge.NativeListBound D 256 337 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (9 - 3) + 52 ∨ m = 7 * 2 ^ (9 - 3) - 52 := by omega
  have hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * 52 - 2 ^ (9 - 3)) = 0 :=
    ⟨11 * 1, pow_mul_add_one_mod_eq_zero (by decide)⟩
  exact (nativeListBound_zero_frobenius_boundary_cw_star hF (r := 9) (δ := 52) (h := 35) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hfrob hm' ha R (by simpa using hR)).2

/-- **Concrete `n = 1024` (`r = 10`) `CW⁺` Cell `(δ, h) = (104, 70)` (`k = 22`, `3k < h < 4k`, `j = 11`):**
Proves `NativeListBound D 512 674 (C a * X ^ m + R) 0` for `m ∈ {744, 792}`. -/
theorem nativeListBound_zero_r10_cw_plus_744_792 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 1024) (hD_pow : ∀ x ∈ D, x ^ 1024 = 1)
    {m : ℕ} (hm : m = 744 ∨ m = 792)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 512) :
    MCAChallenge.NativeListBound D 512 674 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (10 - 3) + 104 ∨ m = 7 * 2 ^ (10 - 3) - 104 := by omega
  have hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * 104 - 2 ^ (10 - 3)) = 0 :=
    ⟨11 * 1, pow_mul_add_one_mod_eq_zero (by decide)⟩
  exact (nativeListBound_zero_frobenius_boundary_cw_star hF (r := 10) (δ := 104) (h := 70) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hfrob hm' ha R (by simpa using hR)).2

/-- **Concrete `n = 4096` (`r = 12`) `CW⁺` Cell `(δ, h) = (416, 280)` (`M-0964` Result 13, `k = 88`, `j = 11`):**
Proves `NativeListBound D 2048 2696 (C a * X ^ m + R) 0` for `m ∈ {2976, 3168}`. -/
theorem nativeListBound_zero_r12_cw_plus_2976_3168 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2976 ∨ m = 3168)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2696 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (12 - 3) + 416 ∨ m = 7 * 2 ^ (12 - 3) - 416 := by omega
  have hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * 416 - 2 ^ (12 - 3)) = 0 :=
    ⟨11 * 1, pow_mul_add_one_mod_eq_zero (by decide)⟩
  exact (nativeListBound_zero_frobenius_boundary_cw_star hF (r := 12) (δ := 416) (h := 280) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hfrob hm' ha R (by simpa using hR)).2

/-- **Concrete `n = 4096` (`r = 12`) `CW*` Cell `(δ, h) = (436, 275)` (`M-0965` Result 14, `k = 123`, `2k < h < 3k`, `j = 99`):**
Proves `NativeListBound D 2048 2721 (C a * X ^ m + R) 0` for `m ∈ {2996, 3148}`. -/
theorem nativeListBound_zero_r12_cw_star_2996_3148 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 2996 ∨ m = 3148)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2721 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (12 - 3) + 436 ∨ m = 7 * 2 ^ (12 - 3) - 436 := by omega
  have hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * 436 - 2 ^ (12 - 3)) = 0 :=
    ⟨11 * 9, pow_mul_add_one_mod_eq_zero (by decide)⟩
  exact (nativeListBound_zero_frobenius_boundary_cw_star hF (r := 12) (δ := 436) (h := 275) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hfrob hm' ha R (by simpa using hR)).2

/-- **Concrete `n = 4096` (`r = 12`) `CW*` Cell `(δ, h) = (440, 274)` (`M-0965` Result 14, `k = 130`, `2k < h < 3k`, `j = 25`):**
Proves `NativeListBound D 2048 2726 (C a * X ^ m + R) 0` for `m ∈ {3000, 3144}`. -/
theorem nativeListBound_zero_r12_cw_star_3000_3144 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 4096) (hD_pow : ∀ x ∈ D, x ^ 4096 = 1)
    {m : ℕ} (hm : m = 3000 ∨ m = 3144)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2048) :
    MCAChallenge.NativeListBound D 2048 2726 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (12 - 3) + 440 ∨ m = 7 * 2 ^ (12 - 3) - 440 := by omega
  have hfrob : ∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * 440 - 2 ^ (12 - 3)) = 0 :=
    ⟨5 * 5, pow_mul_add_one_mod_eq_zero (by decide)⟩
  exact (nativeListBound_zero_frobenius_boundary_cw_star hF (r := 12) (δ := 440) (h := 274) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hfrob hm' ha R (by simpa using hR)).2

end InteriorThreeTheoremCWStar
