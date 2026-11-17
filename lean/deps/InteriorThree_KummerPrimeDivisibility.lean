import MCAChallenge
import InteriorThree_CanonicalReduction
import InteriorThree_TheoremW
import InteriorThree_BoundaryCW
import InteriorThree_TheoremCWStar
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Kummer Prime-Divisibility Boundary Obstruction (`Lemma Q'_ℓ`) Across All Dyadic `5 ≤ r ≤ 31`

This composable module imports `MCAChallenge`, `InteriorThree_CanonicalReduction`,
`InteriorThree_TheoremW`, `InteriorThree_BoundaryCW`, and `InteriorThree_TheoremCWStar`, and proves
`@rukafe0x`'s **Result 19 `Lemma Q'_ℓ`** (`M-0970`, building on Result 8 `M-0959`) across **every
dyadic evaluation subgroup size `n = 2 ^ r` (`5 ≤ r ≤ 31`)**, eliminating **non-Frobenius**
Wronskian-boundary cells (`4 * U.card + 5 * δ = 15 * 2 ^ (r - 3)` where `-1 ∉ ⟨p mod e⟩` so
`Theorem CW*` cannot apply):

1. **`mersenne31_q_prime_conditions`:**
   Fuel-bounded binary modular exponentiation (`powModBin`) and bounded trial division certify in
   the Lean kernel that every prime `ℓ ∈ {7, 11, 31, 151, 331}` is an odd prime dividing
   `(2 ^ 31 - 1) - 1 = 2 ^ 31 - 2` for which `-3` is **not** an `ℓ`-th power in
   `ZMod (2 ^ 31 - 1)` (`(-3 : ZMod (2 ^ 31 - 1)) ^ ((2 ^ 31 - 2) / ℓ) ≠ 1`).
2. **`all_three_kummer_fibres_of_boundary_cubic`:**
   At any Wronskian boundary `4 * h = e + f` (`e = 2 * h + 2 * k`, `f = 2 * h - 2 * k`, `1 ≤ k`,
   `2 * k + 1 ≤ h`, `¬ (3 ∣ e)`, `ringChar F = 0 ∨ 4 * h < ringChar F`), extracts exact degrees
   `B₁.natDegree = h` and `Q₁.natDegree = 2 * k`, all **three** monic Kummer fibre divisibilities
   `A ∣ (X ^ e - C (-3 * ρ))`, `B₁ ∣ (X ^ e - C (-ρ * 3⁻¹))`, `Q₁ ∣ (X ^ e - C ρ)` (`ρ ≠ 0`), and
   the exact reversed `S`-identity
   `- C 3 * Ã * Q̃ * θ B̃ + B̃ * Q̃ * θ Ã + Ã * B̃ * θ Q̃ = C c₂ * X ^ e` (`c₂ ≠ 0`).
3. **`lemma_Q_prime_divisibility` & `lemma_Q_prime_cubic_obstruction` (`Lemma Q'_ℓ`):**
   Over any field `F` of prime characteristic `p > 4 * h`, if an odd prime `ℓ` satisfies `ℓ ∣ e`,
   `ℓ ∣ p - 1`, and `(-3 : ZMod p) ^ ((p - 1) / ℓ) ≠ 1`, then Newton power sums `(★)_m` (`1 ≤ m < e`)
   evaluated along `m = (e / ℓ) * t` (`1 ≤ t < ℓ`), combined with Euclidean GCD degree collapse
   against `X ^ ℓ + C 3` in `(ZMod p)[X]` and `ZMod ℓ` Fourier inversion, force **`ℓ ∣ h ∧ ℓ ∣ k`**.
   Hence `(¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ k))` yields an unconditional cubic contradiction.
4. **`singleMonomialQPrimeBoundaryVanishing` & `interiorThree_of_cwStar_qPrime_and_multi_sublemmas`:**
   Closes every Wronskian-boundary cell `4 * U.card + 5 * δ = 15 * 2 ^ (r - 3)` (`5 ≤ r ≤ 31`)
   having `ℓ ∈ {7, 11, 31, 151, 331}` with `ℓ ∣ (3 * δ - 2 ^ (r - 3))` and
   `(¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ k))`, narrowing `SingleMonomialNonFrobeniusCWBound K` to
   `SingleMonomialResidualAfterCWStarAndQPrimeBound K`, with explicit `NativeListBound = 0`
   corollaries on non-Frobenius cells at `n = 1024` (`m ∈ {748, 788}`) and `n = 2048`
   (`m ∈ {1468, 1604}` and `m ∈ {1496, 1576}`) where `Theorem CW*` fails.
-/

open scoped Polynomial BigOperators
open Polynomial InteriorThreeCanonicalReduction InteriorThreeTheoremW
  InteriorThreeBoundaryCW InteriorThreeTheoremCWStar

namespace InteriorThreeKummerPrimeDivisibility

/-! ## Part 1: Modular Binary Exponentiation, Prime Certificates, `theta`, and `revSum` -/

/-- Fuel-bounded binary modular exponentiation computing `(b ^ e) % m` in `O(fuel)` steps. -/
private def powModBin : ℕ → ℕ → ℕ → ℕ → ℕ
  | _, _, 0, m => 1 % m
  | 0, b, e, m => (b ^ e) % m
  | fuel + 1, b, e, m =>
    let half := powModBin fuel b (e / 2) m
    let sq := (half * half) % m
    if e % 2 = 0 then sq else (sq * (b % m)) % m

private lemma powModBin_eq : ∀ (fuel b e m : ℕ), powModBin fuel b e m = (b ^ e) % m
  | _, _, 0, _ => by simp [powModBin]
  | 0, _, _ + 1, _ => by simp [powModBin]
  | fuel + 1, b, e + 1, m => by
    have ih := powModBin_eq fuel b ((e + 1) / 2) m
    have hdiv : 2 * ((e + 1) / 2) + (e + 1) % 2 = e + 1 := Nat.div_add_mod (e + 1) 2
    have hlt : (e + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases hrem : (e + 1) % 2 = 0
    · have hexp : e + 1 = (e + 1) / 2 + (e + 1) / 2 := by omega
      simp only [powModBin, hrem, ↓reduceIte, ih]
      rw [← Nat.mul_mod, ← pow_add, ← hexp]
    · have hexp : e + 1 = ((e + 1) / 2 + (e + 1) / 2) + 1 := by omega
      simp only [powModBin, hrem, ↓reduceIte, ih]
      rw [← Nat.mul_mod (b ^ ((e + 1) / 2)) (b ^ ((e + 1) / 2)) m,
        ← Nat.mul_mod, ← pow_add, ← pow_succ, ← hexp]

/-- Bounded trial-division primality certificate for small odd primes. -/
private lemma prime_of_no_small_div {n B : ℕ} (hn : 2 ≤ n) (hsq : n < (B + 1) ^ 2)
    (hndiv : ∀ d ∈ Finset.Icc 2 B, n % d ≠ 0) :
    Nat.Prime n := by
  by_contra hnp
  have hmp : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
  have hmd : n.minFac ∣ n := Nat.minFac_dvd n
  have hmsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hleB : n.minFac ≤ B := by
    by_contra hgt
    push Not at hgt
    have hge : (B + 1) ^ 2 ≤ n.minFac ^ 2 := Nat.pow_le_pow_left hgt 2
    omega
  exact hndiv n.minFac (Finset.mem_Icc.mpr ⟨hmp.two_le, hleB⟩) (Nat.mod_eq_zero_of_dvd hmd)

private lemma nat_eq_of_cast_zmod_eq {p x y : ℕ} (hx : x < p) (hy : y < p)
    (heq : (x : ZMod p) = (y : ZMod p)) :
    x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsub0 : ((y - x : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (le_of_lt hlt), heq, sub_self]
    have hdvd : p ∣ (y - x) := (CharP.cast_eq_zero_iff (ZMod p) p (y - x)).mp hsub0
    have hle : p ≤ y - x := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hsub0 : ((x - y : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (le_of_lt hgt), heq, sub_self]
    have hdvd : p ∣ (x - y) := (CharP.cast_eq_zero_iff (ZMod p) p (x - y)).mp hsub0
    have hle : p ≤ x - y := Nat.le_of_dvd (by omega) hdvd
    omega

private lemma neg_three_pow_zmod_mersenne_ne_one {exp : ℕ}
    (hr_lt : powModBin 32 (2 ^ 31 - 4) exp (2 ^ 31 - 1) < 2 ^ 31 - 1)
    (hr_gt1 : 1 < powModBin 32 (2 ^ 31 - 4) exp (2 ^ 31 - 1)) :
    (-3 : ZMod (2 ^ 31 - 1)) ^ exp ≠ 1 := by
  let P : ℕ := 2 ^ 31 - 1
  let r : ℕ := powModBin 32 (2 ^ 31 - 4) exp P
  have hr_eq : r = ((2 ^ 31 - 4) ^ exp) % P := powModBin_eq 32 (2 ^ 31 - 4) exp P
  have hneg3 : (-3 : ZMod P) = ((2 ^ 31 - 4 : ℕ) : ZMod P) := by
    have hsum : (2 ^ 31 - 4) + 3 = P := by decide
    have h0 : (((2 ^ 31 - 4) + 3 : ℕ) : ZMod P) = 0 := by
      rw [hsum]
      exact CharP.cast_eq_zero (ZMod P) P
    rw [Nat.cast_add, Nat.cast_ofNat] at h0
    linear_combination -h0
  have hcast_mod : (((2 ^ 31 - 4) ^ exp : ℕ) : ZMod P) = (r : ZMod P) := by
    have hdiv := (Nat.div_add_mod ((2 ^ 31 - 4) ^ exp) P).symm
    conv_lhs => rw [hdiv]
    rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero (ZMod P) P, zero_mul, zero_add, ← hr_eq]
  rw [hneg3, ← Nat.cast_pow, hcast_mod]
  intro heq1
  have h1_eq : (1 : ZMod P) = ((1 : ℕ) : ZMod P) := by simp
  rw [h1_eq] at heq1
  have hr1 : r = 1 := nat_eq_of_cast_zmod_eq hr_lt (by decide : 1 < 2 ^ 31 - 1) heq1
  exact absurd hr1 (ne_of_gt hr_gt1)

/-- The five odd prime divisors of `2 ^ 31 - 2` for which `-3` is not an `ℓ`-th power in
`ZMod (2 ^ 31 - 1)` (`@rukafe0x` Result 19 `M-0970`). -/
def MersenneQPrimeSet : Finset ℕ := {7, 11, 31, 151, 331}

/-- **Kernel Certificate for `MersenneQPrimeSet` (`{7, 11, 31, 151, 331}`):**
Every `ℓ ∈ {7, 11, 31, 151, 331}` is an odd prime dividing `(2 ^ 31 - 1) - 1` with
`(-3 : ZMod (2 ^ 31 - 1)) ^ (((2 ^ 31 - 1) - 1) / ℓ) ≠ 1`. -/
theorem mersenne31_q_prime_conditions {ℓ : ℕ} (hℓ : ℓ ∈ MersenneQPrimeSet) :
    Nat.Prime ℓ ∧ ℓ % 2 = 1 ∧ ℓ ∣ ((2 ^ 31 - 1) - 1) ∧
      (-3 : ZMod (2 ^ 31 - 1)) ^ (((2 ^ 31 - 1) - 1) / ℓ) ≠ 1 := by
  simp only [MersenneQPrimeSet, Finset.mem_insert, Finset.mem_singleton] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨prime_of_no_small_div (B := 2) (by decide) (by decide) (by decide),
      by decide, ⟨306783378, by decide⟩,
      neg_three_pow_zmod_mersenne_ne_one (by decide) (by decide)⟩
  · exact ⟨prime_of_no_small_div (B := 3) (by decide) (by decide) (by decide),
      by decide, ⟨195225786, by decide⟩,
      neg_three_pow_zmod_mersenne_ne_one (by decide) (by decide)⟩
  · exact ⟨prime_of_no_small_div (B := 5) (by decide) (by decide) (by decide),
      by decide, ⟨69273666, by decide⟩,
      neg_three_pow_zmod_mersenne_ne_one (by decide) (by decide)⟩
  · exact ⟨prime_of_no_small_div (B := 12) (by decide) (by decide) (by decide),
      by decide, ⟨14221746, by decide⟩,
      neg_three_pow_zmod_mersenne_ne_one (by decide) (by decide)⟩
  · exact ⟨prime_of_no_small_div (B := 18) (by decide) (by decide) (by decide),
      by decide, ⟨6487866, by decide⟩,
      neg_three_pow_zmod_mersenne_ne_one (by decide) (by decide)⟩

/-- Logarithmic derivative operator `θ P = X * P'`. -/
private noncomputable def theta {R : Type*} [CommSemiring R] (P : R[X]) : R[X] :=
  X * P.derivative

private lemma theta_C {R : Type*} [CommSemiring R] (c : R) :
    theta (Polynomial.C c) = 0 := by
  simp [theta]

private lemma theta_one {R : Type*} [CommSemiring R] :
    theta (1 : R[X]) = 0 := by
  simp [theta]

private lemma theta_X {R : Type*} [CommSemiring R] :
    theta (X : R[X]) = X := by
  simp [theta]

private lemma theta_add {R : Type*} [CommSemiring R] (P Q : R[X]) :
    theta (P + Q) = theta P + theta Q := by
  unfold theta
  rw [Polynomial.derivative_add, mul_add]

private lemma theta_sub {R : Type*} [CommRing R] (P Q : R[X]) :
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

private lemma theta_X_pow {R : Type*} [CommSemiring R] (n : ℕ) :
    theta ((X : R[X]) ^ n) = Polynomial.C (n : R) * X ^ n := by
  cases n with
  | zero => simp [theta]
  | succ m =>
    unfold theta
    rw [Polynomial.derivative_X_pow, Nat.cast_add, Nat.cast_one]
    have hpow : (X : R[X]) * X ^ m = X ^ (m + 1) := by rw [pow_succ']
    calc (X : R[X]) * (Polynomial.C ((m : R) + 1) * X ^ m)
        = Polynomial.C ((m : R) + 1) * (X * X ^ m) := by ring
      _ = Polynomial.C ((m : R) + 1) * X ^ (m + 1) := by rw [hpow]

private lemma theta_sum {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    theta (∑ i ∈ s, f i) = ∑ i ∈ s, theta (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [theta]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, theta_add, ih, Finset.sum_insert ha]

private lemma theta_prod {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R[X]) :
    theta (∏ i ∈ s, f i) = ∑ i ∈ s, theta (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp [theta]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, theta_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i hi ↦ ?_)
    have hne : i ≠ a := fun h ↦ ha (h ▸ hi)
    have ha_not : a ∉ s.erase i := fun hm ↦ ha (Finset.mem_of_mem_erase hm)
    rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert ha_not]
    ring

private lemma theta_natDegree_le {R : Type*} [CommSemiring R] (P : R[X]) :
    (theta P).natDegree ≤ P.natDegree := by
  by_cases hP0 : P.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hP0, theta_C, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · unfold theta
    refine le_trans (Polynomial.natDegree_mul_le (p := X) (q := P.derivative)) ?_
    have hd : P.derivative.natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
    have hX : (X : R[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
    omega

private lemma theta_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (P : R[X]) :
    (theta P).map φ = theta (P.map φ) := by
  simp [theta, Polynomial.derivative_map]

/-- Formal degree-`N` polynomial reversal `revSum N P = ∑_{i=0}^N C (P.coeff i) * X ^ (N - i)`. -/
private noncomputable def revSum {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) : R[X] :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.C (P.coeff i) * X ^ (N - i)

private lemma eq_sum_range_of_natDegree_le {R : Type*} [Semiring R] {N : ℕ} {P : R[X]}
    (hP : P.natDegree ≤ N) :
    P = ∑ i ∈ Finset.range (N + 1), Polynomial.C (P.coeff i) * X ^ i := by
  ext k
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ N
  · have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp only [↓reduceIte, mul_one]
    · intro i _ hik
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp only [hik.symm, ↓reduceIte, mul_zero]
    · intro hnot
      exact absurd hmem hnot
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    symm
    refine Finset.sum_eq_zero (fun i hi ↦ ?_)
    have hi_le : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hne : ¬ (k = i) := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [hne, ↓reduceIte, mul_zero]

private lemma revSum_add {R : Type*} [Semiring R] (N : ℕ) (P Q : R[X]) :
    revSum N (P + Q) = revSum N P + revSum N Q := by
  unfold revSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Polynomial.coeff_add, map_add, add_mul]

private lemma revSum_sub {R : Type*} [Ring R] (N : ℕ) (P Q : R[X]) :
    revSum N (P - Q) = revSum N P - revSum N Q := by
  unfold revSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Polynomial.coeff_sub, map_sub, sub_mul]

private lemma revSum_sum {R : Type*} [Semiring R] {ι : Type*} (N : ℕ) (s : Finset ι)
    (f : ι → R[X]) :
    revSum N (∑ j ∈ s, f j) = ∑ j ∈ s, revSum N (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [revSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, revSum_add, ih, Finset.sum_insert ha]

private lemma revSum_C_mul {R : Type*} [Semiring R] (N : ℕ) (c : R) (P : R[X]) :
    revSum N (Polynomial.C c * P) = Polynomial.C c * revSum N P := by
  unfold revSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Polynomial.coeff_C_mul, map_mul, mul_assoc]

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

private lemma revSum_C {R : Type*} [Semiring R] (N : ℕ) (c : R) :
    revSum N (Polynomial.C c) = Polynomial.C c * X ^ N := by
  simpa using revSum_C_mul_X_pow (N := N) (s := 0) c (Nat.zero_le N)

private lemma revSum_X_pow_sub_C {R : Type*} [Ring R] (N : ℕ) (c : R) :
    revSum N ((X : R[X]) ^ N - Polynomial.C c) = 1 - Polynomial.C c * X ^ N := by
  rw [revSum_sub, revSum_C]
  have h1 : (X : R[X]) ^ N = Polynomial.C (1 : R) * X ^ N := by simp
  rw [h1, revSum_C_mul_X_pow (1 : R) (le_refl N), Nat.sub_self, pow_zero, map_one, mul_one]

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

private lemma revSum_map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (N : ℕ) (P : R[X]) :
    (revSum N P).map φ = revSum N (P.map φ) := by
  unfold revSum
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  simp [Polynomial.coeff_map]

private lemma theta_revSum {R : Type*} [CommRing R] {N : ℕ} {P : R[X]}
    (hP : P.natDegree ≤ N) :
    theta (revSum N P) = Polynomial.C (N : R) * revSum N P - revSum N (theta P) := by
  have hP_sum := eq_sum_range_of_natDegree_le hP
  have htheta_P : theta P =
      ∑ i ∈ Finset.range (N + 1), Polynomial.C ((i : R) * P.coeff i) * X ^ i := by
    conv_lhs => rw [hP_sum]
    rw [theta_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [theta_C_mul, theta_X_pow, map_mul]
    ring
  rw [htheta_P, revSum_sum]
  conv_lhs => unfold revSum
  rw [theta_sum]
  conv_rhs => rw [revSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  have hi_le : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [theta_C_mul, theta_X_pow, revSum_C_mul_X_pow _ hi_le, Nat.cast_sub hi_le, map_sub, map_mul]
  ring

private lemma revSum_prod_X_sub_C {R : Type*} [CommRing R] [DecidableEq R] (s : Finset R) :
    revSum s.card (∏ x ∈ s, (X - Polynomial.C x)) = ∏ x ∈ s, (1 - Polynomial.C x * X) := by
  induction s using Finset.induction_on with
  | empty => simp [revSum]
  | insert a s ha ih =>
    have hlin_deg : ∀ b : R, (X - Polynomial.C b).natDegree ≤ 1 := fun b ↦
      le_trans (Polynomial.natDegree_sub_le _ _)
        (max_le Polynomial.natDegree_X_le (by rw [Polynomial.natDegree_C]; decide))
    have hdeg_s : (∏ x ∈ s, (X - Polynomial.C x)).natDegree ≤ s.card := by
      refine le_trans (Polynomial.natDegree_prod_le s (fun x ↦ X - Polynomial.C x)) ?_
      trans ∑ _x ∈ s, 1
      · exact Finset.sum_le_sum (fun x _ ↦ hlin_deg x)
      · simp
    have hdeg_1 : (X - Polynomial.C a).natDegree ≤ 1 := hlin_deg a
    have hrev1 : revSum 1 (X - Polynomial.C a) = 1 - Polynomial.C a * X := by
      have hX1 : (X : R[X]) = X ^ 1 := (pow_one X).symm
      rw [hX1, revSum_X_pow_sub_C 1 a, pow_one]
    rw [Finset.card_insert_of_notMem ha, Nat.add_comm s.card 1,
      Finset.prod_insert ha, Finset.prod_insert ha,
      revSum_mul hdeg_1 hdeg_s, hrev1, ih]

private lemma coeff_X_pow_mul_of_lt {R : Type*} [Semiring R] {n j : ℕ} (P : R[X]) (hj : j < n) :
    ((X : R[X]) ^ n * P).coeff j = 0 := by
  rw [Polynomial.coeff_X_pow_mul']
  have hnot : ¬ (n ≤ j) := by omega
  simp only [hnot, ↓reduceIte]

/-! ## Part 2: All Three Kummer Fibres, Exact Degrees, and Reversed `S`-Identity in `F[X]` -/

/-- **All Three Kummer Fibres & Reversed `S`-Identity (`M-0959` Result 8):**
At the Wronskian boundary `4 * h = e + f` (`e = 2 * h + 2 * k`, `f = 2 * h - 2 * k`, `1 ≤ k`,
`2 * k + 1 ≤ h`, `¬ (3 ∣ e)`, `ringChar F = 0 ∨ 4 * h < ringChar F`), any solution `(A, B, Q)` to
`A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q` with `A` monic of degree `h`,
`B.natDegree ≤ h`, `B.eval 0 ≠ 0`, and `Q ≠ 0 → Q.natDegree + f ≤ 2 * h` yields monic normalizations
`B₁, Q₁ : F[X]` and scalars `ρ ≠ 0`, `c₂ ≠ 0` such that:
- `B₁.Monic ∧ B₁.natDegree = h` and `Q₁.Monic ∧ Q₁.natDegree = 2 * k`,
- `A ∣ (X ^ e - C (-3 * ρ))`, `B₁ ∣ (X ^ e - C (-ρ * 3⁻¹))`, and `Q₁ ∣ (X ^ e - C ρ)`,
- `- C 3 * revSum h A * revSum (2 * k) Q₁ * theta (revSum h B₁)
    + revSum h B₁ * revSum (2 * k) Q₁ * theta (revSum h A)
    + revSum h A * revSum h B₁ * theta (revSum (2 * k) Q₁) = C c₂ * X ^ e`. -/
theorem all_three_kummer_fibres_of_boundary_cubic {F : Type*} [Field F] [DecidableEq F]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd3 : ¬ (3 ∣ e))
    (hchar4 : ringChar F = 0 ∨ 4 * h < ringChar F)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) :
    ∃ (B₁ Q₁ : F[X]) (ρ c₂ : F),
      B₁.Monic ∧ B₁.natDegree = h ∧
      Q₁.Monic ∧ Q₁.natDegree = 2 * k ∧
      ρ ≠ 0 ∧ c₂ ≠ 0 ∧
      A ∣ ((X : F[X]) ^ e - Polynomial.C (-3 * ρ)) ∧
      B₁ ∣ ((X : F[X]) ^ e - Polynomial.C (-ρ * (3 : F)⁻¹)) ∧
      Q₁ ∣ ((X : F[X]) ^ e - Polynomial.C ρ) ∧
      (- Polynomial.C (3 : F) * revSum h A * revSum (2 * k) Q₁ * theta (revSum h B₁) +
        revSum h B₁ * revSum (2 * k) Q₁ * theta (revSum h A) +
        revSum h A * revSum h B₁ * theta (revSum (2 * k) Q₁) =
          Polynomial.C c₂ * X ^ e) := by
  have h3_ne : (3 : F) ≠ 0 := by
    intro h30
    have hdvd : ringChar F ∣ 3 := (ringChar.spec F 3).mp (by simpa using h30)
    rcases hchar4 with hc0 | hcgt
    · rw [hc0, zero_dvd_iff] at hdvd
      omega
    · have hle : ringChar F ≤ 3 := Nat.le_of_dvd (by decide) hdvd
      omega
  have hB_ne : B ≠ 0 := fun h0 ↦ hB0 (by simp [h0])
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, mul_zero] at hident
    have heq_cube : (X : F[X]) ^ e * B ^ 3 = -(A ^ 3) := by linear_combination hident
    have hA3_monic : (A ^ 3).Monic := hAm.pow 3
    have hA3_deg : (A ^ 3).natDegree = 3 * h := by rw [Polynomial.natDegree_pow, hAd]
    have hXe_ne : (X : F[X]) ^ e ≠ 0 := pow_ne_zero e Polynomial.X_ne_zero
    have hB3_ne : B ^ 3 ≠ 0 := pow_ne_zero 3 hB_ne
    have hdeg_eq := congrArg Polynomial.natDegree heq_cube
    rw [Polynomial.natDegree_mul hXe_ne hB3_ne, Polynomial.natDegree_X_pow,
      Polynomial.natDegree_pow, Polynomial.natDegree_neg, hA3_deg] at hdeg_eq
    exact hndvd3 ⟨h - B.natDegree, by omega⟩
  have hQ_le : Q.natDegree ≤ 2 * k := by have := hQd hQ_ne; omega
  let P : F[X] := B * Q
  have hP_ne : P ≠ 0 := mul_ne_zero hB_ne hQ_ne
  have hP_le : P.natDegree ≤ h + 2 * k := by
    rw [Polynomial.natDegree_mul hB_ne hQ_ne]; omega
  let R : F[X] := X ^ f * A * Q - B ^ 3
  have hident' : A ^ 3 + X ^ e * B ^ 3 = (X ^ e * X ^ f * A + B) * Q := by
    rw [← pow_add]; exact hident
  have hP_eq : P = A ^ 3 - X ^ e * R := by
    dsimp [P, R]; linear_combination -hident'
  have hA3_monic : (A ^ 3).Monic := hAm.pow 3
  have hA3_deg : (A ^ 3).natDegree = 3 * h := by rw [Polynomial.natDegree_pow, hAd]
  have hR_le : R.natDegree ≤ h - 2 * k := by
    by_cases hR0 : R = 0
    · simp [hR0]
    · have hXe_ne : (X : F[X]) ^ e ≠ 0 := pow_ne_zero e Polynomial.X_ne_zero
      have hXeR_eq : X ^ e * R = A ^ 3 - P := by linear_combination hP_eq
      have hrhs_deg : (A ^ 3 - P).natDegree ≤ 3 * h :=
        le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_of_eq hA3_deg) (by omega))
      have hlhs_deg : (X ^ e * R).natDegree = e + R.natDegree :=
        (Polynomial.natDegree_mul hXe_ne hR0).trans (by rw [Polynomial.natDegree_X_pow])
      rw [← hXeR_eq, hlhs_deg] at hrhs_deg
      omega
  -- Primary Wronskian `W = C 3 * A' * P - A * P' = C c * X ^ (e - 1)` (`c ≠ 0`)
  let e1 : ℕ := e - 1
  have he1_succ : e1 + 1 = e := by omega
  let W : F[X] := Polynomial.C (3 : F) * A.derivative * P - A * P.derivative
  let V : F[X] := Polynomial.C ((e1 + 1 : ℕ) : F) * A * R +
      X * (A * R.derivative - Polynomial.C (3 : F) * A.derivative * R)
  have hW_factor : W = X ^ e1 * V := by
    have hP_eq1 : P = A ^ 3 - X ^ (e1 + 1) * R := by rw [he1_succ]; exact hP_eq
    dsimp [W, V]
    rw [hP_eq1, Polynomial.derivative_sub, Polynomial.derivative_pow,
      Polynomial.derivative_mul, Polynomial.derivative_X_pow, pow_succ]
    simp only [Nat.cast_ofNat, Nat.add_sub_cancel]
    ring
  have hA_der_le : A.derivative.natDegree ≤ h - 1 := by
    have := Polynomial.natDegree_derivative_le A; omega
  have hW_deg_of_P : W.natDegree ≤ h - 1 + P.natDegree := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_mul_le (p := Polynomial.C (3 : F) * A.derivative) (q := P)) ?_
      have hcA : (Polynomial.C (3 : F) * A.derivative).natDegree ≤ h - 1 :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) hA_der_le
      omega
    · by_cases hPd0 : P.derivative = 0
      · simp [hPd0]
      · have hP_pos : 1 ≤ P.natDegree := by
          by_contra h0
          have hP0 : P.natDegree = 0 := by omega
          rw [Polynomial.eq_C_of_natDegree_eq_zero hP0, Polynomial.derivative_C] at hPd0
          exact hPd0 rfl
        have hPd_le : P.derivative.natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
        refine le_trans (Polynomial.natDegree_mul_le (p := A) (q := P.derivative)) ?_
        omega
  have hW_le : W.natDegree ≤ e1 := le_trans hW_deg_of_P (by omega)
  have hchar3 : ringChar F = 0 ∨ 3 * h < ringChar F := by
    rcases hchar4 with hc0 | hcgt
    · exact Or.inl hc0
    · exact Or.inr (by omega)
  have hW_ne : W ≠ 0 := by
    intro hW0
    have hsub0 : Polynomial.C (3 : F) * A.derivative * P = A * P.derivative := sub_eq_zero.mp hW0
    have hwronsk : (A ^ 3).derivative * P = A ^ 3 * P.derivative := by
      rw [Polynomial.derivative_pow]
      simp only [Nat.cast_ofNat]
      calc (3 : F[X]) * A ^ 2 * A.derivative * P
          = A ^ 2 * (Polynomial.C (3 : F) * A.derivative * P) := by
              rw [← map_ofNat Polynomial.C 3]; ring
        _ = A ^ 2 * (A * P.derivative) := by rw [hsub0]
        _ = A ^ 3 * P.derivative := by ring
    have hdvd : A ^ 3 ∣ P :=
      dvd_of_derivative_mul_eq hA3_monic.ne_zero (le_of_eq hA3_deg) hchar3 hwronsk
    have hle := Polynomial.natDegree_le_of_dvd hdvd hP_ne
    omega
  have hV_ne : V ≠ 0 := fun hV0 ↦ hW_ne (by rw [hW_factor, hV0, mul_zero])
  have hV_deg0 : V.natDegree = 0 := by
    have hXe1_ne : (X : F[X]) ^ e1 ≠ 0 := pow_ne_zero e1 Polynomial.X_ne_zero
    have hmul_deg : W.natDegree = e1 + V.natDegree := by
      rw [hW_factor, Polynomial.natDegree_mul hXe1_ne hV_ne, Polynomial.natDegree_X_pow]
    omega
  let c : F := V.coeff 0
  have hVc : V = Polynomial.C c := Polynomial.eq_C_of_natDegree_eq_zero hV_deg0
  have hc_ne : c ≠ 0 := fun hc0 ↦ hV_ne (by rw [hVc, hc0, map_zero])
  have hW_eq : W = Polynomial.C c * X ^ e1 := by rw [hW_factor, hVc, mul_comm]
  have hW_deg_exact : W.natDegree = e1 := by
    rw [hW_eq, Polynomial.natDegree_C_mul hc_ne, Polynomial.natDegree_X_pow]
  -- Exact degrees `B.natDegree = h` and `Q.natDegree = 2 * k`
  have hP_deg_exact : P.natDegree = h + 2 * k := by
    have hge : e1 ≤ h - 1 + P.natDegree := hW_deg_exact ▸ hW_deg_of_P
    omega
  have hBQ_deg_sum : B.natDegree + Q.natDegree = h + 2 * k := by
    rw [← Polynomial.natDegree_mul hB_ne hQ_ne]
    exact hP_deg_exact
  have hB_deg_exact : B.natDegree = h := by omega
  have hQ_deg_exact : Q.natDegree = 2 * k := by omega
  -- Dual Wronskian `W_dual = C 3 * B' * R - B * R' = X ^ (f - 1) * S₀`, `S₀ = C c'` (`c' ≠ 0`)
  let f1 : ℕ := f - 1
  have hf1_succ : f1 + 1 = f := by omega
  let S₀ : F[X] :=
    Q * (Polynomial.C (3 : F) * A * theta B - B * theta A - Polynomial.C (f : F) * A * B) -
      A * B * theta Q
  let W_dual : F[X] := Polynomial.C (3 : F) * B.derivative * R - B * R.derivative
  have hW_dual_factor : W_dual = X ^ f1 * S₀ := by
    have hR_eq1 : R = X ^ (f1 + 1) * A * Q - B ^ 3 := by rw [hf1_succ]
    have hf_cast : (f : F) = (f1 : F) + 1 := by
      rw [← hf1_succ, Nat.cast_add, Nat.cast_one]
    dsimp only [W_dual, S₀, theta]
    rw [hR_eq1, hf_cast, Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.derivative_pow, pow_succ]
    simp only [Nat.cast_ofNat, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      map_add, map_one, map_ofNat]
    ring
  have hR_ne : R ≠ 0 := by
    intro hR0
    have hB3_eq : X ^ f * A * Q = B ^ 3 := sub_eq_zero.mp hR0
    have hev := congrArg (fun T : F[X] ↦ T.eval 0) hB3_eq
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      zero_pow (by omega : f ≠ 0), zero_mul] at hev
    exact pow_ne_zero 3 hB0 hev.symm
  have hW_dual_le : W_dual.natDegree ≤ f1 := by
    have hB_der_le : B.derivative.natDegree ≤ h - 1 := by
      have := Polynomial.natDegree_derivative_le B; omega
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_mul_le (p := Polynomial.C (3 : F) * B.derivative) (q := R)) ?_
      have hcB : (Polynomial.C (3 : F) * B.derivative).natDegree ≤ h - 1 :=
        le_trans (Polynomial.natDegree_C_mul_le _ _) hB_der_le
      omega
    · by_cases hRd0 : R.derivative = 0
      · simp [hRd0]
      · have hR_pos : 1 ≤ R.natDegree := by
          by_contra h0
          have hR0 : R.natDegree = 0 := by omega
          rw [Polynomial.eq_C_of_natDegree_eq_zero hR0, Polynomial.derivative_C] at hRd0
          exact hRd0 rfl
        have hRd_le : R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
        refine le_trans (Polynomial.natDegree_mul_le (p := B) (q := R.derivative)) ?_
        omega
  have hW_dual_ne : W_dual ≠ 0 := by
    intro hWd0
    have hsub0 : Polynomial.C (3 : F) * B.derivative * R = B * R.derivative := sub_eq_zero.mp hWd0
    have hB3_ne : B ^ 3 ≠ 0 := pow_ne_zero 3 hB_ne
    have hB3_deg : (B ^ 3).natDegree = 3 * h := by rw [Polynomial.natDegree_pow, hB_deg_exact]
    have hwronsk : (B ^ 3).derivative * R = B ^ 3 * R.derivative := by
      rw [Polynomial.derivative_pow]
      simp only [Nat.cast_ofNat]
      calc (3 : F[X]) * B ^ 2 * B.derivative * R
          = B ^ 2 * (Polynomial.C (3 : F) * B.derivative * R) := by
              rw [← map_ofNat Polynomial.C 3]; ring
        _ = B ^ 2 * (B * R.derivative) := by rw [hsub0]
        _ = B ^ 3 * R.derivative := by ring
    have hdvd : B ^ 3 ∣ R := dvd_of_derivative_mul_eq hB3_ne (le_of_eq hB3_deg) hchar3 hwronsk
    have hle := Polynomial.natDegree_le_of_dvd hdvd hR_ne
    omega
  have hS₀_ne : S₀ ≠ 0 := fun hS0 ↦ hW_dual_ne (by rw [hW_dual_factor, hS0, mul_zero])
  have hS₀_deg0 : S₀.natDegree = 0 := by
    have hXf1_ne : (X : F[X]) ^ f1 ≠ 0 := pow_ne_zero f1 Polynomial.X_ne_zero
    have hmul_deg : W_dual.natDegree = f1 + S₀.natDegree := by
      rw [hW_dual_factor, Polynomial.natDegree_mul hXf1_ne hS₀_ne, Polynomial.natDegree_X_pow]
    omega
  let c' : F := S₀.coeff 0
  have hS₀_eq : S₀ = Polynomial.C c' := Polynomial.eq_C_of_natDegree_eq_zero hS₀_deg0
  have hc'_ne : c' ≠ 0 := fun hc0 ↦ hS₀_ne (by rw [hS₀_eq, hc0, map_zero])
  -- Monic normalizations `B₁ := C b₀⁻¹ * B` and `Q₁ := C q₀⁻¹ * Q`
  let b₀ : F := B.leadingCoeff
  let q₀ : F := Q.leadingCoeff
  have hb₀_ne : b₀ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB_ne
  have hq₀_ne : q₀ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ_ne
  let B₁ : F[X] := Polynomial.C b₀⁻¹ * B
  let Q₁ : F[X] := Polynomial.C q₀⁻¹ * Q
  have hB₁_monic : B₁.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact inv_mul_cancel₀ hb₀_ne
  have hB₁_deg : B₁.natDegree = h := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hb₀_ne), hB_deg_exact]
  have hQ₁_monic : Q₁.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact inv_mul_cancel₀ hq₀_ne
  have hQ₁_deg : Q₁.natDegree = 2 * k := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hq₀_ne), hQ_deg_exact]
  have hB_scale : B = Polynomial.C b₀ * B₁ := by
    dsimp only [B₁]; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hb₀_ne, map_one, one_mul]
  have hQ_scale : Q = Polynomial.C q₀ * Q₁ := by
    dsimp only [Q₁]; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq₀_ne, map_one, one_mul]
  have hbq_ne : b₀ * q₀ ≠ 0 := mul_ne_zero hb₀_ne hq₀_ne
  let c₁ : F := (b₀ * q₀)⁻¹ * c
  let c₂ : F := (b₀ * q₀)⁻¹ * c'
  have hc₁_ne : c₁ ≠ 0 := mul_ne_zero (inv_ne_zero hbq_ne) hc_ne
  have hc₂_ne : c₂ ≠ 0 := mul_ne_zero (inv_ne_zero hbq_ne) hc'_ne
  let W₁ : F[X] := Polynomial.C (3 : F) * theta A * (B₁ * Q₁) - A * theta (B₁ * Q₁)
  let S₁ : F[X] :=
    Q₁ * (Polynomial.C (3 : F) * A * theta B₁ - B₁ * theta A - Polynomial.C (f : F) * A * B₁) -
      A * B₁ * theta Q₁
  have hXW_eq : X * W = Polynomial.C (b₀ * q₀) * W₁ := by
    dsimp only [W, P, W₁]
    rw [hB_scale, hQ_scale]
    have hprod_bq :
        (Polynomial.C b₀ * B₁) * (Polynomial.C q₀ * Q₁) = Polynomial.C (b₀ * q₀) * (B₁ * Q₁) := by
      rw [map_mul]; ring
    rw [hprod_bq, Polynomial.derivative_C_mul]
    dsimp only [theta]
    rw [map_mul]
    ring
  have hW₁_eq : W₁ = Polynomial.C c₁ * X ^ e := by
    have hXWe : X * W = Polynomial.C c * X ^ e := by
      rw [hW_eq, show (X : F[X]) * (Polynomial.C c * X ^ e1) = Polynomial.C c * (X ^ e1 * X) by ring,
        ← pow_succ, he1_succ]
    calc W₁
        = Polynomial.C (b₀ * q₀)⁻¹ * (Polynomial.C (b₀ * q₀) * W₁) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hbq_ne, map_one, one_mul]
      _ = Polynomial.C (b₀ * q₀)⁻¹ * (Polynomial.C c * X ^ e) := by
            rw [← hXW_eq, hXWe]
      _ = Polynomial.C c₁ * X ^ e := by
            rw [← mul_assoc, ← map_mul]
  have hS₀_scale : S₀ = Polynomial.C (b₀ * q₀) * S₁ := by
    dsimp only [S₀, S₁]
    rw [hB_scale, hQ_scale, theta_C_mul b₀ B₁, theta_C_mul q₀ Q₁, map_mul]
    ring
  have hS₁_eq : S₁ = Polynomial.C c₂ := by
    calc S₁
        = Polynomial.C (b₀ * q₀)⁻¹ * (Polynomial.C (b₀ * q₀) * S₁) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hbq_ne, map_one, one_mul]
      _ = Polynomial.C (b₀ * q₀)⁻¹ * Polynomial.C c' := by
            rw [← hS₀_scale, hS₀_eq]
      _ = Polynomial.C c₂ := by
            rw [← map_mul]
  -- All three Kummer divisibilities with `ρ := c₂ * c₁⁻¹ ≠ 0`
  let ρ : F := c₂ * c₁⁻¹
  have hρ_ne : ρ ≠ 0 := mul_ne_zero hc₂_ne (inv_ne_zero hc₁_ne)
  have hc₂_eq : c₂ = ρ * c₁ := by dsimp only [ρ]; rw [mul_assoc, inv_mul_cancel₀ hc₁_ne, mul_one]
  have hdvd_A : A ∣ ((X : F[X]) ^ e - Polynomial.C (-3 * ρ)) := by
    have hcomb : W₁ + Polynomial.C (3 : F) * S₁ =
        A * (Polynomial.C (8 : F) * Q₁ * theta B₁ -
          Polynomial.C (3 * (f : F)) * B₁ * Q₁ -
          Polynomial.C (4 : F) * B₁ * theta Q₁) := by
      dsimp only [W₁, S₁]
      rw [theta_mul, map_mul]
      simp only [map_ofNat]
      ring
    have hrhs : W₁ + Polynomial.C (3 : F) * S₁ =
        Polynomial.C c₁ * ((X : F[X]) ^ e - Polynomial.C (-3 * ρ)) := by
      rw [hW₁_eq, hS₁_eq, hc₂_eq, mul_sub, ← map_mul, ← map_mul]
      have hsc : 3 * (ρ * c₁) = -(c₁ * (-3 * ρ)) := by ring
      rw [hsc, map_neg]
      ring
    refine ⟨Polynomial.C c₁⁻¹ * (Polynomial.C (8 : F) * Q₁ * theta B₁ -
      Polynomial.C (3 * (f : F)) * B₁ * Q₁ - Polynomial.C (4 : F) * B₁ * theta Q₁), ?_⟩
    calc (X : F[X]) ^ e - Polynomial.C (-3 * ρ)
        = Polynomial.C c₁⁻¹ * (Polynomial.C c₁ * ((X : F[X]) ^ e - Polynomial.C (-3 * ρ))) := by
            rw [← mul_assoc (Polynomial.C c₁⁻¹), ← map_mul, inv_mul_cancel₀ hc₁_ne, map_one, one_mul]
      _ = Polynomial.C c₁⁻¹ * (A * (Polynomial.C (8 : F) * Q₁ * theta B₁ -
            Polynomial.C (3 * (f : F)) * B₁ * Q₁ - Polynomial.C (4 : F) * B₁ * theta Q₁)) := by
            rw [← hrhs, hcomb]
      _ = A * (Polynomial.C c₁⁻¹ * (Polynomial.C (8 : F) * Q₁ * theta B₁ -
            Polynomial.C (3 * (f : F)) * B₁ * Q₁ - Polynomial.C (4 : F) * B₁ * theta Q₁)) := by
            ring
  have hdvd_B₁ : B₁ ∣ ((X : F[X]) ^ e - Polynomial.C (-ρ * (3 : F)⁻¹)) := by
    have h3c₁_ne : (3 : F) * c₁ ≠ 0 := mul_ne_zero h3_ne hc₁_ne
    have hcomb : Polynomial.C (3 : F) * W₁ + S₁ =
        B₁ * (Polynomial.C (8 : F) * Q₁ * theta A -
          Polynomial.C (f : F) * A * Q₁ -
          Polynomial.C (4 : F) * A * theta Q₁) := by
      dsimp only [W₁, S₁]
      rw [theta_mul]
      simp only [map_ofNat]
      ring
    have hrhs : Polynomial.C (3 : F) * W₁ + S₁ =
        Polynomial.C ((3 : F) * c₁) * ((X : F[X]) ^ e - Polynomial.C (-ρ * (3 : F)⁻¹)) := by
      rw [hW₁_eq, hS₁_eq, hc₂_eq, mul_sub, ← mul_assoc, ← map_mul, ← map_mul]
      have hsc : ρ * c₁ = -((3 * c₁) * (-ρ * (3 : F)⁻¹)) := by
        calc ρ * c₁ = ρ * c₁ * ((3 : F) * (3 : F)⁻¹) := by rw [mul_inv_cancel₀ h3_ne, mul_one]
          _ = -((3 * c₁) * (-ρ * (3 : F)⁻¹)) := by ring
      rw [hsc, map_neg]
      ring
    refine ⟨Polynomial.C ((3 : F) * c₁)⁻¹ * (Polynomial.C (8 : F) * Q₁ * theta A -
      Polynomial.C (f : F) * A * Q₁ - Polynomial.C (4 : F) * A * theta Q₁), ?_⟩
    calc (X : F[X]) ^ e - Polynomial.C (-ρ * (3 : F)⁻¹)
        = Polynomial.C ((3 : F) * c₁)⁻¹ *
            (Polynomial.C ((3 : F) * c₁) * ((X : F[X]) ^ e - Polynomial.C (-ρ * (3 : F)⁻¹))) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h3c₁_ne, map_one, one_mul]
      _ = Polynomial.C ((3 : F) * c₁)⁻¹ * (B₁ * (Polynomial.C (8 : F) * Q₁ * theta A -
            Polynomial.C (f : F) * A * Q₁ - Polynomial.C (4 : F) * A * theta Q₁)) := by
            rw [← hrhs, hcomb]
      _ = B₁ * (Polynomial.C ((3 : F) * c₁)⁻¹ * (Polynomial.C (8 : F) * Q₁ * theta A -
            Polynomial.C (f : F) * A * Q₁ - Polynomial.C (4 : F) * A * theta Q₁)) := by
            ring
  have hdvd_Q₁ : Q₁ ∣ ((X : F[X]) ^ e - Polynomial.C ρ) := by
    have hcomb : W₁ - S₁ =
        Q₁ * (Polynomial.C (4 : F) * B₁ * theta A -
          Polynomial.C (4 : F) * A * theta B₁ +
          Polynomial.C (f : F) * A * B₁) := by
      dsimp only [W₁, S₁]
      rw [theta_mul]
      simp only [map_ofNat]
      ring
    have hrhs : W₁ - S₁ = Polynomial.C c₁ * ((X : F[X]) ^ e - Polynomial.C ρ) := by
      rw [hW₁_eq, hS₁_eq, hc₂_eq, mul_sub, ← map_mul]
      have hsc : ρ * c₁ = c₁ * ρ := mul_comm ρ c₁
      rw [hsc]
    refine ⟨Polynomial.C c₁⁻¹ * (Polynomial.C (4 : F) * B₁ * theta A -
      Polynomial.C (4 : F) * A * theta B₁ + Polynomial.C (f : F) * A * B₁), ?_⟩
    calc (X : F[X]) ^ e - Polynomial.C ρ
        = Polynomial.C c₁⁻¹ * (Polynomial.C c₁ * ((X : F[X]) ^ e - Polynomial.C ρ)) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc₁_ne, map_one, one_mul]
      _ = Polynomial.C c₁⁻¹ * (Q₁ * (Polynomial.C (4 : F) * B₁ * theta A -
            Polynomial.C (4 : F) * A * theta B₁ + Polynomial.C (f : F) * A * B₁)) := by
            rw [← hrhs, hcomb]
      _ = Q₁ * (Polynomial.C c₁⁻¹ * (Polynomial.C (4 : F) * B₁ * theta A -
            Polynomial.C (4 : F) * A * theta B₁ + Polynomial.C (f : F) * A * B₁)) := by
            ring
  -- Exact reversed `S₁` identity at degree `e = 2 * h + 2 * k`
  have hrev_S₁ :
      - Polynomial.C (3 : F) * revSum h A * revSum (2 * k) Q₁ * theta (revSum h B₁) +
        revSum h B₁ * revSum (2 * k) Q₁ * theta (revSum h A) +
        revSum h A * revSum h B₁ * theta (revSum (2 * k) Q₁) =
          Polynomial.C c₂ * X ^ e := by
    have hAd_le : A.natDegree ≤ h := le_of_eq hAd
    have hB₁d_le : B₁.natDegree ≤ h := le_of_eq hB₁_deg
    have hQ₁d_le : Q₁.natDegree ≤ 2 * k := le_of_eq hQ₁_deg
    have htA_le : (theta A).natDegree ≤ h := le_trans (theta_natDegree_le A) hAd_le
    have htB₁_le : (theta B₁).natDegree ≤ h := le_trans (theta_natDegree_le B₁) hB₁d_le
    have htQ₁_le : (theta Q₁).natDegree ≤ 2 * k := le_trans (theta_natDegree_le Q₁) hQ₁d_le
    have hS₁_expand :
        S₁ = Polynomial.C (3 : F) * (Q₁ * (A * theta B₁)) -
          Q₁ * (B₁ * theta A) -
          Polynomial.C (f : F) * (Q₁ * (A * B₁)) -
          A * (B₁ * theta Q₁) := by
      dsimp only [S₁]; ring
    have he_2k_2h : e = 2 * k + (h + h) := by omega
    have he_h_h_2k : e = h + (h + 2 * k) := by omega
    have hAB₁_le : (A * B₁).natDegree ≤ h + h :=
      le_trans (Polynomial.natDegree_mul_le (p := A) (q := B₁)) (by omega)
    have hAtB₁_le : (A * theta B₁).natDegree ≤ h + h :=
      le_trans (Polynomial.natDegree_mul_le (p := A) (q := theta B₁)) (by omega)
    have hB₁tA_le : (B₁ * theta A).natDegree ≤ h + h :=
      le_trans (Polynomial.natDegree_mul_le (p := B₁) (q := theta A)) (by omega)
    have hB₁tQ₁_le : (B₁ * theta Q₁).natDegree ≤ h + 2 * k :=
      le_trans (Polynomial.natDegree_mul_le (p := B₁) (q := theta Q₁)) (by omega)
    have hrev_lhs :
        revSum e (Polynomial.C (3 : F) * (Q₁ * (A * theta B₁)) -
          Q₁ * (B₁ * theta A) -
          Polynomial.C (f : F) * (Q₁ * (A * B₁)) -
          A * (B₁ * theta Q₁)) = revSum e (Polynomial.C c₂) :=
      congrArg (revSum e) (hS₁_expand.symm.trans hS₁_eq)
    rw [revSum_C, revSum_sub, revSum_sub, revSum_sub, revSum_C_mul, revSum_C_mul] at hrev_lhs
    have hr1 : revSum e (Q₁ * (A * theta B₁)) =
        revSum (2 * k) Q₁ * (revSum h A * revSum h (theta B₁)) := by
      rw [he_2k_2h, revSum_mul hQ₁d_le hAtB₁_le, revSum_mul hAd_le htB₁_le]
    have hr2 : revSum e (Q₁ * (B₁ * theta A)) =
        revSum (2 * k) Q₁ * (revSum h B₁ * revSum h (theta A)) := by
      rw [he_2k_2h, revSum_mul hQ₁d_le hB₁tA_le, revSum_mul hB₁d_le htA_le]
    have hr3 : revSum e (Q₁ * (A * B₁)) =
        revSum (2 * k) Q₁ * (revSum h A * revSum h B₁) := by
      rw [he_2k_2h, revSum_mul hQ₁d_le hAB₁_le, revSum_mul hAd_le hB₁d_le]
    have hr4 : revSum e (A * (B₁ * theta Q₁)) =
        revSum h A * (revSum h B₁ * revSum (2 * k) (theta Q₁)) := by
      rw [he_h_h_2k, revSum_mul hAd_le hB₁tQ₁_le, revSum_mul hB₁d_le htQ₁_le]
    rw [hr1, hr2, hr3, hr4] at hrev_lhs
    have htrA : revSum h (theta A) = Polynomial.C (h : F) * revSum h A - theta (revSum h A) := by
      linear_combination theta_revSum hAd_le
    have htrB₁ : revSum h (theta B₁) = Polynomial.C (h : F) * revSum h B₁ - theta (revSum h B₁) := by
      linear_combination theta_revSum hB₁d_le
    have htrQ₁ : revSum (2 * k) (theta Q₁) =
        Polynomial.C ((2 * k : ℕ) : F) * revSum (2 * k) Q₁ - theta (revSum (2 * k) Q₁) := by
      linear_combination theta_revSum hQ₁d_le
    rw [htrA, htrB₁, htrQ₁] at hrev_lhs
    have hf_cast : Polynomial.C (f : F) =
        Polynomial.C (2 : F) * Polynomial.C (h : F) -
          Polynomial.C ((2 * k : ℕ) : F) := by
      rw [hf_eq, Nat.cast_sub (by omega : 2 * k ≤ 2 * h), map_sub, Nat.cast_mul, map_mul,
        Nat.cast_ofNat]
    rw [hf_cast] at hrev_lhs
    simp only [map_ofNat] at hrev_lhs ⊢
    linear_combination hrev_lhs
  exact ⟨B₁, Q₁, ρ, c₂, hB₁_monic, hB₁_deg, hQ₁_monic, hQ₁_deg,
    hρ_ne, hc₂_ne, hdvd_A, hdvd_B₁, hdvd_Q₁, hrev_S₁⟩

/-! ## Part 3: Exact Newton Power Sums `(★)_m` & Fibre-Block Partition over `IsAlgClosed` -/

private lemma geom_sum_one_sub_C_mul_X {R : Type*} [CommRing R] (x : R) :
    ∀ e : ℕ,
      (1 - Polynomial.C x * X) * (∑ j ∈ Finset.range e, Polynomial.C (x ^ j) * X ^ j) =
        1 - Polynomial.C (x ^ e) * X ^ e
  | 0 => by simp
  | e + 1 => by
    rw [Finset.sum_range_succ, mul_add, geom_sum_one_sub_C_mul_X x e]
    have hterm :
        (1 - Polynomial.C x * X) * (Polynomial.C (x ^ e) * X ^ e) =
          Polynomial.C (x ^ e) * X ^ e - Polynomial.C (x ^ (e + 1)) * X ^ (e + 1) := by
      rw [pow_succ x e, pow_succ X e, map_mul]
      ring
    rw [hterm]
    ring

private lemma separable_X_pow_sub_C {E : Type*} [Field E] {e : ℕ} (he_pos : 1 ≤ e)
    (he_ne : (e : E) ≠ 0) {δ : E} (hδ_ne : δ ≠ 0) :
    ((X : E[X]) ^ e - Polynomial.C δ).Separable := by
  unfold Polynomial.Separable
  have he1 : (e - 1) + 1 = e := by omega
  have hder : ((X : E[X]) ^ e - Polynomial.C δ).derivative = Polynomial.C (e : E) * X ^ (e - 1) := by
    rw [← he1, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero, Nat.add_sub_cancel, he1]
  rw [hder]
  refine ⟨Polynomial.C (-δ⁻¹), Polynomial.C (δ⁻¹ * (e : E)⁻¹) * X, ?_⟩
  have hXpow : (X : E[X]) * X ^ (e - 1) = X ^ e := by
    conv_rhs => rw [← he1, pow_succ']
  have h1 : Polynomial.C (-δ⁻¹) * ((X : E[X]) ^ e - Polynomial.C δ) =
      - (Polynomial.C δ⁻¹ * X ^ e) + 1 := by
    rw [mul_sub, ← map_mul, neg_mul, inv_mul_cancel₀ hδ_ne]
    simp only [map_neg, map_one, neg_mul, sub_neg_eq_add]
  have h2 : Polynomial.C (δ⁻¹ * (e : E)⁻¹) * X * (Polynomial.C (e : E) * X ^ (e - 1)) =
      Polynomial.C δ⁻¹ * X ^ e := by
    calc Polynomial.C (δ⁻¹ * (e : E)⁻¹) * X * (Polynomial.C (e : E) * X ^ (e - 1))
        = (Polynomial.C (δ⁻¹ * (e : E)⁻¹) * Polynomial.C (e : E)) * (X * X ^ (e - 1)) := by ring
      _ = Polynomial.C (δ⁻¹ * ((e : E)⁻¹ * (e : E))) * X ^ e := by
          rw [← map_mul, mul_assoc, hXpow]
      _ = Polynomial.C δ⁻¹ * X ^ e := by rw [inv_mul_cancel₀ he_ne, mul_one]
  rw [h1, h2]
  ring

/-- Root `Finset` and exact Newton power-sum identity for any monic divisor `M` of `X ^ e - C δ`
over an algebraically closed field `E`. -/
private lemma kummer_divisor_roots_and_newton_sum {E : Type*} [Field E] [IsAlgClosed E]
    [DecidableEq E] {e : ℕ} (he_pos : 1 ≤ e) (he_ne : (e : E) ≠ 0) {δ : E} (hδ_ne : δ ≠ 0)
    {M : E[X]} (hMm : M.Monic) (hdvd : M ∣ ((X : E[X]) ^ e - Polynomial.C δ)) :
    let R_M : Finset E := M.roots.toFinset
    R_M.card = M.natDegree ∧
    M = ∏ x ∈ R_M, (X - Polynomial.C x) ∧
    (∀ x ∈ R_M, x ^ e = δ) ∧
    (∃ M_rev_comp : E[X],
      revSum M.natDegree M * M_rev_comp = 1 - Polynomial.C δ * X ^ e ∧
      ∀ m : ℕ, 1 ≤ m → m < e →
        (theta (revSum M.natDegree M) * M_rev_comp).coeff m = - ∑ x ∈ R_M, x ^ m) := by
  intro R_M
  obtain ⟨M_comp, hfac⟩ := hdvd
  have hXe_monic : ((X : E[X]) ^ e - Polynomial.C δ).Monic :=
    Polynomial.monic_X_pow_sub_C δ (by omega)
  have hXe_deg : ((X : E[X]) ^ e - Polynomial.C δ).natDegree = e :=
    Polynomial.natDegree_X_pow_sub_C
  have hM_comp_ne : M_comp ≠ 0 := fun h0 ↦ hXe_monic.ne_zero (by rw [hfac, h0, mul_zero])
  have hdeg_sum : M.natDegree + M_comp.natDegree = e := by
    have hd := congrArg Polynomial.natDegree hfac
    rw [hXe_deg, Polynomial.natDegree_mul hMm.ne_zero hM_comp_ne] at hd
    exact hd.symm
  have hsep_M : M.Separable :=
    (separable_X_pow_sub_C he_pos he_ne hδ_ne).of_dvd ⟨M_comp, hfac⟩
  have hnup : M.roots.Nodup := Polynomial.nodup_roots hsep_M
  have hsplits : M.Splits := IsAlgClosed.splits M
  have hcard_R : R_M.card = M.natDegree := by
    dsimp only [R_M]
    rw [Multiset.toFinset_card_of_nodup hnup, ← hsplits.natDegree_eq_card_roots]
  have hprod_R : M = ∏ x ∈ R_M, (X - Polynomial.C x) := by
    rw [Finset.prod_eq_multiset_prod]
    have hval : R_M.val = M.roots := Multiset.dedup_eq_self.mpr hnup
    rw [hval]
    exact hsplits.eq_prod_roots_of_monic hMm
  have hpow_R : ∀ x ∈ R_M, x ^ e = δ := by
    intro x hx
    have hx_root : M.eval x = 0 :=
      (Polynomial.mem_roots hMm.ne_zero).mp (Multiset.mem_toFinset.mp hx)
    have hev := congrArg (fun T : E[X] ↦ T.eval x) hfac
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul, hx_root, zero_mul] at hev
    exact sub_eq_zero.mp hev
  let d : ℕ := M.natDegree
  let M_rev : E[X] := revSum d M
  let M_rev_comp : E[X] := revSum (e - d) M_comp
  have hM_comp_deg : M_comp.natDegree = e - d := by omega
  have hrev_prod : M_rev * M_rev_comp = 1 - Polynomial.C δ * X ^ e := by
    dsimp only [M_rev, M_rev_comp]
    rw [← revSum_mul (le_refl d) (le_of_eq hM_comp_deg),
      show d + (e - d) = e by omega, ← hfac, revSum_X_pow_sub_C]
  have hM_rev_prod : M_rev = ∏ x ∈ R_M, (1 - Polynomial.C x * X) := by
    dsimp only [M_rev, d]
    rw [← hcard_R]
    calc revSum R_M.card M
        = revSum R_M.card (∏ x ∈ R_M, (X - Polynomial.C x)) := by rw [← hprod_R]
      _ = ∏ x ∈ R_M, (1 - Polynomial.C x * X) := revSum_prod_X_sub_C R_M
  have hnewton_poly :
      theta M_rev * M_rev_comp =
        - ∑ x ∈ R_M, ∑ j ∈ Finset.range e, Polynomial.C (x ^ (j + 1)) * X ^ (j + 1) := by
    have htheta_M_rev :
        theta M_rev * M_rev_comp =
          ∑ x ∈ R_M, theta (1 - Polynomial.C x * X) *
            ((∏ y ∈ R_M.erase x, (1 - Polynomial.C y * X)) * M_rev_comp) := by
      rw [hM_rev_prod, theta_prod, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ ↦ by ring)
    rw [htheta_M_rev, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    have hx_e : x ^ e = δ := hpow_R x hx
    have hlin_ne : (1 - Polynomial.C x * X : E[X]) ≠ 0 := by
      intro h0
      have hc0 := congrArg (fun T : E[X] ↦ T.coeff 0) h0
      simp at hc0
    have hcancel :
        (∏ y ∈ R_M.erase x, (1 - Polynomial.C y * X)) * M_rev_comp =
          ∑ j ∈ Finset.range e, Polynomial.C (x ^ j) * X ^ j := by
      apply mul_left_cancel₀ hlin_ne
      calc (1 - Polynomial.C x * X) * ((∏ y ∈ R_M.erase x, (1 - Polynomial.C y * X)) * M_rev_comp)
          = ((1 - Polynomial.C x * X) * ∏ y ∈ R_M.erase x, (1 - Polynomial.C y * X)) * M_rev_comp := by
              ring
        _ = M_rev * M_rev_comp := by
            rw [Finset.mul_prod_erase R_M (fun y ↦ 1 - Polynomial.C y * X) hx, ← hM_rev_prod]
        _ = 1 - Polynomial.C (x ^ e) * X ^ e := by rw [hrev_prod, hx_e]
        _ = (1 - Polynomial.C x * X) * ∑ j ∈ Finset.range e, Polynomial.C (x ^ j) * X ^ j :=
              (geom_sum_one_sub_C_mul_X x e).symm
    have htheta_lin : theta (1 - Polynomial.C x * X) = - (Polynomial.C x * X) := by
      rw [theta_sub, theta_one, theta_C_mul, theta_X, zero_sub]
    rw [htheta_lin, hcancel, neg_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [pow_succ' x j, pow_succ' X j, map_mul]
    ring
  refine ⟨hcard_R, hprod_R, hpow_R, M_rev_comp, hrev_prod, fun m hm_pos hm_lt ↦ ?_⟩
  rw [hnewton_poly, Polynomial.coeff_neg, Polynomial.finsetSum_coeff]
  congr 1
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rw [Polynomial.finsetSum_coeff]
  have hm1_mem : m - 1 ∈ Finset.range e := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single (m - 1)]
  · have hm_eq : (m - 1) + 1 = m := by omega
    rw [hm_eq, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [↓reduceIte, mul_one]
  · intro j _ hne
    have hne' : ¬ (m = j + 1) := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [hne', ↓reduceIte, mul_zero]
  · intro hnot
    exact absurd hm1_mem hnot

private lemma coeff_one_sub_C_X_pow_mul_of_lt {R : Type*} [CommRing R] {e m : ℕ} (δ : R)
    (U : R[X]) (hm : m < e) :
    ((1 - Polynomial.C δ * X ^ e) * U).coeff m = U.coeff m := by
  have hexp : (1 - Polynomial.C δ * X ^ e) * U = U - X ^ e * (Polynomial.C δ * U) := by ring
  rw [hexp, Polynomial.coeff_sub, coeff_X_pow_mul_of_lt _ hm, sub_zero]

/-- Over an algebraically closed field `E`, if `ζ : E` satisfies `ζ ^ ℓ = 1` and `ζ ^ d ≠ 1` for
`1 ≤ d < ℓ`, then `X ^ ℓ - C (γ ^ ℓ) = ∏ b ∈ Finset.range ℓ, (X - C (γ * ζ ^ b))` for every
`γ ≠ 0`. -/
private lemma X_pow_sub_C_pow_eq_prod_zeta {E : Type*} [Field E] [DecidableEq E]
    {ℓ : ℕ} (hℓ_pos : 1 ≤ ℓ) {ζ γ : E} (hζ_ne : ζ ≠ 0) (hζ_pow : ζ ^ ℓ = 1)
    (hζ_prim : ∀ d : ℕ, 1 ≤ d → d < ℓ → ζ ^ d ≠ 1) (hγ_ne : γ ≠ 0) :
    (X : E[X]) ^ ℓ - Polynomial.C (γ ^ ℓ) =
      ∏ b ∈ Finset.range ℓ, (X - Polynomial.C (γ * ζ ^ b)) := by
  let P₁ : E[X] := (X : E[X]) ^ ℓ - Polynomial.C (γ ^ ℓ)
  let P₂ : E[X] := ∏ b ∈ Finset.range ℓ, (X - Polynomial.C (γ * ζ ^ b))
  have hP₁_monic : P₁.Monic := Polynomial.monic_X_pow_sub_C (γ ^ ℓ) (by omega)
  have hP₁_deg : P₁.natDegree = ℓ := Polynomial.natDegree_X_pow_sub_C
  have hP₂_monic : P₂.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun b _ ↦ Polynomial.monic_X_sub_C _)
  have hP₂_deg : P₂.natDegree = ℓ := by
    dsimp only [P₂]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun b _ ↦ Polynomial.monic_X_sub_C _)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  have hinj : Set.InjOn (fun b : ℕ ↦ γ * ζ ^ b) (Finset.range ℓ) := by
    intro b₁ hb₁ b₂ hb₂ heq
    have hb₁_lt : b₁ < ℓ := Finset.mem_range.mp hb₁
    have hb₂_lt : b₂ < ℓ := Finset.mem_range.mp hb₂
    have hpow_eq : ζ ^ b₁ = ζ ^ b₂ := mul_left_cancel₀ hγ_ne heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : ζ ^ b₁ * 1 = ζ ^ b₁ * ζ ^ (b₂ - b₁) := by
        rw [mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
        exact hpow_eq
      exact hζ_prim (b₂ - b₁) (by omega) (by omega) (mul_left_cancel₀ (pow_ne_zero b₁ hζ_ne) h1).symm
    · have h1 : ζ ^ b₂ * ζ ^ (b₁ - b₂) = ζ ^ b₂ * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hgt)]
        exact hpow_eq
      exact hζ_prim (b₁ - b₂) (by omega) (by omega) (mul_left_cancel₀ (pow_ne_zero b₂ hζ_ne) h1)
  by_contra hne_poly
  have hdiff_ne : P₁ - P₂ ≠ 0 := sub_ne_zero.mpr hne_poly
  have hndeg_lt : (P₁ - P₂).natDegree < ℓ := by
    by_contra hge
    have hge' : ℓ ≤ (P₁ - P₂).natDegree := Nat.le_of_not_lt hge
    have hlc_ne : (P₁ - P₂).coeff (P₁ - P₂).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hdiff_ne
    rcases eq_or_lt_of_le hge' with heq | hgt
    · rw [← heq, Polynomial.coeff_sub] at hlc_ne
      have hc1 : P₁.coeff ℓ = 1 := by rw [← hP₁_deg]; exact hP₁_monic.leadingCoeff
      have hc2 : P₂.coeff ℓ = 1 := by rw [← hP₂_deg]; exact hP₂_monic.leadingCoeff
      rw [hc1, hc2, sub_self] at hlc_ne
      exact hlc_ne rfl
    · rw [Polynomial.coeff_sub,
        Polynomial.coeff_eq_zero_of_natDegree_lt (hP₁_deg ▸ hgt),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hP₂_deg ▸ hgt), sub_self] at hlc_ne
      exact hlc_ne rfl
  let S_γ : Finset E := (Finset.range ℓ).image (fun b ↦ γ * ζ ^ b)
  have hS_card : S_γ.card = ℓ := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hS_sub : S_γ ⊆ (P₁ - P₂).roots.toFinset := by
    intro y hy
    obtain ⟨b, hb_mem, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hdiff_ne, Polynomial.IsRoot.def,
      Polynomial.eval_sub]
    have hev₁ : P₁.eval (γ * ζ ^ b) = 0 := by
      dsimp only [P₁]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        mul_pow, ← pow_mul, mul_comm b ℓ, pow_mul, hζ_pow, one_pow, mul_one, sub_self]
    have hev₂ : P₂.eval (γ * ζ ^ b) = 0 := by
      dsimp only [P₂]
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero hb_mem (by simp)
    rw [hev₁, hev₂, sub_self]
  have hcard_le : S_γ.card ≤ (P₁ - P₂).natDegree :=
    le_trans (Finset.card_le_card hS_sub)
      (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _))
  omega

/-- Sub-fibre partition of the root `Finset` `R_M` of a monic divisor `M ∣ X ^ (ℓ * s) - C (γ ^ ℓ)`
into `ℓ` blocks `R_M_b = {x ∈ R_M | x ^ s = γ * ζ ^ b}` (`0 ≤ b < ℓ`), each of cardinality `≤ s`. -/
private lemma fibre_block_partition {E : Type*} [Field E] [DecidableEq E]
    {p ℓ s : ℕ} [Fact p.Prime] [CharP E p]
    (hℓ_pos : 1 ≤ ℓ) (hs_pos : 1 ≤ s)
    {ζ₀ : ZMod p} (hζ₀_ne : ζ₀ ≠ 0) (hζ₀_pow : ζ₀ ^ ℓ = 1)
    (hζ₀_prim : ∀ d : ℕ, 1 ≤ d → d < ℓ → ζ₀ ^ d ≠ 1)
    {γ : E} (hγ_ne : γ ≠ 0)
    {R_M : Finset E} (hpow_R : ∀ x ∈ R_M, x ^ (ℓ * s) = γ ^ ℓ) :
    let ι : ZMod p →+* E := ZMod.castHom (dvd_refl p) E
    let ζ : E := ι ζ₀
    let n_M : ℕ → ℕ := fun b ↦ (R_M.filter (fun x ↦ x ^ s = γ * ζ ^ b)).card
    (∀ b ∈ Finset.range ℓ, n_M b ≤ s) ∧
    (∑ b ∈ Finset.range ℓ, n_M b = R_M.card) ∧
    (∀ t : ℕ,
      ∑ x ∈ R_M, x ^ (s * t) =
        γ ^ t * ι (∑ b ∈ Finset.range ℓ, (n_M b : ZMod p) * ζ₀ ^ (b * t))) := by
  intro ι ζ n_M
  have hι_inj : Function.Injective ι := ι.injective
  have hζ_ne : ζ ≠ 0 := fun h0 ↦ hζ₀_ne (hι_inj (by dsimp only [ζ] at h0; rw [map_zero]; exact h0))
  have hζ_pow : ζ ^ ℓ = 1 := by dsimp only [ζ]; rw [← map_pow, hζ₀_pow, map_one]
  have hζ_prim : ∀ d : ℕ, 1 ≤ d → d < ℓ → ζ ^ d ≠ 1 := by
    intro d hd1 hd_lt h1
    apply hζ₀_prim d hd1 hd_lt
    apply hι_inj
    rw [map_pow, map_one]
    exact h1
  let block : ℕ → Finset E := fun b ↦ R_M.filter (fun x ↦ x ^ s = γ * ζ ^ b)
  have hdisj : (↑(Finset.range ℓ) : Set ℕ).PairwiseDisjoint block := by
    intro b₁ hb₁ b₂ hb₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    have heq₁ : x ^ s = γ * ζ ^ b₁ := (Finset.mem_filter.mp hx₁).2
    have heq₂ : x ^ s = γ * ζ ^ b₂ := (Finset.mem_filter.mp hx₂).2
    have hpow_eq : ζ ^ b₁ = ζ ^ b₂ := mul_left_cancel₀ hγ_ne (heq₁.symm.trans heq₂)
    have hb₁_lt : b₁ < ℓ := Finset.mem_range.mp hb₁
    have hb₂_lt : b₂ < ℓ := Finset.mem_range.mp hb₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : ζ ^ b₁ * 1 = ζ ^ b₁ * ζ ^ (b₂ - b₁) := by
        rw [mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]; exact hpow_eq
      exact hζ_prim (b₂ - b₁) (by omega) (by omega) (mul_left_cancel₀ (pow_ne_zero b₁ hζ_ne) h1).symm
    · have h1 : ζ ^ b₂ * ζ ^ (b₁ - b₂) = ζ ^ b₂ * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hgt)]; exact hpow_eq
      exact hζ_prim (b₁ - b₂) (by omega) (by omega) (mul_left_cancel₀ (pow_ne_zero b₂ hζ_ne) h1)
  have hbiUnion : (Finset.range ℓ).biUnion block = R_M := by
    ext x
    rw [Finset.mem_biUnion]
    refine ⟨fun ⟨b, _, hxb⟩ ↦ (Finset.mem_filter.mp hxb).1, fun hxR ↦ ?_⟩
    have hxs_pow : (x ^ s) ^ ℓ = γ ^ ℓ := by
      rw [← pow_mul, mul_comm s ℓ]
      exact hpow_R x hxR
    have hfac := X_pow_sub_C_pow_eq_prod_zeta hℓ_pos hζ_ne hζ_pow hζ_prim hγ_ne
    have hev := congrArg (fun T : E[X] ↦ T.eval (x ^ s)) hfac
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      hxs_pow, sub_self, Polynomial.eval_prod] at hev
    obtain ⟨b, hb_mem, hfac0⟩ := Finset.prod_eq_zero_iff.mp hev.symm
    exact ⟨b, hb_mem, Finset.mem_filter.mpr ⟨hxR, sub_eq_zero.mp hfac0⟩⟩
  have hle_s : ∀ b ∈ Finset.range ℓ, n_M b ≤ s := by
    intro b _
    let P_s : E[X] := (X : E[X]) ^ s - Polynomial.C (γ * ζ ^ b)
    have hPs_monic : P_s.Monic := Polynomial.monic_X_pow_sub_C _ (by omega)
    have hPs_deg : P_s.natDegree = s := Polynomial.natDegree_X_pow_sub_C
    have hsub : block b ⊆ P_s.roots.toFinset := by
      intro x hxb
      have heq := (Finset.mem_filter.mp hxb).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hPs_monic.ne_zero, Polynomial.IsRoot.def]
      dsimp [P_s]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        heq, sub_self]
    calc n_M b
        ≤ P_s.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ P_s.roots.card := Multiset.toFinset_card_le _
      _ ≤ P_s.natDegree := Polynomial.card_roots' _
      _ = s := hPs_deg
  have hsum_card : ∑ b ∈ Finset.range ℓ, n_M b = R_M.card := by
    dsimp [n_M]
    rw [← Finset.card_biUnion hdisj, hbiUnion]
  refine ⟨hle_s, hsum_card, fun t ↦ ?_⟩
  rw [← hbiUnion, Finset.sum_biUnion hdisj, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ ↦ ?_)
  have hblock_sum :
      ∑ x ∈ block b, x ^ (s * t) = (n_M b : E) * (γ ^ t * ζ ^ (b * t)) := by
    trans ∑ _x ∈ block b, (γ ^ t * ζ ^ (b * t))
    · refine Finset.sum_congr rfl (fun x hxb ↦ ?_)
      have heq := (Finset.mem_filter.mp hxb).2
      rw [pow_mul, heq, mul_pow, ← pow_mul]
    · rw [Finset.sum_const, nsmul_eq_mul]
  rw [hblock_sum, map_mul, map_natCast, map_pow]
  change (n_M b : E) * (γ ^ t * ζ ^ (b * t)) = γ ^ t * ((n_M b : E) * ζ ^ (b * t))
  ring

/-! ## Part 4: `Lemma Q'_ℓ` GCD Degree Collapse & Fourier Inversion in `ZMod p` -/

/-- Orthogonality of powers of a primitive `ℓ`-th root of unity `ζ₀ : ZMod p`. -/
private lemma sum_zeta_pow_orthog {p ℓ b : ℕ} [Fact p.Prime]
    {ζ₀ : ZMod p} (hζ₀_pow : ζ₀ ^ ℓ = 1)
    (hζ₀_prim : ∀ d : ℕ, 1 ≤ d → d < ℓ → ζ₀ ^ d ≠ 1)
    (hb : b ∈ Finset.range ℓ) :
    ∑ t ∈ Finset.range ℓ, ζ₀ ^ (b * t) = if b = 0 then (ℓ : ZMod p) else 0 := by
  have hb_lt : b < ℓ := Finset.mem_range.mp hb
  by_cases hb0 : b = 0
  · subst hb0
    simp
  · simp only [hb0, ↓reduceIte]
    let z : ZMod p := ζ₀ ^ b
    have hz_ne1 : z ≠ 1 := hζ₀_prim b (by omega) hb_lt
    have hz_sub_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
    have hgeom : (z - 1) * ∑ t ∈ Finset.range ℓ, z ^ t = z ^ ℓ - 1 := by
      clear hb hb_lt hb0 hz_ne1 hz_sub_ne hζ₀_pow hζ₀_prim
      induction ℓ with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
        ring
    have hz_pow : z ^ ℓ = 1 := by dsimp [z]; rw [← pow_mul, mul_comm b ℓ, pow_mul, hζ₀_pow, one_pow]
    rw [hz_pow, sub_self] at hgeom
    have hsum0 : ∑ t ∈ Finset.range ℓ, z ^ t = 0 :=
      (mul_eq_zero.mp hgeom).resolve_left hz_sub_ne
    convert hsum0 using 2 with t _
    dsimp [z]
    rw [← pow_mul]

private lemma lemma_Q_prime_over_algClosed {F E : Type*} [Field F] [DecidableEq F]
    [Field E] [IsAlgClosed E] [Algebra F E]
    {p ℓ : ℕ} [Fact p.Prime] [CharP F p]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd3 : ¬ (3 ∣ e))
    (hp_gt : 4 * h < p)
    (hℓ_prime : Nat.Prime ℓ) (hℓ_odd : ℓ % 2 = 1)
    (hℓ_dvd_e : ℓ ∣ e) (hℓ_dvd_p1 : ℓ ∣ p - 1)
    (hneg3_nres : (-3 : ZMod p) ^ ((p - 1) / ℓ) ≠ 1)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) :
    ℓ ∣ h ∧ ℓ ∣ k := by
  classical
  have hrchar : ringChar F = p := ringChar.eq F p
  obtain ⟨B₁, Q₁, ρ, c₂, hB₁m, hB₁d, hQ₁m, hQ₁d, hρ_ne, _, hdvd_A, hdvd_B₁, hdvd_Q₁, hrev_S₁⟩ :=
    all_three_kummer_fibres_of_boundary_cubic hk_pos h2k_lt he_eq hf_eq hndvd3
      (Or.inr (by rw [hrchar]; exact hp_gt)) hAm hAd hBd hB0 hQd hident
  have hℓ_ge3 : 3 ≤ ℓ := by have := hℓ_prime.two_le; omega
  have : Fact ℓ.Prime := ⟨hℓ_prime⟩
  obtain ⟨s, hs_eq⟩ := hℓ_dvd_e
  have he_pos : 1 ≤ e := by omega
  have hs_pos : 1 ≤ s := by
    by_contra hs0
    have : s = 0 := by omega
    rw [this, mul_zero] at hs_eq
    omega
  have : CharP E p := (Algebra.charP_iff F E p).mp inferInstance
  let φ : F →+* E := algebraMap F E
  let ι : ZMod p →+* E := ZMod.castHom (dvd_refl p) E
  have hι_inj : Function.Injective ι := ι.injective
  have he_lt_p : e < p := by omega
  have he_E_ne : (e : E) ≠ 0 := by
    intro he0
    have hdvd : p ∣ e := (CharP.cast_eq_zero_iff E p e).mp he0
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hℓ_lt_p : ℓ < p := by
    have hle : ℓ ≤ p - 1 := Nat.le_of_dvd (by omega) hℓ_dvd_p1
    omega
  have hℓ_E_ne : (ℓ : E) ≠ 0 := by
    intro hℓ0
    have hdvd : p ∣ ℓ := (CharP.cast_eq_zero_iff E p ℓ).mp hℓ0
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have h3_ZMod_ne : (3 : ZMod p) ≠ 0 := by
    intro h30
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp (by simpa using h30)
    have hle := Nat.le_of_dvd (by decide) hdvd
    omega
  have h3_E_ne : (3 : E) ≠ 0 :=
    fun h0 ↦ h3_ZMod_ne (hι_inj (by rw [map_ofNat, map_zero]; exact h0))
  have hneg3_ZMod_ne : (-3 : ZMod p) ≠ 0 := neg_ne_zero.mpr h3_ZMod_ne
  -- Primitive `ℓ`-th root of unity `ζ₀ : ZMod p` from `(ZMod p)ˣ`
  have hdvd_units : ℓ ∣ Fintype.card (ZMod p)ˣ := by
    rw [Fintype.card_units, ZMod.card]
    exact hℓ_dvd_p1
  obtain ⟨u₀, hu₀_ord⟩ := exists_prime_orderOf_dvd_card ℓ hdvd_units
  let ζ₀ : ZMod p := (u₀ : ZMod p)
  let ζ : E := ι ζ₀
  have hζ₀_ne : ζ₀ ≠ 0 := Units.ne_zero u₀
  have hζ₀_pow : ζ₀ ^ ℓ = 1 := by
    dsimp only [ζ₀]
    rw [← Units.val_pow_eq_pow_val, ← hu₀_ord, pow_orderOf_eq_one, Units.val_one]
  have hζ₀_prim : ∀ d : ℕ, 1 ≤ d → d < ℓ → ζ₀ ^ d ≠ 1 := by
    intro d hd1 hd_lt h1
    have hu_d : u₀ ^ d = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h1)
    have hdvd_d : ℓ ∣ d := hu₀_ord ▸ orderOf_dvd_iff_pow_eq_one.mpr hu_d
    have hle := Nat.le_of_dvd (by omega) hdvd_d
    omega
  have hζ_ne : ζ ≠ 0 :=
    fun h0 ↦ hζ₀_ne (hι_inj (by dsimp only [ζ] at h0; rw [map_zero]; exact h0))
  have hζ_pow : ζ ^ ℓ = 1 := by dsimp only [ζ]; rw [← map_pow, hζ₀_pow, map_one]
  have hζ_prim : ∀ d : ℕ, 1 ≤ d → d < ℓ → ζ ^ d ≠ 1 := by
    intro d hd1 hd_lt h1
    exact hζ₀_prim d hd1 hd_lt (hι_inj (by dsimp only [ζ] at h1; rw [map_pow, map_one]; exact h1))
  -- Choose `r_Q, μ ∈ E` with `r_Q ^ ℓ = φ ρ` and `μ ^ ℓ = -3`
  let ρ_E : E := φ ρ
  have hρ_E_ne : ρ_E ≠ 0 :=
    fun h0 ↦ hρ_ne (φ.injective (by dsimp only [ρ_E] at h0; rw [map_zero]; exact h0))
  obtain ⟨r_Q, hr_Q_pow⟩ := IsAlgClosed.exists_pow_nat_eq ρ_E (by omega : 0 < ℓ)
  obtain ⟨μ, hμ_pow⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : E) (by omega : 0 < ℓ)
  have hr_Q_ne : r_Q ≠ 0 := fun h0 ↦ hρ_E_ne (by rw [← hr_Q_pow, h0, zero_pow (by omega)])
  have hμ_ne : μ ≠ 0 := fun h0 ↦
    (neg_ne_zero.mpr h3_E_ne) (by rw [← hμ_pow, h0, zero_pow (by omega)])
  -- Lift `A, B₁, Q₁` and the reversed `S₁` identity to `E[X]`
  let A_E : E[X] := A.map φ
  let B_E : E[X] := B₁.map φ
  let Q_E : E[X] := Q₁.map φ
  have hA_Em : A_E.Monic := hAm.map φ
  have hB_Em : B_E.Monic := hB₁m.map φ
  have hQ_Em : Q_E.Monic := hQ₁m.map φ
  have hA_Ed : A_E.natDegree = h := (hAm.natDegree_map φ).trans hAd
  have hB_Ed : B_E.natDegree = h := (hB₁m.natDegree_map φ).trans hB₁d
  have hQ_Ed : Q_E.natDegree = 2 * k := (hQ₁m.natDegree_map φ).trans hQ₁d
  have hdvd_AE : A_E ∣ ((X : E[X]) ^ e - Polynomial.C ((r_Q * μ) ^ ℓ)) := by
    obtain ⟨U_A, hUA⟩ := hdvd_A
    refine ⟨U_A.map φ, ?_⟩
    have hm := congrArg (Polynomial.map φ) hUA
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_mul] at hm
    have hrhs : φ (-3 * ρ) = (r_Q * μ) ^ ℓ := by
      rw [map_mul, map_neg, map_ofNat, mul_pow]
      change (-3 : E) * ρ_E = r_Q ^ ℓ * μ ^ ℓ
      rw [hr_Q_pow, hμ_pow]
      ring
    rw [hrhs] at hm
    exact hm
  have hdvd_BE : B_E ∣ ((X : E[X]) ^ e - Polynomial.C ((r_Q * μ⁻¹) ^ ℓ)) := by
    obtain ⟨U_B, hUB⟩ := hdvd_B₁
    refine ⟨U_B.map φ, ?_⟩
    have hm := congrArg (Polynomial.map φ) hUB
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_mul] at hm
    have hrhs : φ (-ρ * (3 : F)⁻¹) = (r_Q * μ⁻¹) ^ ℓ := by
      rw [map_mul, map_neg, map_inv₀, map_ofNat, mul_pow, inv_pow]
      change -ρ_E * (3 : E)⁻¹ = r_Q ^ ℓ * (μ ^ ℓ)⁻¹
      rw [hr_Q_pow, hμ_pow]
      have hneg3_inv : (-3 : E)⁻¹ = -((3 : E)⁻¹) := by
        apply inv_eq_of_mul_eq_one_right
        calc (-3 : E) * -((3 : E)⁻¹) = (3 : E) * (3 : E)⁻¹ := by ring
          _ = 1 := mul_inv_cancel₀ h3_E_ne
      rw [hneg3_inv]
      ring
    rw [hrhs] at hm
    exact hm
  have hdvd_QE : Q_E ∣ ((X : E[X]) ^ e - Polynomial.C (r_Q ^ ℓ)) := by
    obtain ⟨U_Q, hUQ⟩ := hdvd_Q₁
    refine ⟨U_Q.map φ, ?_⟩
    have hm := congrArg (Polynomial.map φ) hUQ
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_mul] at hm
    change (X : E[X]) ^ e - Polynomial.C ρ_E = Q_E * U_Q.map φ at hm
    rw [← hr_Q_pow] at hm
    exact hm
  have hrev_SE :
      - Polynomial.C (3 : E) * revSum h A_E * revSum (2 * k) Q_E * theta (revSum h B_E) +
        revSum h B_E * revSum (2 * k) Q_E * theta (revSum h A_E) +
        revSum h A_E * revSum h B_E * theta (revSum (2 * k) Q_E) =
          Polynomial.C (φ c₂) * X ^ e := by
    have hm := congrArg (Polynomial.map φ) hrev_S₁
    rw [Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      theta_map, theta_map, theta_map] at hm
    simp only [revSum_map, map_ofNat] at hm
    exact hm
  -- Apply `kummer_divisor_roots_and_newton_sum` to `A_E, B_E, Q_E`
  have hγA_ne : (r_Q * μ) ^ ℓ ≠ 0 := pow_ne_zero ℓ (mul_ne_zero hr_Q_ne hμ_ne)
  have hγB_ne : (r_Q * μ⁻¹) ^ ℓ ≠ 0 := pow_ne_zero ℓ (mul_ne_zero hr_Q_ne (inv_ne_zero hμ_ne))
  have hγQ_ne : r_Q ^ ℓ ≠ 0 := pow_ne_zero ℓ hr_Q_ne
  obtain ⟨hRA_card, _, hRA_pow, A_rev_comp, hA_rev_prod, hA_newton⟩ :=
    kummer_divisor_roots_and_newton_sum he_pos he_E_ne hγA_ne hA_Em hdvd_AE
  obtain ⟨hRB_card, _, hRB_pow, B_rev_comp, hB_rev_prod, hB_newton⟩ :=
    kummer_divisor_roots_and_newton_sum he_pos he_E_ne hγB_ne hB_Em hdvd_BE
  obtain ⟨hRQ_card, _, hRQ_pow, Q_rev_comp, hQ_rev_prod, hQ_newton⟩ :=
    kummer_divisor_roots_and_newton_sum he_pos he_E_ne hγQ_ne hQ_Em hdvd_QE
  rw [hA_Ed] at hRA_card hA_rev_prod hA_newton
  rw [hB_Ed] at hRB_card hB_rev_prod hB_newton
  rw [hQ_Ed] at hRQ_card hQ_rev_prod hQ_newton
  -- Derive Newton power-sum equation `(★)_m` for every `1 ≤ m < e`
  let R_A : Finset E := A_E.roots.toFinset
  let R_B : Finset E := B_E.roots.toFinset
  let R_Q : Finset E := Q_E.roots.toFinset
  have hstar : ∀ m : ℕ, 1 ≤ m → m < e →
      (3 : E) * (∑ x ∈ R_B, x ^ m) - (∑ x ∈ R_A, x ^ m) - (∑ x ∈ R_Q, x ^ m) = 0 := by
    intro m hm_pos hm_lt
    have hmul :
        ((- Polynomial.C (3 : E) * revSum h A_E * revSum (2 * k) Q_E * theta (revSum h B_E) +
          revSum h B_E * revSum (2 * k) Q_E * theta (revSum h A_E) +
          revSum h A_E * revSum h B_E * theta (revSum (2 * k) Q_E)) *
            (A_rev_comp * B_rev_comp * Q_rev_comp)).coeff m =
          (Polynomial.C (φ c₂) * X ^ e * (A_rev_comp * B_rev_comp * Q_rev_comp)).coeff m :=
      congrArg (fun T : E[X] ↦ (T * (A_rev_comp * B_rev_comp * Q_rev_comp)).coeff m) hrev_SE
    have hlhs_rearr :
        (- Polynomial.C (3 : E) * revSum h A_E * revSum (2 * k) Q_E * theta (revSum h B_E) +
          revSum h B_E * revSum (2 * k) Q_E * theta (revSum h A_E) +
          revSum h A_E * revSum h B_E * theta (revSum (2 * k) Q_E)) *
            (A_rev_comp * B_rev_comp * Q_rev_comp) =
          - Polynomial.C (3 : E) *
              ((revSum h A_E * A_rev_comp) * ((revSum (2 * k) Q_E * Q_rev_comp) *
                (theta (revSum h B_E) * B_rev_comp))) +
            (revSum h B_E * B_rev_comp) * ((revSum (2 * k) Q_E * Q_rev_comp) *
              (theta (revSum h A_E) * A_rev_comp)) +
            (revSum h A_E * A_rev_comp) * ((revSum h B_E * B_rev_comp) *
              (theta (revSum (2 * k) Q_E) * Q_rev_comp)) := by
      ring
    have hrhs_rearr :
        Polynomial.C (φ c₂) * X ^ e * (A_rev_comp * B_rev_comp * Q_rev_comp) =
          X ^ e * (Polynomial.C (φ c₂) * (A_rev_comp * B_rev_comp * Q_rev_comp)) := by
      ring
    rw [hlhs_rearr, hrhs_rearr, coeff_X_pow_mul_of_lt _ hm_lt,
      Polynomial.coeff_add, Polynomial.coeff_add, neg_mul, Polynomial.coeff_neg,
      Polynomial.coeff_C_mul, hA_rev_prod, hB_rev_prod, hQ_rev_prod,
      coeff_one_sub_C_X_pow_mul_of_lt _ _ hm_lt,
      coeff_one_sub_C_X_pow_mul_of_lt _ _ hm_lt,
      coeff_one_sub_C_X_pow_mul_of_lt _ _ hm_lt,
      coeff_one_sub_C_X_pow_mul_of_lt _ _ hm_lt,
      coeff_one_sub_C_X_pow_mul_of_lt _ _ hm_lt,
      coeff_one_sub_C_X_pow_mul_of_lt _ _ hm_lt,
      hB_newton m hm_pos hm_lt, hA_newton m hm_pos hm_lt, hQ_newton m hm_pos hm_lt] at hmul
    change -(3 * -∑ x ∈ R_B, x ^ m) + (-∑ x ∈ R_A, x ^ m) + (-∑ x ∈ R_Q, x ^ m) = 0 at hmul
    linear_combination hmul
  -- Partition `R_A`, `R_B`, `R_Q` into `ℓ` fibre blocks and evaluate `(★)_{s * t}` (`1 ≤ t < ℓ`)
  have hRA_pow' : ∀ x ∈ R_A, x ^ (ℓ * s) = (r_Q * μ) ^ ℓ := by rw [← hs_eq]; exact hRA_pow
  have hRB_pow' : ∀ x ∈ R_B, x ^ (ℓ * s) = (r_Q * μ⁻¹) ^ ℓ := by rw [← hs_eq]; exact hRB_pow
  have hRQ_pow' : ∀ x ∈ R_Q, x ^ (ℓ * s) = r_Q ^ ℓ := by rw [← hs_eq]; exact hRQ_pow
  obtain ⟨hnA_le, hnA_sum, hA_block⟩ :=
    fibre_block_partition (by omega) hs_pos hζ₀_ne hζ₀_pow hζ₀_prim
      (mul_ne_zero hr_Q_ne hμ_ne) hRA_pow'
  obtain ⟨_, _, hB_block⟩ :=
    fibre_block_partition (by omega) hs_pos hζ₀_ne hζ₀_pow hζ₀_prim
      (mul_ne_zero hr_Q_ne (inv_ne_zero hμ_ne)) hRB_pow'
  obtain ⟨hnQ_le, hnQ_sum, hQ_block⟩ :=
    fibre_block_partition (by omega) hs_pos hζ₀_ne hζ₀_pow hζ₀_prim hr_Q_ne hRQ_pow'
  let n_A : ℕ → ℕ := fun b ↦ (R_A.filter (fun x ↦ x ^ s = (r_Q * μ) * ζ ^ b)).card
  let n_B : ℕ → ℕ := fun b ↦ (R_B.filter (fun x ↦ x ^ s = (r_Q * μ⁻¹) * ζ ^ b)).card
  let n_Q : ℕ → ℕ := fun b ↦ (R_Q.filter (fun x ↦ x ^ s = r_Q * ζ ^ b)).card
  let I_hat : ℕ → ZMod p := fun t ↦ ∑ b ∈ Finset.range ℓ, (n_A b : ZMod p) * ζ₀ ^ (b * t)
  let J_hat : ℕ → ZMod p := fun t ↦ ∑ b ∈ Finset.range ℓ, (n_B b : ZMod p) * ζ₀ ^ (b * t)
  let L_hat : ℕ → ZMod p := fun t ↦ ∑ b ∈ Finset.range ℓ, (n_Q b : ZMod p) * ζ₀ ^ (b * t)
  let P_poly : ℕ → (ZMod p)[X] := fun t ↦
    Polynomial.C (J_hat t) * X ^ (ℓ - t) + Polynomial.C (I_hat t) * X ^ t + Polynomial.C (L_hat t)
  have hPt_eval0 : ∀ t : ℕ, 1 ≤ t → t < ℓ → ((P_poly t).map ι).eval μ = 0 := by
    intro t ht1 ht_lt
    have hm_pos : 1 ≤ s * t := Nat.mul_pos hs_pos ht1
    have hm_lt : s * t < e := by
      rw [hs_eq, mul_comm ℓ s]
      exact (Nat.mul_lt_mul_left hs_pos).mpr ht_lt
    have hst := hstar (s * t) hm_pos hm_lt
    rw [hB_block t, hA_block t, hQ_block t] at hst
    change (3 : E) * ((r_Q * μ⁻¹) ^ t * ι (J_hat t)) -
        (r_Q * μ) ^ t * ι (I_hat t) - r_Q ^ t * ι (L_hat t) = 0 at hst
    rw [mul_pow, mul_pow] at hst
    have hfactor :
        r_Q ^ t * ((3 : E) * (μ⁻¹) ^ t * ι (J_hat t) - μ ^ t * ι (I_hat t) - ι (L_hat t)) = 0 := by
      linear_combination hst
    have hinner := (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero t hr_Q_ne)
    have hμ_inv_t : (3 : E) * (μ⁻¹) ^ t = - (μ ^ (ℓ - t)) := by
      have hprod1 : (μ⁻¹) ^ t * μ ^ t = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hμ_ne, one_pow]
      have hpow_split : μ ^ (ℓ - t) * μ ^ t = -3 := by
        rw [← pow_add, show ℓ - t + t = ℓ by omega, hμ_pow]
      apply mul_right_cancel₀ (pow_ne_zero t hμ_ne)
      calc (3 : E) * (μ⁻¹) ^ t * μ ^ t
          = (3 : E) * ((μ⁻¹) ^ t * μ ^ t) := by ring
        _ = 3 := by rw [hprod1, mul_one]
        _ = - (-3 : E) := by ring
        _ = - (μ ^ (ℓ - t) * μ ^ t) := by rw [hpow_split]
        _ = - (μ ^ (ℓ - t)) * μ ^ t := by ring
    rw [hμ_inv_t] at hinner
    dsimp only [P_poly]
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination -hinner
  -- GCD degree collapse in `(ZMod p)[X]`: prove `P_poly t = 0` for every `1 ≤ t < ℓ`
  let Q_ℓ : (ZMod p)[X] := (X : (ZMod p)[X]) ^ ℓ + Polynomial.C 3
  have hQℓ_eval0 : (Q_ℓ.map ι).eval μ = 0 := by
    dsimp only [Q_ℓ]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      map_ofNat, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      hμ_pow]
    ring
  have hPt_zero : ∀ t : ℕ, 1 ≤ t → t < ℓ → P_poly t = 0 := by
    intro t ht1 ht_lt
    by_contra hPt_ne
    have hPt_deg_lt : (P_poly t).natDegree < ℓ := by
      dsimp only [P_poly]
      refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
        (max_lt (lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)) ?_)
      · refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) ?_
        exact lt_of_le_of_lt (Polynomial.natDegree_X_pow_le _) (by omega)
      · refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) ?_
        exact lt_of_le_of_lt (Polynomial.natDegree_X_pow_le _) ht_lt
      · rw [Polynomial.natDegree_C]; omega
    let G₀ : (ZMod p)[X] := EuclideanDomain.gcd (P_poly t) Q_ℓ
    have hG₀_dvd_Pt : G₀ ∣ P_poly t := EuclideanDomain.gcd_dvd_left _ _
    have hG₀_dvd_Qℓ : G₀ ∣ Q_ℓ := EuclideanDomain.gcd_dvd_right _ _
    have hG₀_ne : G₀ ≠ 0 := fun h0 ↦ hPt_ne (zero_dvd_iff.mp (h0 ▸ hG₀_dvd_Pt))
    let G : (ZMod p)[X] := Polynomial.C (G₀.leadingCoeff)⁻¹ * G₀
    have hlc_ne : G₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hG₀_ne
    have hGm : G.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact inv_mul_cancel₀ hlc_ne
    have hG₀_eq : G₀ = Polynomial.C G₀.leadingCoeff * G := by
      dsimp only [G]; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hlc_ne, map_one, one_mul]
    have hG_dvd_Pt : G ∣ P_poly t :=
      dvd_trans ⟨Polynomial.C G₀.leadingCoeff, hG₀_eq.trans (mul_comm _ _)⟩ hG₀_dvd_Pt
    have hG_dvd_Qℓ : G ∣ Q_ℓ :=
      dvd_trans ⟨Polynomial.C G₀.leadingCoeff, hG₀_eq.trans (mul_comm _ _)⟩ hG₀_dvd_Qℓ
    have hG_eval0 : (G.map ι).eval μ = 0 := by
      have hbez := EuclideanDomain.gcd_eq_gcd_ab (P_poly t) Q_ℓ
      have hG₀_eval0 : (G₀.map ι).eval μ = 0 := by
        change ((EuclideanDomain.gcd (P_poly t) Q_ℓ).map ι).eval μ = 0
        rw [hbez, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
          hPt_eval0 t ht1 ht_lt, hQℓ_eval0, zero_mul, zero_mul, add_zero]
      dsimp only [G]
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C,
        hG₀_eval0, mul_zero]
    let r : ℕ := G.natDegree
    have hr_lt : r < ℓ := lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hG_dvd_Pt hPt_ne) hPt_deg_lt
    have hr_pos : 1 ≤ r := by
      by_contra hr0
      have hr_eq0 : r = 0 := by omega
      have hG1 : G = 1 := Polynomial.eq_one_of_monic_natDegree_zero hGm hr_eq0
      rw [hG1, Polynomial.map_one, Polynomial.eval_one] at hG_eval0
      exact one_ne_zero hG_eval0
    -- Factor `G.map ι` among the roots `{μ * ζ ^ u | u ∈ range ℓ}` of `X ^ ℓ - C (μ ^ ℓ)` in `E[X]`
    have hGE_monic : (G.map ι).Monic := hGm.map ι
    have hGE_deg : (G.map ι).natDegree = r := hGm.natDegree_map ι
    have hGE_dvd : G.map ι ∣ ((X : E[X]) ^ ℓ - Polynomial.C (μ ^ ℓ)) := by
      obtain ⟨H_Q, hHQ⟩ := hG_dvd_Qℓ
      refine ⟨H_Q.map ι, ?_⟩
      have hm := congrArg (Polynomial.map ι) hHQ
      dsimp only [Q_ℓ] at hm
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.map_mul, map_ofNat] at hm
      rw [hμ_pow, map_neg, sub_neg_eq_add]
      exact hm
    have hsep_ℓ : ((X : E[X]) ^ ℓ - Polynomial.C (μ ^ ℓ)).Separable :=
      separable_X_pow_sub_C (by omega) hℓ_E_ne (pow_ne_zero ℓ hμ_ne)
    have hnup_G : (G.map ι).roots.Nodup := Polynomial.nodup_roots (hsep_ℓ.of_dvd hGE_dvd)
    have hsplits_G : (G.map ι).Splits := IsAlgClosed.splits (G.map ι)
    let T_G : Finset E := (G.map ι).roots.toFinset
    have hTG_card : T_G.card = r := by
      dsimp only [T_G]
      rw [Multiset.toFinset_card_of_nodup hnup_G, ← hsplits_G.natDegree_eq_card_roots, hGE_deg]
    have hGE_prod : G.map ι = ∏ x ∈ T_G, (X - Polynomial.C x) := by
      rw [Finset.prod_eq_multiset_prod]
      have hval : T_G.val = (G.map ι).roots := Multiset.dedup_eq_self.mpr hnup_G
      rw [hval]
      exact hsplits_G.eq_prod_roots_of_monic hGE_monic
    have hTG_form : ∀ x ∈ T_G, ∃ u : ℕ, x = μ * ζ ^ u := by
      intro x hx
      have hx_root : (G.map ι).eval x = 0 :=
        (Polynomial.mem_roots hGE_monic.ne_zero).mp (Multiset.mem_toFinset.mp hx)
      obtain ⟨H_E, hHE⟩ := hGE_dvd
      have hev := congrArg (fun T : E[X] ↦ T.eval x) hHE
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_mul, hx_root, zero_mul] at hev
      have hfac := X_pow_sub_C_pow_eq_prod_zeta (by omega) hζ_ne hζ_pow hζ_prim hμ_ne
      have hev' := congrArg (fun T : E[X] ↦ T.eval x) hfac
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        hev, Polynomial.eval_prod] at hev'
      obtain ⟨u, _, hu_eq⟩ := Finset.prod_eq_zero_iff.mp hev'.symm
      exact ⟨u, sub_eq_zero.mp hu_eq⟩
    let uFn : E → ℕ := fun x ↦ if hx : x ∈ T_G then Classical.choose (hTG_form x hx) else 0
    have huFn_spec : ∀ x ∈ T_G, x = μ * ζ ^ (uFn x) := by
      intro x hx
      dsimp only [uFn]
      simp only [hx, ↓reduceDIte]
      exact Classical.choose_spec (hTG_form x hx)
    have hev0 := congrArg (fun T : E[X] ↦ T.eval 0) hGE_prod
    have hGE_eval0 : (G.map ι).eval 0 = ι (G.coeff 0) := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self (G.map ι).natDegree),
        Finset.sum_eq_single 0]
      · rw [pow_zero, mul_one, Polynomial.coeff_map]
      · intro j _ hj0
        rw [zero_pow hj0, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ _)) hnot
    rw [hGE_eval0, Polynomial.eval_prod] at hev0
    have hprod_eval :
        (∏ x ∈ T_G, ((X : E[X]) - Polynomial.C x).eval 0) =
          (-1 : E) ^ r * μ ^ r * ι (ζ₀ ^ (∑ x ∈ T_G, uFn x)) := by
      have h1 : (∏ x ∈ T_G, ((X : E[X]) - Polynomial.C x).eval 0) =
          ∏ x ∈ T_G, (((-1 : E) * μ) * ζ ^ (uFn x)) :=
        Finset.prod_congr rfl (fun x hx ↦ by
          conv_lhs => rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, huFn_spec x hx]
          ring)
      rw [h1, Finset.prod_mul_distrib, Finset.prod_const, hTG_card, mul_pow,
        Finset.prod_pow_eq_pow_sum, map_pow]
    rw [hprod_eval] at hev0
    let zsum : ZMod p := ζ₀ ^ (∑ x ∈ T_G, uFn x)
    have hzsum_ne : zsum ≠ 0 := pow_ne_zero _ hζ₀_ne
    have hι_zsum_ne : ι zsum ≠ 0 := fun h0 ↦ hzsum_ne (hι_inj (by rw [map_zero]; exact h0))
    let w₀ : ZMod p := (-1 : ZMod p) ^ r * G.coeff 0 * zsum⁻¹
    have hμ_pow_r : μ ^ r = ι w₀ := by
      have hsign : (-1 : E) ^ r * (-1 : E) ^ r = 1 := by rw [← mul_pow]; norm_num
      dsimp only [w₀]
      rw [map_mul, map_mul, map_pow, map_neg, map_one, map_inv₀]
      change μ ^ r = (-1 : E) ^ r * ι (G.coeff 0) * (ι zsum)⁻¹
      rw [hev0]
      calc μ ^ r
          = ((-1 : E) ^ r * (-1 : E) ^ r) * μ ^ r * (ι zsum * (ι zsum)⁻¹) := by
              rw [hsign, one_mul, mul_inv_cancel₀ hι_zsum_ne, mul_one]
        _ = (-1 : E) ^ r * ((-1 : E) ^ r * μ ^ r * ι zsum) * (ι zsum)⁻¹ := by ring
    -- Invert `r` modulo `ℓ` via Fermat's Little Theorem `(r : ZMod ℓ) ^ (ℓ - 1) = 1`
    have hr_zmod_ne : (r : ZMod ℓ) ≠ 0 := by
      intro hr0
      have hdvd : ℓ ∣ r := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ r).mp hr0
      have hle := Nat.le_of_dvd hr_pos hdvd
      omega
    let a : ℕ := r ^ (ℓ - 2)
    have hra_mod : ℓ ∣ (r * a - 1) := by
      have hflt : (r : ZMod ℓ) ^ (ℓ - 1) = 1 := ZMod.pow_card_sub_one_eq_one hr_zmod_ne
      have hsplit : ℓ - 1 = 1 + (ℓ - 2) := by omega
      rw [hsplit, pow_add, pow_one] at hflt
      have hra_cast : ((r * a : ℕ) : ZMod ℓ) = 1 := by
        dsimp only [a]; rw [Nat.cast_mul, Nat.cast_pow]; exact hflt
      have hra_pos : 1 ≤ r * a := Nat.mul_pos hr_pos (Nat.pow_pos hr_pos)
      rw [← CharP.cast_eq_zero_iff (ZMod ℓ) ℓ (r * a - 1), Nat.cast_sub hra_pos,
        hra_cast, Nat.cast_one, sub_self]
    obtain ⟨b, hb_eq⟩ := hra_mod
    have hra_eq : r * a = ℓ * b + 1 := by
      have hra_pos : 1 ≤ r * a := Nat.mul_pos hr_pos (Nat.pow_pos hr_pos)
      omega
    have hμ_mem : ι (w₀ ^ a) = ι ((-3 : ZMod p) ^ b) * μ := by
      calc ι (w₀ ^ a)
          = (ι w₀) ^ a := map_pow ι w₀ a
        _ = (μ ^ r) ^ a := by rw [← hμ_pow_r]
        _ = μ ^ (r * a) := (pow_mul μ r a).symm
        _ = μ ^ (ℓ * b + 1) := by rw [hra_eq]
        _ = (μ ^ ℓ) ^ b * μ := by rw [pow_add, pow_mul, pow_one]
        _ = (-3 : E) ^ b * μ := by rw [hμ_pow]
        _ = ι ((-3 : ZMod p) ^ b) * μ := by rw [map_pow, map_neg, map_ofNat]
    let z₀ : ZMod p := w₀ ^ a * ((-3 : ZMod p) ^ b)⁻¹
    have hneg3_b_ne : (-3 : ZMod p) ^ b ≠ 0 := pow_ne_zero b hneg3_ZMod_ne
    have hι_neg3_b_ne : ι ((-3 : ZMod p) ^ b) ≠ 0 :=
      fun h0 ↦ hneg3_b_ne (hι_inj (by rw [map_zero]; exact h0))
    have hμ_eq_ι : μ = ι z₀ := by
      dsimp only [z₀]
      rw [map_mul, map_inv₀, hμ_mem]
      calc μ = μ * (ι ((-3 : ZMod p) ^ b) * (ι ((-3 : ZMod p) ^ b))⁻¹) := by
              rw [mul_inv_cancel₀ hι_neg3_b_ne, mul_one]
        _ = ι ((-3 : ZMod p) ^ b) * μ * (ι ((-3 : ZMod p) ^ b))⁻¹ := by ring
    have hz₀_pow_ℓ : z₀ ^ ℓ = -3 := by
      apply hι_inj
      rw [map_pow, ← hμ_eq_ι, hμ_pow, map_neg, map_ofNat]
    have hz₀_ne : z₀ ≠ 0 := fun h0 ↦ hneg3_ZMod_ne (by rw [← hz₀_pow_ℓ, h0, zero_pow (by omega)])
    have hp1_div : ℓ * ((p - 1) / ℓ) = p - 1 := Nat.mul_div_cancel' hℓ_dvd_p1
    have hres1 : (-3 : ZMod p) ^ ((p - 1) / ℓ) = 1 := by
      rw [← hz₀_pow_ℓ, ← pow_mul, hp1_div]
      exact ZMod.pow_card_sub_one_eq_one hz₀_ne
    exact hneg3_nres hres1
  -- Extract `I_hat t = 0` and `L_hat t = 0` for all `1 ≤ t < ℓ` (using `ℓ % 2 = 1`, so `t ≠ ℓ - t`)
  have hI_zero : ∀ t : ℕ, 1 ≤ t → t < ℓ → I_hat t = 0 := by
    intro t ht1 ht_lt
    have hc := congrArg (fun T : (ZMod p)[X] ↦ T.coeff t) (hPt_zero t ht1 ht_lt)
    dsimp only [P_poly] at hc
    have hne_lt : ¬ (t = ℓ - t) := by omega
    have hne_t0 : t ≠ 0 := by omega
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    simp only [hne_lt, hne_t0, ↓reduceIte, mul_zero, mul_one, zero_add, add_zero] at hc
    exact hc
  have hL_zero : ∀ t : ℕ, 1 ≤ t → t < ℓ → L_hat t = 0 := by
    intro t ht1 ht_lt
    have hc := congrArg (fun T : (ZMod p)[X] ↦ T.coeff 0) (hPt_zero t ht1 ht_lt)
    dsimp only [P_poly] at hc
    have hne_0lt : ¬ (0 = ℓ - t) := by omega
    have hne_0t : ¬ (0 = t) := by omega
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    simp only [hne_0lt, hne_0t, ↓reduceIte, mul_zero, zero_add] at hc
    exact hc
  -- Fourier inversion over `Finset.range ℓ` gives `h = ℓ * n_A 0` and `2 * k = ℓ * n_Q 0`
  have h0_mem : 0 ∈ Finset.range ℓ := Finset.mem_range.mpr (by omega)
  have hsum_I_lhs : ∑ t ∈ Finset.range ℓ, I_hat t = (h : ZMod p) := by
    rw [← Finset.add_sum_erase _ _ h0_mem]
    have herase0 : ∑ t ∈ (Finset.range ℓ).erase 0, I_hat t = 0 := by
      refine Finset.sum_eq_zero (fun t ht ↦ ?_)
      have ht_ne0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
      have ht_lt : t < ℓ := Finset.mem_range.mp (Finset.mem_erase.mp ht).2
      exact hI_zero t (by omega) ht_lt
    have hI0 : I_hat 0 = (h : ZMod p) := by
      have hsum_A : ∑ b ∈ Finset.range ℓ, n_A b = h := hnA_sum.trans hRA_card
      dsimp only [I_hat]
      simp only [mul_zero, pow_zero, mul_one, ← Nat.cast_sum]
      rw [hsum_A]
    rw [herase0, add_zero, hI0]
  have hsum_I_rhs : ∑ t ∈ Finset.range ℓ, I_hat t = ((ℓ * n_A 0 : ℕ) : ZMod p) := by
    dsimp only [I_hat]
    rw [Finset.sum_comm]
    trans ∑ b ∈ Finset.range ℓ, (n_A b : ZMod p) * (if b = 0 then (ℓ : ZMod p) else 0)
    · refine Finset.sum_congr rfl (fun b hb ↦ ?_)
      rw [← Finset.mul_sum, sum_zeta_pow_orthog hζ₀_pow hζ₀_prim hb]
    · rw [Finset.sum_eq_single 0]
      · simp [mul_comm]
      · intro b _ hb0; simp [hb0]
      · intro hnot; exact absurd h0_mem hnot
  have hnA0_le_s : n_A 0 ≤ s := hnA_le 0 h0_mem
  have hℓnA0_lt_p : ℓ * n_A 0 < p := by
    have hle : ℓ * n_A 0 ≤ e := hs_eq ▸ Nat.mul_le_mul_left ℓ hnA0_le_s
    omega
  have hh_eq : h = ℓ * n_A 0 :=
    nat_eq_of_cast_zmod_eq (by omega) hℓnA0_lt_p (hsum_I_lhs.symm.trans hsum_I_rhs)
  have hsum_L_lhs : ∑ t ∈ Finset.range ℓ, L_hat t = ((2 * k : ℕ) : ZMod p) := by
    rw [← Finset.add_sum_erase _ _ h0_mem]
    have herase0 : ∑ t ∈ (Finset.range ℓ).erase 0, L_hat t = 0 := by
      refine Finset.sum_eq_zero (fun t ht ↦ ?_)
      have ht_ne0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
      have ht_lt : t < ℓ := Finset.mem_range.mp (Finset.mem_erase.mp ht).2
      exact hL_zero t (by omega) ht_lt
    have hL0 : L_hat 0 = ((2 * k : ℕ) : ZMod p) := by
      have hsum_Q : ∑ b ∈ Finset.range ℓ, n_Q b = 2 * k := hnQ_sum.trans hRQ_card
      dsimp only [L_hat]
      simp only [mul_zero, pow_zero, mul_one, ← Nat.cast_sum]
      rw [hsum_Q]
    rw [herase0, add_zero, hL0]
  have hsum_L_rhs : ∑ t ∈ Finset.range ℓ, L_hat t = ((ℓ * n_Q 0 : ℕ) : ZMod p) := by
    dsimp only [L_hat]
    rw [Finset.sum_comm]
    trans ∑ b ∈ Finset.range ℓ, (n_Q b : ZMod p) * (if b = 0 then (ℓ : ZMod p) else 0)
    · refine Finset.sum_congr rfl (fun b hb ↦ ?_)
      rw [← Finset.mul_sum, sum_zeta_pow_orthog hζ₀_pow hζ₀_prim hb]
    · rw [Finset.sum_eq_single 0]
      · simp [mul_comm]
      · intro b _ hb0; simp [hb0]
      · intro hnot; exact absurd h0_mem hnot
  have hnQ0_le_s : n_Q 0 ≤ s := hnQ_le 0 h0_mem
  have hℓnQ0_lt_p : ℓ * n_Q 0 < p := by
    have hle : ℓ * n_Q 0 ≤ e := hs_eq ▸ Nat.mul_le_mul_left ℓ hnQ0_le_s
    omega
  have h2k_eq : 2 * k = ℓ * n_Q 0 :=
    nat_eq_of_cast_zmod_eq (by omega) hℓnQ0_lt_p (hsum_L_lhs.symm.trans hsum_L_rhs)
  have hdvd_h : ℓ ∣ h := ⟨n_A 0, hh_eq⟩
  have hdvd_2k : ℓ ∣ 2 * k := ⟨n_Q 0, h2k_eq⟩
  have hnot_dvd_2 : ¬ (ℓ ∣ 2) := by
    intro hd2
    have hle := Nat.le_of_dvd (by decide) hd2
    omega
  have hdvd_k : ℓ ∣ k := ((Nat.Prime.dvd_mul hℓ_prime).mp hdvd_2k).resolve_left hnot_dvd_2
  exact ⟨hdvd_h, hdvd_k⟩

/-- **Result 19 `Lemma Q'_ℓ` — Prime-Divisibility Theorem (`M-0970`):**
Over any field `F` of prime characteristic `p > 4 * h`, at the Wronskian boundary
`e = 2 * h + 2 * k`, `f = 2 * h - 2 * k` (`1 ≤ k`, `2 * k + 1 ≤ h`, `¬ (3 ∣ e)`), if an odd prime
`ℓ` divides both `e` and `p - 1` and `-3` is not an `ℓ`-th power in `ZMod p`
(`(-3 : ZMod p) ^ ((p - 1) / ℓ) ≠ 1`), then any solution `(A, B, Q)` to
`A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q` forces **`ℓ ∣ h ∧ ℓ ∣ k`**. -/
theorem lemma_Q_prime_divisibility {F : Type*} [Field F] [DecidableEq F]
    {p ℓ : ℕ} [Fact p.Prime] [CharP F p]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd3 : ¬ (3 ∣ e))
    (hp_gt : 4 * h < p)
    (hℓ_prime : Nat.Prime ℓ) (hℓ_odd : ℓ % 2 = 1)
    (hℓ_dvd_e : ℓ ∣ e) (hℓ_dvd_p1 : ℓ ∣ p - 1)
    (hneg3_nres : (-3 : ZMod p) ^ ((p - 1) / ℓ) ≠ 1)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) :
    ℓ ∣ h ∧ ℓ ∣ k :=
  lemma_Q_prime_over_algClosed (E := AlgebraicClosure F)
    hk_pos h2k_lt he_eq hf_eq hndvd3 hp_gt hℓ_prime hℓ_odd hℓ_dvd_e hℓ_dvd_p1 hneg3_nres
    hAm hAd hBd hB0 hQd hident

/-- **Result 19 `Lemma Q'_ℓ` — Cubic Obstruction (`M-0970`):**
Over any field `F` of prime characteristic `p > 4 * h`, at the Wronskian boundary
`e = 2 * h + 2 * k`, `f = 2 * h - 2 * k` (`1 ≤ k`, `2 * k + 1 ≤ h`, `¬ (3 ∣ e)`), if an odd prime
`ℓ` satisfies `ℓ ∣ e`, `ℓ ∣ p - 1`, `(-3 : ZMod p) ^ ((p - 1) / ℓ) ≠ 1`, and
`¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ k)`, then NO polynomials `(A, B, Q)` can satisfy
`A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q`! -/
theorem lemma_Q_prime_cubic_obstruction {F : Type*} [Field F] [DecidableEq F]
    {p ℓ : ℕ} [Fact p.Prime] [CharP F p]
    {A B Q : F[X]} {h k e f : ℕ}
    (hk_pos : 1 ≤ k) (h2k_lt : 2 * k + 1 ≤ h)
    (he_eq : e = 2 * h + 2 * k) (hf_eq : f = 2 * h - 2 * k)
    (hndvd3 : ¬ (3 ∣ e))
    (hp_gt : 4 * h < p)
    (hℓ_prime : Nat.Prime ℓ) (hℓ_odd : ℓ % 2 = 1)
    (hℓ_dvd_e : ℓ ∣ e) (hℓ_dvd_p1 : ℓ ∣ p - 1)
    (hneg3_nres : (-3 : ZMod p) ^ ((p - 1) / ℓ) ≠ 1)
    (hnot_both : ¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ k))
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hQd : Q ≠ 0 → Q.natDegree + f ≤ 2 * h)
    (hident : A ^ 3 + X ^ e * B ^ 3 = (X ^ (e + f) * A + B) * Q) :
    False := by
  obtain ⟨hdvd_h, hdvd_k⟩ :=
    lemma_Q_prime_divisibility hk_pos h2k_lt he_eq hf_eq hndvd3 hp_gt
      hℓ_prime hℓ_odd hℓ_dvd_e hℓ_dvd_p1 hneg3_nres hAm hAd hBd hB0 hQd hident
  rcases hnot_both with hnh | hnk
  · exact hnh hdvd_h
  · exact hnk hdvd_k

/-! ## Part 5: All-Dyadic `5 ≤ r ≤ 31` `Lemma Q'_ℓ` Vanishing, Composable Reduction, & Corollaries -/

private lemma not_dvd_three_pow_two : ∀ t : ℕ, ¬ (3 ∣ 2 ^ t)
  | 0 => by decide
  | t + 1 => fun hdvd ↦ by
    have hpr : Nat.Prime 3 := by decide
    rcases hpr.dvd_mul.mp (by rw [pow_succ'] at hdvd; exact hdvd) with h32 | h3t
    · revert h32; decide
    · exact not_dvd_three_pow_two t h3t

private lemma not_dvd_three_sub_pow_two {t δ : ℕ} (hlt : 2 ^ t < 3 * δ) :
    ¬ (3 ∣ (3 * δ - 2 ^ t)) := by
  intro hdvd
  have hsub : 3 ∣ 3 * δ - (3 * δ - 2 ^ t) := Nat.dvd_sub (dvd_mul_right 3 δ) hdvd
  rw [Nat.sub_sub_self (le_of_lt hlt)] at hsub
  exact not_dvd_three_pow_two t hsub

private lemma not_seven_dvd_five_mul_pow_two : ∀ t : ℕ, ¬ (7 ∣ 5 * 2 ^ t)
  | 0 => by decide
  | t + 1 => fun hdvd ↦ by
    have hpr : Nat.Prime 7 := by decide
    have hdvd' : 7 ∣ 2 * (5 * 2 ^ t) := by
      have heq : 5 * 2 ^ (t + 1) = 2 * (5 * 2 ^ t) := by rw [pow_succ]; ring
      rwa [← heq]
    rcases hpr.dvd_mul.mp hdvd' with h72 | h7t
    · revert h72; decide
    · exact not_seven_dvd_five_mul_pow_two t h7t

/-- **All-Dyadic `Lemma Q'_ℓ` Inner-Band Vanishing (`m = 5 * q + δ` at `4 * h = 3 * q - δ`):**
Across every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), at `4 * h = 3 * q - δ` (`h ≤ δ`,
`q + h < 3 * δ`), whenever some `ℓ ∈ {7, 11, 31, 151, 331}` divides `3 * δ - q` and satisfies
`¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ (h - 2 * (q - δ)))`, NO degree-`≤ 2 ^ (r - 1)` polynomial agrees with
`C a * X ^ (5 * q + δ) + R` on `(5 * q + δ) - h` points of `D`, and `NativeListBound = 0`. -/
theorem ambient_and_native_vanishing_q_prime_boundary_inner
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hqprime : ∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * δ - 2 ^ (r - 3)) ∧
        (¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ (h - 2 * (2 ^ (r - 3) - δ)))))
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
    · have hh_ne_2qd : h ≠ 2 * (2 ^ (r - 3) - δ) := by
        intro heq
        exact not_seven_dvd_five_mul_pow_two (r - 3) ⟨δ, by omega⟩
      have h3h_ne_e : 3 * h ≠ 3 * δ - 2 ^ (r - 3) := by
        intro heq
        exact not_dvd_three_pow_two (r - 3) ⟨δ - h, by rw [Nat.mul_sub]; omega⟩
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
        · obtain ⟨ℓ, hℓ_mem, hℓ_dvd_e, hnot_both⟩ := hqprime
          obtain ⟨hℓ_prime, hℓ_odd, hℓ_dvd_p1, hneg3_nres⟩ :=
            mersenne31_q_prime_conditions hℓ_mem
          let k : ℕ := h' - 2 * (q - δ)
          exact lemma_Q_prime_cubic_obstruction (p := 2 ^ 31 - 1) (ℓ := ℓ) (k := k)
            (by omega : 1 ≤ k)
            (by omega : 2 * k + 1 ≤ h')
            (by omega : 3 * δ - q = 2 * h' + 2 * k)
            (by omega : 4 * (q - δ) = 2 * h' - 2 * k)
            hndvd
            (by omega : 4 * h' < 2 ^ 31 - 1)
            hℓ_prime hℓ_odd hℓ_dvd_e hℓ_dvd_p1 hneg3_nres hnot_both
            hAm hAd hBd hB0 hQd hident
      refine ⟨hno_amb, fun L hL ↦ ?_⟩
      have hL_empty : L = ∅ := by
        by_contra hne
        obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
        exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
      rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- **Mirror Duality (`m = 7 * q - δ`) at `4 * h = 3 * q - δ` (`Lemma Q'_ℓ`):**
Extends `ambient_and_native_vanishing_q_prime_boundary_inner` to `m = 7 * 2 ^ (r - 3) - δ` via
Mersenne circle Frobenius inversion `x ^ p = x⁻¹` (`p = 2 ^ 31 - 1`). -/
theorem ambient_and_native_vanishing_q_prime_boundary_mirror
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hqprime : ∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * δ - 2 ^ (r - 3)) ∧
        (¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ (h - 2 * (2 ^ (r - 3) - δ)))))
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
  let p : ℕ := 2 ^ 31 - 1
  let q : ℕ := 2 ^ (r - 3)
  let K : ℕ := 2 ^ (r - 1)
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
  have hinner := ambient_and_native_vanishing_q_prime_boundary_inner hF hr_lo hr_hi
    hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry hqprime hap_ne (conjRev R) (hconjRev_deg R)
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

/-- Parameter stratum for Wronskian-boundary Kummer prime-divisibility vanishing (`Lemma Q'_ℓ`,
`M-0970`): at `4 * u + 5 * δ = 15 * 2 ^ (r - 3)` (`u < 2 * (2 ^ (r - 3) + δ)`), some odd prime
`ℓ ∈ {7, 11, 31, 151, 331}` divides `e = 3 * δ - 2 ^ (r - 3)` while failing to divide both
`h = u + δ - 3 * 2 ^ (r - 3)` and `k = u + 3 * δ - 5 * 2 ^ (r - 3)`. -/
def InSingleQPrimeBoundaryStratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u < 2 * (2 ^ (r - 3) + δ) ∧
    4 * u + 5 * δ = 15 * 2 ^ (r - 3) ∧
    (∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * δ - 2 ^ (r - 3)) ∧
        (¬ (ℓ ∣ (u + δ - 3 * 2 ^ (r - 3))) ∨
          ¬ (ℓ ∣ (u + 3 * δ - 5 * 2 ^ (r - 3)))))

/-- All-dyadic `Lemma Q'_ℓ` complement-vanishing proposition across `5 ≤ r ≤ 31`. -/
def SingleMonomialQPrimeBoundaryVanishing.{u} : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 5 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ δ : ℕ, 1 ≤ δ → δ < 2 ^ (r - 3) →
        ∀ m : ℕ, (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) →
          ∀ (γ : F) (U : Finset F),
            U.card < 2 * (2 ^ (r - 3) + δ) →
            4 * U.card + 5 * δ = 15 * 2 ^ (r - 3) →
            (∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
              ℓ ∣ (3 * δ - 2 ^ (r - 3)) ∧
                (¬ (ℓ ∣ (U.card + δ - 3 * 2 ^ (r - 3))) ∨
                  ¬ (ℓ ∣ (U.card + 3 * δ - 5 * 2 ^ (r - 3))))) →
            ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U

/-- **Main `Lemma Q'_ℓ` Boundary Vanishing Theorem (`SingleMonomialQPrimeBoundaryVanishing`):**
Proves `¬ IsValidCWComplement D r (X ^ m) γ U` across all universes `u` and all dyadic `5 ≤ r ≤ 31`
on every Wronskian-boundary cell `4 * U.card + 5 * δ = 15 * 2 ^ (r - 3)` (`U.card < 2 * (q + δ)`)
where some `ℓ ∈ {7, 11, 31, 151, 331}` divides `3 * δ - 2 ^ (r - 3)` and fails to divide both `h`
and `k`. -/
theorem singleMonomialQPrimeBoundaryVanishing.{u} :
    SingleMonomialQPrimeBoundaryVanishing.{u} := by
  intro F _ _ hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry_u hqprime hvalid
  have hr4 : 4 ≤ r := by omega
  obtain ⟨_, _, hr0⟩ := dyadic_octant_identities hr4
  obtain ⟨hUD, hu_le_3q, _, _, hB_deg, _, _⟩ := hvalid
  let S : Finset F := D \ U
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
  let h : ℕ := U.card + δ - 3 * 2 ^ (r - 3)
  have hh_le : h ≤ δ := by omega
  have hqh : 2 ^ (r - 3) + h < 3 * δ := by omega
  have hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ := by omega
  have hk_eq : h - 2 * (2 ^ (r - 3) - δ) = U.card + 3 * δ - 5 * 2 ^ (r - 3) := by omega
  have hqprime' : ∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * δ - 2 ^ (r - 3)) ∧
        (¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ (h - 2 * (2 ^ (r - 3) - δ)))) := by
    obtain ⟨ℓ, hℓ_mem, hℓ_dvd, hnot⟩ := hqprime
    exact ⟨ℓ, hℓ_mem, hℓ_dvd, by rwa [hk_eq]⟩
  have hS_eq : (5 * 2 ^ (r - 3) + δ) - h = S.card := by omega
  rcases hm_eq with rfl | rfl
  · exact (ambient_and_native_vanishing_q_prime_boundary_inner hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry hqprime' one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · exact (ambient_and_native_vanishing_q_prime_boundary_mirror hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh hbdry hqprime' one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩

/-- Narrowed single-monomial residual complement bound after eliminating ALL `Theorem W`
(`M-0934` / `M-0958`), full `Theorem CW*` (`M-0964` / `M-0965`), AND `Lemma Q'_ℓ` (`M-0970`)
Wronskian-boundary strata. -/
def SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ m : ℕ, 5 * 2 ^ (r - 3) ≤ m → m ≤ 7 * 2 ^ (r - 3) → ∀ γ : F,
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r ((X : F[X]) ^ m) γ U ∧
            ¬ InSingleWronskianStratum r m U.card ∧
            ¬ InSingleFullFrobeniusBoundaryStratum r m U.card ∧
            ¬ InSingleQPrimeBoundaryStratum r m U.card) →
          𝒰.card ≤ K * 2 ^ r

/-- `SingleMonomialResidualAfterCWStarAndQPrimeBound K` implies `SingleMonomialNonFrobeniusCWBound K`. -/
theorem singleMonomialNonFrobeniusCWBound_of_after_qPrime.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} K) :
    SingleMonomialNonFrobeniusCWBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 h𝒰
  refine hRem F hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
  obtain ⟨hvalid, hnotW, hnotCWStar⟩ := h𝒰 U hUm
  refine ⟨hvalid, hnotW, hnotCWStar, ?_⟩
  rintro ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hbdry, hqprime⟩
  exact singleMonomialQPrimeBoundaryVanishing F hF r hr5 hr_hi D hD_card hD_pow
    δ hδ1 hδ_lt m hm_eq γ U hu_lt hbdry hqprime hvalid

/-- Reduces `CanonicalInteriorCWBound.{u} K` to `SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} K`
and `MultiMonomialCanonicalCWBound.{u} K`. -/
theorem canonicalInteriorCWBound_of_cwStar_qPrime_and_multi_sublemmas.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    CanonicalInteriorCWBound.{u} K :=
  canonicalInteriorCWBound_of_nonFrobenius_and_multi_sublemmas
    (singleMonomialNonFrobeniusCWBound_of_after_qPrime hRem)
    hMulti

/-- **Master `CW*` + `Lemma Q'_ℓ` Reduced Theorem (`MCAChallenge.InteriorThree K`):**
Reduces `MCAChallenge.InteriorThree.{u} K` (`1 ≤ K ≤ 2 ^ 20`) across all dyadic `4 ≤ r ≤ 31` directly
to `SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} K` and `MultiMonomialCanonicalCWBound.{u} K`. -/
theorem interiorThree_of_cwStar_qPrime_and_multi_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hRem : SingleMonomialResidualAfterCWStarAndQPrimeBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_nonFrobenius_and_multi_sublemmas
    hK_pos
    hK_cap
    (singleMonomialNonFrobeniusCWBound_of_after_qPrime hRem)
    hMulti

/-- **Unified `NativeListBound = 0` Corollary on All `Lemma Q'_ℓ` Boundary Cells:**
For every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), whenever `4 * h = 3 * q - δ`, `h ≤ δ`,
`q + h < 3 * δ`, and some `ℓ ∈ {7, 11, 31, 151, 331}` divides `3 * δ - q` without dividing both `h`
and `h - 2 * (q - δ)`, both `m = 5 * q + δ` and `m = 7 * q - δ` satisfy
`NativeListBound D (2 ^ (r - 1)) ((5 * q + δ) - h) (C a * X ^ m + R) 0`. -/
theorem nativeListBound_zero_q_prime_boundary {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h m : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hbdry : 4 * h = 3 * 2 ^ (r - 3) - δ)
    (hqprime : ∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * δ - 2 ^ (r - 3)) ∧
        (¬ (ℓ ∣ h) ∨ ¬ (ℓ ∣ (h - 2 * (2 ^ (r - 3) - δ)))))
    (hm_eq : m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        (5 * 2 ^ (r - 3) + δ) - h ≤
          (D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) ((5 * 2 ^ (r - 3) + δ) - h)
      (Polynomial.C a * X ^ m + R) 0 := by
  rcases hm_eq with rfl | rfl
  · exact ambient_and_native_vanishing_q_prime_boundary_inner hF hr_lo hr_hi
      hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry hqprime ha R hR
  · exact ambient_and_native_vanishing_q_prime_boundary_mirror hF hr_lo hr_hi
      hD_card hD_pow hδ_pos hδ_lt hh_le hqh hbdry hqprime ha R hR

/-- **Non-Frobenius `n = 1024` (`r = 10`) Boundary Cell `(δ, h) = (108, 69)` (`u = 345`, `k = 29`,
`e = 196`, `ℓ = 7`, `-1 ∉ ⟨p mod 196⟩` so `Theorem CW*` fails!):**
Proves `NativeListBound D 512 679 (C a * X ^ m + R) 0` for `m ∈ {748, 788}`. -/
theorem nativeListBound_zero_r10_nonfrobenius_748_788 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 1024) (hD_pow : ∀ x ∈ D, x ^ 1024 = 1)
    {m : ℕ} (hm : m = 748 ∨ m = 788)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 512) :
    MCAChallenge.NativeListBound D 512 679 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (10 - 3) + 108 ∨ m = 7 * 2 ^ (10 - 3) - 108 := by omega
  have hqprime : ∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * 108 - 2 ^ (10 - 3)) ∧
        (¬ (ℓ ∣ 69) ∨ ¬ (ℓ ∣ (69 - 2 * (2 ^ (10 - 3) - 108)))) :=
    ⟨7, by decide, ⟨28, by decide⟩, Or.inl (by decide)⟩
  exact (nativeListBound_zero_q_prime_boundary hF (r := 10) (δ := 108) (h := 69) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hqprime hm' ha R (by simpa using hR)).2

/-- **Non-Frobenius `n = 2048` (`r = 11`) Boundary Cell `(δ, h) = (188, 145)` (`u = 725`, `k = 9`,
`e = 308`, `ℓ = 7`, `-1 ∉ ⟨p mod 308⟩` so `Theorem CW*` fails!):**
Proves `NativeListBound D 1024 1323 (C a * X ^ m + R) 0` for `m ∈ {1468, 1604}`. -/
theorem nativeListBound_zero_r11_nonfrobenius_1468_1604 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 2048) (hD_pow : ∀ x ∈ D, x ^ 2048 = 1)
    {m : ℕ} (hm : m = 1468 ∨ m = 1604)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 1024) :
    MCAChallenge.NativeListBound D 1024 1323 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (11 - 3) + 188 ∨ m = 7 * 2 ^ (11 - 3) - 188 := by omega
  have hqprime : ∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * 188 - 2 ^ (11 - 3)) ∧
        (¬ (ℓ ∣ 145) ∨ ¬ (ℓ ∣ (145 - 2 * (2 ^ (11 - 3) - 188)))) :=
    ⟨7, by decide, ⟨44, by decide⟩, Or.inl (by decide)⟩
  exact (nativeListBound_zero_q_prime_boundary hF (r := 11) (δ := 188) (h := 145) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hqprime hm' ha R (by simpa using hR)).2

/-- **Non-Frobenius `n = 2048` (`r = 11`) Boundary Cell `(δ, h) = (216, 138)` (`u = 690`, `k = 58`,
`e = 392`, `ℓ = 7`, `-1 ∉ ⟨p mod 392⟩` so `Theorem CW*` fails!):**
Proves `NativeListBound D 1024 1358 (C a * X ^ m + R) 0` for `m ∈ {1496, 1576}`. -/
theorem nativeListBound_zero_r11_nonfrobenius_1496_1576 {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {D : Finset F} (hD_card : D.card = 2048) (hD_pow : ∀ x ∈ D, x ^ 2048 = 1)
    {m : ℕ} (hm : m = 1496 ∨ m = 1576)
    {a : F} (ha : a ≠ 0) (R : F[X]) (hR : R.natDegree ≤ 1024) :
    MCAChallenge.NativeListBound D 1024 1358 (Polynomial.C a * X ^ m + R) 0 := by
  have hm' : m = 5 * 2 ^ (11 - 3) + 216 ∨ m = 7 * 2 ^ (11 - 3) - 216 := by omega
  have hqprime : ∃ ℓ ∈ ({7, 11, 31, 151, 331} : Finset ℕ),
      ℓ ∣ (3 * 216 - 2 ^ (11 - 3)) ∧
        (¬ (ℓ ∣ 138) ∨ ¬ (ℓ ∣ (138 - 2 * (2 ^ (11 - 3) - 216)))) :=
    ⟨7, by decide, ⟨56, by decide⟩, Or.inl (by decide)⟩
  exact (nativeListBound_zero_q_prime_boundary hF (r := 11) (δ := 216) (h := 138) (m := m)
    (by decide) (by decide) (by simpa using hD_card) (by simpa using hD_pow)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hqprime hm' ha R (by simpa using hR)).2

end InteriorThreeKummerPrimeDivisibility
