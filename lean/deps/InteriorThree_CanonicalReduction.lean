import MCAChallenge

/-!
# Standalone Canonical Weierstrass–`CW*` Reduction & Named Sub-Lemma Suite for `MCAChallenge.InteriorThree`

This standalone module (`import MCAChallenge` only) establishes at **every dyadic blocklength**
`n = 2 ^ r` (`4 ≤ r ≤ 31`) the algebraic infrastructure, exterior/wraparound elimination theorems,
canonical Weierstrass–`CW*` reduction, and exhaustive named sub-lemma decomposition for
`MCAChallenge.InteriorThree K`:

1. **Dyadic Root-of-Unity Subgroup & Monic Factorization (`dyadicSubgroup_properties` /
   `dyadic_roots_eq_univ_and_prod`):**
   Over any field `F`, any `D : Finset F` with `D.card = 2 ^ r` and `∀ x ∈ D, x ^ (2 ^ r) = 1`
   satisfies `0 ∉ D`, `1 ∈ D`, closure under multiplication and inversion (`x⁻¹ = x ^ (2 ^ r - 1)`),
   membership characterization `z ∈ D ↔ z ^ (2 ^ r) = 1`, and
   `(X : F[X]) ^ (2 ^ r) - 1 = ∏ x ∈ D, (X - C x)`.

2. **Mersenne Circle Frobenius Conjugation (`complement_locator_cw_star`):**
   Over any field `F` of size `(2 ^ 31 - 1) ^ 2` (`p = 2 ^ 31 - 1` kernel-proved prime),
   `ringChar F = p`, every `x ∈ D` (`r ≤ 31`) satisfies `x ^ p = x⁻¹` (`x ^ (p + 1) = 1`), and for
   any `S ⊆ D` with complement `U := D \ S` (`u := U.card`) and monic complement locator
   `H_U = ∏ x ∈ U, (X - C x)`, we have `(H_U.coeff 0) ^ (p + 1) = 1`, `H_U.coeff 0 ≠ 0`, and
   `∀ j ≤ u, H_U.coeff (u - j) = H_U.coeff 0 * (H_U.coeff j) ^ p`.

3. **Weierstrass Silent-Band Bijection (`weierstrass_silent_band_iff`):**
   At agreement `5 * 2 ^ (r - 3) ≤ S.card` (`4 ≤ r`), ambient Reed–Solomon codewords
   `P.natDegree ≤ 2 ^ (r - 1)` agreeing with `w` on `S` are unique (`P = B /ₘ H_U` where
   `B := (w * H_U) %ₘ (X ^ (2 ^ r) - 1)`), and exist if and only if `B` vanishes across the
   Weierstrass silent band `(2 ^ (r - 1) + u, 2 ^ r)` (`B.natDegree ≤ 2 ^ (r - 1) + u`).

4. **Universal Cyclic-Arc / Exterior-Window Bound (`nativeListBound_le_one_of_cyclic_shift` and
   four explicit window/wraparound corollaries):**
   Over *every* field `F`, whenever a cyclic shift `s` with `2 ^ (r - 1) + s < 5 * 2 ^ (r - 3)`
   places every active high exponent `(m i + s) % (2 ^ r)` strictly below `5 * 2 ^ (r - 3)`, at most
   **one** ambient polynomial of degree `≤ 2 ^ (r - 1)` (hence `NativeListBound ... 1`) agrees with
   `∑ i, C (a i) * X ^ (m i) + R` on `5 * 2 ^ (r - 3)` points of `D`.

5. **Canonical Reduction (`interiorThree_of_canonical_weierstrass_cw`) and Exhaustive Named
   Sub-Lemma Decomposition (`interiorThree_of_named_sublemmas`):**
   Reduces `MCAChallenge.InteriorThree K` (`1 ≤ K ≤ 2 ^ 20`) to `CanonicalInteriorCWBound K`
   (`1 ≤ d ≤ 3` strictly increasing exponents in `[5n/8, 7n/8]` with no cyclic gap `> 3n/8`,
   `b 0 = 1`, `R = 0` absorbed into scalar circle key `γ ∈ F`), and further decomposes
   `CanonicalInteriorCWBound K` into four self-contained open sub-lemmas:
   - `SingleMonomialWronskianVanishing` (`Theorem W` / `M-0934` + `M-0958` inner & mirror vanishing),
   - `SingleMonomialFrobeniusBoundaryCWVanishing` (`Theorem CW` Frobenius-inversion boundary `4h = 3q - δ`),
   - `SingleMonomialResidualCWBound K` (remaining `d = 1` interior complement bound), and
   - `MultiMonomialCanonicalCWBound K` (`d ∈ {2, 3}` canonical interior complement bound).
-/

namespace InteriorThreeCanonicalReduction

open Polynomial Finset

/-! ## Part 0: Polynomial Degree & Monic Division Helpers -/

lemma degree_lt_of_natDegree_lt {R : Type*} [Semiring R] {P : R[X]} {m : ℕ}
    (h : P.natDegree < m) : P.degree < (m : WithBot ℕ) :=
  lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr h)

lemma mul_divByMonic_cancel {F : Type*} [Field F] (P : F[X]) {Q : F[X]} (hQ : Q.Monic) :
    (P * Q) %ₘ Q = 0 ∧ (P * Q) /ₘ Q = P := by
  have hdiv := Polynomial.modByMonic_add_div (P * Q) Q
  have hmod_lt : ((P * Q) %ₘ Q).degree < Q.degree :=
    Polynomial.degree_modByMonic_lt (P * Q) hQ
  have hdiff_eq : (P * Q) %ₘ Q = Q * (P - (P * Q) /ₘ Q) := by
    calc (P * Q) %ₘ Q = P * Q - Q * ((P * Q) /ₘ Q) := eq_sub_of_add_eq hdiv
      _ = Q * (P - (P * Q) /ₘ Q) := by ring
  have hsub0 : P - (P * Q) /ₘ Q = 0 := by
    by_contra hne
    have hdeg_mul : ((P * Q) %ₘ Q).degree = Q.degree + (P - (P * Q) /ₘ Q).degree := by
      rw [hdiff_eq, Polynomial.degree_mul]
    have hge0 : (0 : WithBot ℕ) ≤ (P - (P * Q) /ₘ Q).degree :=
      Polynomial.zero_le_degree_iff.mpr hne
    have hle : Q.degree ≤ ((P * Q) %ₘ Q).degree := by
      rw [hdeg_mul]
      exact le_add_of_nonneg_right hge0
    exact not_lt_of_ge hle hmod_lt
  refine ⟨?_, (sub_eq_zero.mp hsub0).symm⟩
  rw [hdiff_eq, hsub0, mul_zero]

/-! ## Part 1: Finite Root-of-Unity Subgroup & Monic Factorization -/

theorem rootsOfUnity_X_pow_sub_one_eq_prod {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {n : ℕ} (hn : 0 < n) (hD_card : D.card = n)
    (hD_pow : ∀ x ∈ D, x ^ n = 1) :
    (X : F[X]) ^ n - 1 = ∏ x ∈ D, (X - Polynomial.C x) := by
  set Q : F[X] := ∏ x ∈ D, (X - Polynomial.C x)
  have hQm : Q.Monic := Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
  have hQd : Q.natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
    simp [hD_card]
  set Δ : F[X] := ((X : F[X]) ^ n - 1) - Q
  suffices hΔ0 : Δ = 0 from sub_eq_zero.mp hΔ0
  have hXn_deg : ((X : F[X]) ^ n - 1).natDegree ≤ n := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact Polynomial.natDegree_X_pow_le n
    · simp
  have hΔ_le : Δ.natDegree ≤ n :=
    le_trans (Polynomial.natDegree_sub_le _ _) (max_le hXn_deg (le_of_eq hQd))
  have hΔ_coeff_n : Δ.coeff n = 0 := by
    have hc1 : (1 : F[X]).coeff n = 0 := by
      simp [Polynomial.coeff_one, hn.ne']
    have hcQ : Q.coeff n = 1 := by
      rw [← hQd]; exact hQm.leadingCoeff
    simp [Δ, hc1, hcQ]
  have hΔ_lt : Δ.natDegree < n := by
    rcases eq_or_ne Δ 0 with h0 | hne
    · rw [h0]; simp [hn]
    · refine lt_of_le_of_ne hΔ_le (fun heq ↦ ?_)
      have hlc : Δ.leadingCoeff = 0 := by
        rw [Polynomial.leadingCoeff, heq, hΔ_coeff_n]
      exact (Polynomial.leadingCoeff_ne_zero.mpr hne) hlc
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq D ?_ ?_ ?_
  · rw [hD_card]; exact degree_lt_of_natDegree_lt hΔ_lt
  · simp [hD_card]
  · intro x hx
    have hQx : Q.eval x = 0 := by
      rw [Polynomial.eval_prod]
      refine Finset.prod_eq_zero hx ?_
      simp
    simp [Δ, hD_pow x hx, hQx]

theorem mem_rootsOfUnity_finset_iff {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {n : ℕ} (hn : 0 < n) (hD_card : D.card = n)
    (hD_pow : ∀ x ∈ D, x ^ n = 1) (z : F) :
    z ∈ D ↔ z ^ n = 1 := by
  constructor
  · exact fun hz ↦ hD_pow z hz
  · intro hzn
    have hfac := rootsOfUnity_X_pow_sub_one_eq_prod hn hD_card hD_pow
    have hev := congrArg (fun P : F[X] ↦ P.eval z) hfac
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      hzn, sub_self, Polynomial.eval_prod] at hev
    obtain ⟨x, hxD, hzx⟩ := Finset.prod_eq_zero_iff.mp hev.symm
    simp only [Polynomial.eval_C, sub_eq_zero] at hzx
    exact hzx ▸ hxD

/-- Complete subgroup and monic factorization package for any dyadic root-of-unity domain
`D : Finset F` of size `2 ^ r`. -/
theorem dyadicSubgroup_properties {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1) :
    (0 : F) ∉ D ∧
    (1 : F) ∈ D ∧
    (∀ x ∈ D, ∀ y ∈ D, x * y ∈ D) ∧
    (∀ x ∈ D, x⁻¹ = x ^ (2 ^ r - 1) ∧ x⁻¹ ∈ D) ∧
    ((X : F[X]) ^ (2 ^ r) - 1 = ∏ x ∈ D, (X - Polynomial.C x)) := by
  have hn : 0 < 2 ^ r := Nat.pos_of_ne_zero (by positivity)
  have hmiff := fun z ↦ mem_rootsOfUnity_finset_iff hn hD_card hD_pow z
  have h0_not : (0 : F) ∉ D := by
    intro h0
    have h01 := hD_pow 0 h0
    rw [zero_pow hn.ne'] at h01
    exact zero_ne_one h01
  refine ⟨h0_not, ?_, ?_, ?_, rootsOfUnity_X_pow_sub_one_eq_prod hn hD_card hD_pow⟩
  · exact (hmiff 1).mpr (one_pow _)
  · intro x hx y hy
    rw [hmiff]
    rw [mul_pow, hD_pow x hx, hD_pow y hy, one_mul]
  · intro x hx
    have hinv_eq : x⁻¹ = x ^ (2 ^ r - 1) := by
      apply inv_eq_of_mul_eq_one_right
      calc x * x ^ (2 ^ r - 1) = x ^ (1 + (2 ^ r - 1)) := by rw [pow_add, pow_one]
        _ = x ^ (2 ^ r) := by congr 1; omega
        _ = 1 := hD_pow x hx
    refine ⟨hinv_eq, (hmiff x⁻¹).mpr ?_⟩
    rw [inv_pow, hD_pow x hx, inv_one]

/-- Alias for `dyadicSubgroup_properties`. -/
theorem dyadic_roots_eq_univ_and_prod {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1) :
    (0 : F) ∉ D ∧
    (1 : F) ∈ D ∧
    (∀ x ∈ D, ∀ y ∈ D, x * y ∈ D) ∧
    (∀ x ∈ D, x⁻¹ = x ^ (2 ^ r - 1) ∧ x⁻¹ ∈ D) ∧
    ((X : F[X]) ^ (2 ^ r) - 1 = ∏ x ∈ D, (X - Polynomial.C x)) :=
  dyadicSubgroup_properties hD_card hD_pow

/-! ## Part 2: Mersenne Circle Frobenius Conjugation (`CW*`) -/

private def P31 : Nat := 2147483647

private def noDivPow : Nat → Nat → Bool
  | 0, d => !Nat.beq (P31 % (2 * d + 3)) 0
  | f + 1, d => noDivPow f d && noDivPow f (d + 2 ^ f)

private lemma nat_beq_false_iff (a b : Nat) : (!Nat.beq a b) = true ↔ a ≠ b := by
  cases h : Nat.beq a b
  · refine ⟨fun _ heq ↦ ?_, fun _ ↦ rfl⟩
    subst heq; rw [Nat.beq_refl] at h; cases h
  · exact ⟨(fun h1 ↦ by cases h1), (fun hne ↦ absurd (Nat.beq_eq.mp h) hne)⟩

private lemma noDivPow_spec : ∀ (f d m : Nat), noDivPow f d = true →
    Odd m → 2 * d + 3 ≤ m → m < 2 * (d + 2 ^ f) + 3 → ¬ (m ∣ P31)
  | 0, d, m, hok, hm, _, hlt => by
    obtain ⟨k, rfl⟩ := hm
    have hk : k = d + 1 := by change 2 * k + 1 < 2 * (d + 1) + 3 at hlt; omega
    subst hk
    have hne := (nat_beq_false_iff _ _).mp hok
    intro hdvd
    exact hne (Nat.mod_eq_zero_of_dvd (by simpa [show 2 * (d + 1) + 1 = 2 * d + 3 by omega] using hdvd))
  | f + 1, d, m, hok, hm, hle, hlt => by
    simp only [noDivPow, Bool.and_eq_true] at hok
    have hpow : 2 ^ (f + 1) = 2 ^ f + 2 ^ f := by ring
    by_cases hmid : m < 2 * (d + 2 ^ f) + 3
    · exact noDivPow_spec f d m hok.1 hm hle hmid
    · exact noDivPow_spec f (d + 2 ^ f) m hok.2 hm (by omega) (by omega)

/-- Kernel-verified primality of the 31st Mersenne prime `2 ^ 31 - 1 = 2147483647`. -/
theorem prime_mersenne_31 : Nat.Prime (2 ^ 31 - 1) := by
  have hP : 2 ^ 31 - 1 = P31 := by decide
  rw [hP]
  by_contra hnp
  have hm_prime : Nat.Prime P31.minFac := Nat.minFac_prime (by unfold P31; decide)
  have hm_dvd : P31.minFac ∣ P31 := Nat.minFac_dvd P31
  have hm_sq : P31.minFac ^ 2 ≤ P31 := Nat.minFac_sq_le_self (by unfold P31; decide) hnp
  have hsq : P31.minFac < 46341 := by
    by_contra hge; push Not at hge
    have h1 : 46341 ^ 2 ≤ P31 := le_trans (Nat.pow_le_pow_left hge 2) hm_sq
    revert h1; unfold P31; decide
  rcases hm_prime.eq_two_or_odd' with h2 | hodd
  · have hd2 : 2 ∣ P31 := h2 ▸ hm_dvd
    have h0 : P31 % 2 = 0 := Nat.mod_eq_zero_of_dvd hd2
    revert h0; unfold P31; decide
  · have hok : noDivPow 15 0 = true := by decide
    have hm3 : 3 ≤ P31.minFac := by have := hm_prime.two_le; obtain ⟨_, _⟩ := hodd; omega
    have h65 : P31.minFac < 2 * (0 + 2 ^ 15) + 3 := by
      have hp15 : 2 * (0 + 2 ^ 15) + 3 = 65539 := by decide
      omega
    exact noDivPow_spec 15 0 P31.minFac hok hodd hm3 h65 hm_dvd

instance fact_prime_mersenne_31 : Fact (Nat.Prime (2 ^ 31 - 1)) := ⟨prime_mersenne_31⟩

/-- Any field of cardinality `(2 ^ 31 - 1) ^ 2` has characteristic `2 ^ 31 - 1`. -/
theorem mersenne_ext_ringChar {F : Type*} [Field F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2) :
    ringChar F = 2 ^ 31 - 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; decide)
  let _ : Fintype F := Fintype.ofFinite F
  have hfc : Fintype.card F = (2 ^ 31 - 1) ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨m, hchar_prime, hcard_p⟩ := FiniteField.card F (ringChar F)
  have hdvd1 : ringChar F ∣ (2 ^ 31 - 1) ^ 2 := by
    rw [← hfc, hcard_p]; exact dvd_pow_self (ringChar F) m.ne_zero
  have hdvd2 : ringChar F ∣ (2 ^ 31 - 1) := hchar_prime.dvd_of_dvd_pow hdvd1
  exact (prime_mersenne_31.eq_one_or_self_of_dvd _ hdvd2).resolve_left hchar_prime.ne_one

/-- On any `2 ^ r`-th root-of-unity subset `D` (`r ≤ 31`), Frobenius `x ↦ x ^ (2 ^ 31 - 1)` acts as
inversion `x ↦ x⁻¹` (`x ^ ((2 ^ 31 - 1) + 1) = 1`). -/
theorem mersenne_frobenius_inv_on_D {F : Type*} [Field F] {r : ℕ} (hr_hi : r ≤ 31)
    {D : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1) :
    ∀ x ∈ D, x ^ ((2 ^ 31 - 1) + 1) = 1 ∧ x ^ (2 ^ 31 - 1) = x⁻¹ := by
  have hexp : (2 ^ 31 - 1) + 1 = 2 ^ r * 2 ^ (31 - r) := by
    have hadd : r + (31 - r) = 31 := Nat.add_sub_of_le hr_hi
    calc (2 ^ 31 - 1) + 1 = 2 ^ 31 := by decide
      _ = 2 ^ (r + (31 - r)) := by rw [hadd]
      _ = 2 ^ r * 2 ^ (31 - r) := pow_add 2 r (31 - r)
  intro x hx
  have hpow1 : x ^ ((2 ^ 31 - 1) + 1) = 1 := by
    rw [hexp, pow_mul, hD_pow x hx, one_pow]
  refine ⟨hpow1, ?_⟩
  apply eq_inv_of_mul_eq_one_left
  exact (pow_succ x (2 ^ 31 - 1)).symm.trans hpow1

private lemma coeff_X_sub_C_mul_succ {R : Type*} [Ring R] (a : R) (H : R[X]) (k : ℕ) :
    ((X - Polynomial.C a) * H).coeff (k + 1) = H.coeff k - a * H.coeff (k + 1) := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]

private lemma cw_star_induct {F : Type*} [Field F] [DecidableEq F]
    [CharP F (2 ^ 31 - 1)] (U : Finset F)
    (hU : ∀ x ∈ U, x ^ ((2 ^ 31 - 1) + 1) = 1) :
    let H : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    (H.coeff 0) ^ ((2 ^ 31 - 1) + 1) = 1 ∧
    (∀ j ≤ U.card, H.coeff (U.card - j) = H.coeff 0 * (H.coeff j) ^ (2 ^ 31 - 1)) := by
  induction U using Finset.induction_on with
  | empty =>
    dsimp only
    rw [Finset.prod_empty, Finset.card_empty]
    refine ⟨by simp, fun j hj ↦ ?_⟩
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst hj0
    simp
  | @insert a U ha_notMem ih =>
    have ha1 : a ^ ((2 ^ 31 - 1) + 1) = 1 := hU a (Finset.mem_insert_self a U)
    obtain ⟨hc0_ih, hrec_ih⟩ := ih (fun x hx ↦ hU x (Finset.mem_insert_of_mem hx))
    set H : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    set u : ℕ := U.card
    have hHm : H.Monic := Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
    have hHd : H.natDegree = u := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
      simp [u]
    dsimp only
    rw [Finset.prod_insert ha_notMem, Finset.card_insert_of_notMem ha_notMem]
    change (((X - Polynomial.C a) * H).coeff 0) ^ ((2 ^ 31 - 1) + 1) = 1 ∧
      ∀ j ≤ u + 1, ((X - Polynomial.C a) * H).coeff (u + 1 - j) =
        ((X - Polynomial.C a) * H).coeff 0 * (((X - Polynomial.C a) * H).coeff j) ^ (2 ^ 31 - 1)
    have hc0_new : ((X - Polynomial.C a) * H).coeff 0 = -a * H.coeff 0 := by
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul,
        zero_sub, neg_mul]
    have hneg1_even : (-1 : F) ^ ((2 ^ 31 - 1) + 1) = 1 := by
      have hev : (2 ^ 31 - 1) + 1 = 2 * 2 ^ 30 := by decide
      rw [hev, pow_mul, neg_one_sq, one_pow]
    have hc0_norm : (((X - Polynomial.C a) * H).coeff 0) ^ ((2 ^ 31 - 1) + 1) = 1 := by
      rw [hc0_new, show -a * H.coeff 0 = (-1 : F) * a * H.coeff 0 by ring,
        mul_pow, mul_pow, hneg1_even, ha1, hc0_ih, mul_one, mul_one]
    refine ⟨hc0_norm, fun j hj ↦ ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj_pos
    · simp only [Nat.sub_zero]
      have hHm' : ((X - Polynomial.C a) * H).Monic := (Polynomial.monic_X_sub_C a).mul hHm
      have hHd' : ((X - Polynomial.C a) * H).natDegree = u + 1 := by
        rw [(Polynomial.monic_X_sub_C a).natDegree_mul hHm, Polynomial.natDegree_X_sub_C, hHd,
          add_comm]
      have htop : ((X - Polynomial.C a) * H).coeff (u + 1) = 1 := by
        rw [← hHd']; exact hHm'.leadingCoeff
      rw [htop]
      exact hc0_norm.symm.trans (pow_succ' (((X - Polynomial.C a) * H).coeff 0) (2 ^ 31 - 1))
    · rcases eq_or_lt_of_le hj with rfl | hj_lt
      · simp only [Nat.sub_self]
        have hHm' : ((X - Polynomial.C a) * H).Monic := (Polynomial.monic_X_sub_C a).mul hHm
        have hHd' : ((X - Polynomial.C a) * H).natDegree = u + 1 := by
          rw [(Polynomial.monic_X_sub_C a).natDegree_mul hHm, Polynomial.natDegree_X_sub_C, hHd,
            add_comm]
        have htop : ((X - Polynomial.C a) * H).coeff (u + 1) = 1 := by
          rw [← hHd']; exact hHm'.leadingCoeff
        rw [htop, one_pow, mul_one]
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, (Nat.sub_add_cancel hj_pos).symm⟩
        have hk_lt : k < u := Nat.lt_of_succ_lt_succ hj_lt
        have hlhs_idx : u + 1 - (k + 1) = (u - 1 - k) + 1 := by omega
        rw [hlhs_idx, coeff_X_sub_C_mul_succ, coeff_X_sub_C_mul_succ, hc0_new]
        have hfrob_sub :
            (H.coeff k - a * H.coeff (k + 1)) ^ (2 ^ 31 - 1) =
              (H.coeff k) ^ (2 ^ 31 - 1) - a ^ (2 ^ 31 - 1) * (H.coeff (k + 1)) ^ (2 ^ 31 - 1) := by
          have hf := (frobenius F (2 ^ 31 - 1)).map_sub (H.coeff k) (a * H.coeff (k + 1))
          have hfm := (frobenius F (2 ^ 31 - 1)).map_mul a (H.coeff (k + 1))
          change (H.coeff k - a * H.coeff (k + 1)) ^ (2 ^ 31 - 1) =
            (H.coeff k) ^ (2 ^ 31 - 1) - (a * H.coeff (k + 1)) ^ (2 ^ 31 - 1) at hf
          change (a * H.coeff (k + 1)) ^ (2 ^ 31 - 1) =
            a ^ (2 ^ 31 - 1) * (H.coeff (k + 1)) ^ (2 ^ 31 - 1) at hfm
          rw [hf, hfm]
        rw [hfrob_sub]
        have hih_k : H.coeff 0 * (H.coeff k) ^ (2 ^ 31 - 1) = H.coeff (u - k) :=
          (hrec_ih k (le_of_lt hk_lt)).symm
        have hih_k1 : H.coeff 0 * (H.coeff (k + 1)) ^ (2 ^ 31 - 1) = H.coeff (u - (k + 1)) :=
          (hrec_ih (k + 1) hk_lt).symm
        have ha_prod : a * a ^ (2 ^ 31 - 1) = 1 :=
          (pow_succ' a (2 ^ 31 - 1)).symm.trans ha1
        have hidx1 : u - 1 - k = u - (k + 1) := by omega
        have hidx2 : (u - 1 - k) + 1 = u - k := by omega
        rw [hidx2, hidx1]
        calc H.coeff (u - (k + 1)) - a * H.coeff (u - k)
            = 1 * (H.coeff 0 * (H.coeff (k + 1)) ^ (2 ^ 31 - 1)) -
              a * (H.coeff 0 * (H.coeff k) ^ (2 ^ 31 - 1)) := by rw [one_mul, hih_k1, hih_k]
          _ = (a * a ^ (2 ^ 31 - 1)) * (H.coeff 0 * (H.coeff (k + 1)) ^ (2 ^ 31 - 1)) -
              a * (H.coeff 0 * (H.coeff k) ^ (2 ^ 31 - 1)) := by rw [ha_prod]
          _ = -a * H.coeff 0 *
              ((H.coeff k) ^ (2 ^ 31 - 1) -
               a ^ (2 ^ 31 - 1) * (H.coeff (k + 1)) ^ (2 ^ 31 - 1)) := by ring

/-- **Mersenne Circle Complement-Locator Conjugate Reciprocity (`CW*`):**
Over any field `F` with `Nat.card F = (2 ^ 31 - 1) ^ 2` and `r ≤ 31` (including every `4 ≤ r ≤ 31`),
for any `S ⊆ D` (`∀ x ∈ D, x ^ (2 ^ r) = 1`), the monic complement locator
`H_U := ∏ x ∈ D \ S, (X - C x)` (`u := (D \ S).card`) has norm-1 constant term
`(H_U.coeff 0) ^ ((2 ^ 31 - 1) + 1) = 1` (`H_U.coeff 0 ≠ 0`) and satisfies
`∀ j ≤ u, H_U.coeff (u - j) = H_U.coeff 0 * (H_U.coeff j) ^ (2 ^ 31 - 1)`. -/
theorem complement_locator_cw_star {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2) {r : ℕ} (hr_hi : r ≤ 31)
    {D S : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1) (_hSD : S ⊆ D) :
    let U := D \ S
    let u := U.card
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    H_U.Monic ∧
    H_U.natDegree = u ∧
    (H_U.coeff 0) ^ ((2 ^ 31 - 1) + 1) = 1 ∧
    H_U.coeff 0 ≠ 0 ∧
    (∀ j ≤ u, H_U.coeff (u - j) = H_U.coeff 0 * (H_U.coeff j) ^ (2 ^ 31 - 1)) := by
  have hrchar : ringChar F = 2 ^ 31 - 1 := mersenne_ext_ringChar hF
  have : CharP F (2 ^ 31 - 1) := ringChar.of_eq hrchar
  have hinv := mersenne_frobenius_inv_on_D hr_hi hD_pow
  set U := D \ S
  set u := U.card
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  have hHm : H_U.Monic := Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
  have hHd : H_U.natDegree = u := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
    simp [u]
  obtain ⟨hc0_pow, hrec⟩ := cw_star_induct U (fun x hx ↦ (hinv x (Finset.sdiff_subset hx)).1)
  have hc0_ne : H_U.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at hc0_pow
    exact zero_ne_one hc0_pow
  exact ⟨hHm, hHd, hc0_pow, hc0_ne, hrec⟩

/-! ## Part 3: Weierstrass Silent-Band Bijection -/

lemma dyadic_five_eighths_bounds {r : ℕ} (hr : 4 ≤ r) :
    2 ^ (r - 1) < 5 * 2 ^ (r - 3) ∧
    ∀ u : ℕ, u + 5 * 2 ^ (r - 3) ≤ 2 ^ r → 2 ^ (r - 1) + u < 2 ^ r := by
  have hq_pos : 0 < 2 ^ (r - 3) := Nat.pos_of_ne_zero (by positivity)
  have hr1 : 2 ^ (r - 1) = 4 * 2 ^ (r - 3) := by
    have he : r - 1 = (r - 3) + 2 := by omega
    conv_lhs => rw [he, pow_add]
    ring
  have hr0 : 2 ^ r = 8 * 2 ^ (r - 3) := by
    have he : r = (r - 3) + 3 := by omega
    conv_lhs => rw [he, pow_add]
    ring
  refine ⟨by omega, fun u hu ↦ by omega⟩

/-- Uniqueness of ambient Reed–Solomon codewords `P.natDegree ≤ 2 ^ (r - 1)` on any agreement set
`S` of size `5 * 2 ^ (r - 3) ≤ S.card` (`4 ≤ r`). -/
theorem ambient_unique_on_agreement {F : Type*} [Field F] {r : ℕ} (hr : 4 ≤ r)
    {S : Finset F} (hS_card : 5 * 2 ^ (r - 3) ≤ S.card)
    {w P₁ P₂ : F[X]}
    (hdeg1 : P₁.natDegree ≤ 2 ^ (r - 1)) (hdeg2 : P₂.natDegree ≤ 2 ^ (r - 1))
    (hag1 : ∀ x ∈ S, P₁.eval x = w.eval x) (hag2 : ∀ x ∈ S, P₂.eval x = w.eval x) :
    P₁ = P₂ := by
  have hlt_S : 2 ^ (r - 1) < S.card := lt_of_lt_of_le (dyadic_five_eighths_bounds hr).1 hS_card
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq S
    (degree_lt_of_natDegree_lt (lt_of_le_of_lt hdeg1 hlt_S))
    (degree_lt_of_natDegree_lt (lt_of_le_of_lt hdeg2 hlt_S)) ?_
  intro x hx
  rw [hag1 x hx, hag2 x hx]

/-- Unconditional divisibility `B = (B /ₘ H_U) * H_U` and degree bound `B.natDegree < 2 ^ r` for
`B := (w * H_U) %ₘ (X ^ (2 ^ r) - 1)` whenever `U ⊆ D`. -/
theorem locator_dvd_twisted_mod {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} {D U : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (hUD : U ⊆ D) (w : F[X]) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    let M : F[X] := (X : F[X]) ^ (2 ^ r) - 1
    let B : F[X] := (w * H_U) %ₘ M
    B.natDegree < 2 ^ r ∧
    (∀ x ∈ D, B.eval x = w.eval x * H_U.eval x) ∧
    B = (B /ₘ H_U) * H_U := by
  have hn : 0 < 2 ^ r := Nat.pos_of_ne_zero (by positivity)
  have hfac := rootsOfUnity_X_pow_sub_one_eq_prod hn hD_card hD_pow
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  set M : F[X] := (X : F[X]) ^ (2 ^ r) - 1
  set B : F[X] := (w * H_U) %ₘ M
  have hMm : M.Monic := by
    rw [hfac]
    exact Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
  have hMd : M.natDegree = 2 ^ r := by
    rw [hfac, Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
    simp [hD_card]
  have hB_deg_lt : B.natDegree < 2 ^ r := by
    rcases eq_or_ne B 0 with hB0 | hBne
    · rw [hB0]; simp [hn]
    · have hd : B.degree < ((2 ^ r : ℕ) : WithBot ℕ) := by
        rw [← hMd]
        exact lt_of_lt_of_le (Polynomial.degree_modByMonic_lt (w * H_U) hMm)
          Polynomial.degree_le_natDegree
      rw [Polynomial.degree_eq_natDegree hBne] at hd
      exact WithBot.coe_lt_coe.mp hd
  have hB_eval : ∀ x ∈ D, B.eval x = w.eval x * H_U.eval x := by
    have hdiv := Polynomial.modByMonic_add_div (w * H_U) M
    intro x hx
    have hMx : M.eval x = 0 := by simp [M, hD_pow x hx]
    have hev := congrArg (fun P : F[X] ↦ P.eval x) hdiv
    change (B + M * ((w * H_U) /ₘ M)).eval x = (w * H_U).eval x at hev
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hMx, zero_mul, add_zero] at hev
    exact hev
  have hHm : H_U.Monic := Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
  have hHd : H_U.natDegree = U.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
    simp
  have hdivH := Polynomial.modByMonic_add_div B H_U
  have hrem0 : B %ₘ H_U = 0 := by
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq U ?_ ?_ ?_
    · rw [← hHd]
      exact lt_of_lt_of_le (Polynomial.degree_modByMonic_lt B hHm) Polynomial.degree_le_natDegree
    · exact WithBot.bot_lt_coe U.card
    · intro x hxU
      have hHx : H_U.eval x = 0 := by
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero hxU (by simp)
      have hBx : B.eval x = 0 := by
        rw [hB_eval x (hUD hxU), hHx, mul_zero]
      have hev := congrArg (fun P : F[X] ↦ P.eval x) hdivH
      change (B %ₘ H_U + H_U * (B /ₘ H_U)).eval x = B.eval x at hev
      rw [Polynomial.eval_add, Polynomial.eval_mul, hHx, zero_mul, add_zero, hBx] at hev
      rw [Polynomial.eval_zero]
      exact hev
  refine ⟨hB_deg_lt, hB_eval, ?_⟩
  rw [hrem0, zero_add, mul_comm] at hdivH
  exact hdivH.symm

/-- **Weierstrass Silent-Band Bijection & Explicit Quotient Witness:**
For `4 ≤ r`, root-of-unity domain `D` (`D.card = 2 ^ r`), `S ⊆ D` with `5 * 2 ^ (r - 3) ≤ S.card`,
complement `U := D \ S` (`u := U.card`), `H_U := ∏ x ∈ U, (X - C x)`, and
`B := (w * H_U) %ₘ (X ^ (2 ^ r) - 1)`:
1. If `P.natDegree ≤ 2 ^ (r - 1)` agrees with `w` on `S`, then `B = P * H_U`, `P = B /ₘ H_U`, and
   `B.natDegree ≤ 2 ^ (r - 1) + u`.
2. Conversely, if `B.natDegree ≤ 2 ^ (r - 1) + u`, then `P := B /ₘ H_U` satisfies `B = P * H_U`,
   `P.natDegree ≤ 2 ^ (r - 1)`, and `∀ x ∈ S, P.eval x = w.eval x`.
3. `(∃ P, P.natDegree ≤ 2 ^ (r - 1) ∧ ∀ x ∈ S, P.eval x = w.eval x) ↔ B.natDegree ≤ 2 ^ (r - 1) + u`
   and `B.natDegree ≤ 2 ^ (r - 1) + u ↔ (∀ j, 2 ^ (r - 1) + u < j → j < 2 ^ r → B.coeff j = 0)`. -/
theorem weierstrass_silent_band_iff {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} (hr : 4 ≤ r) {D S : Finset F}
    (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (hSD : S ⊆ D) (hS_card : 5 * 2 ^ (r - 3) ≤ S.card) (w : F[X]) :
    let U := D \ S
    let u := U.card
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    let B : F[X] := (w * H_U) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)
    ((∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧ ∀ x ∈ S, P.eval x = w.eval x) ↔
      B.natDegree ≤ 2 ^ (r - 1) + u) ∧
    (B.natDegree ≤ 2 ^ (r - 1) + u ↔
      (∀ j : ℕ, 2 ^ (r - 1) + u < j → j < 2 ^ r → B.coeff j = 0)) ∧
    (∀ P : F[X], P.natDegree ≤ 2 ^ (r - 1) → (∀ x ∈ S, P.eval x = w.eval x) →
      B = P * H_U ∧ P = B /ₘ H_U) ∧
    (B.natDegree ≤ 2 ^ (r - 1) + u →
      (B /ₘ H_U).natDegree ≤ 2 ^ (r - 1) ∧ ∀ x ∈ S, (B /ₘ H_U).eval x = w.eval x) := by
  let U := D \ S
  let u := U.card
  let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  let B : F[X] := (w * H_U) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)
  have hHm : H_U.Monic := Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
  have hHd : H_U.natDegree = u := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
    simp [u]
  obtain ⟨hB_lt, hB_eval, hB_fac⟩ := locator_dvd_twisted_mod hD_card hD_pow Finset.sdiff_subset w
  change B.natDegree < 2 ^ r at hB_lt
  change ∀ x ∈ D, B.eval x = w.eval x * H_U.eval x at hB_eval
  change B = (B /ₘ H_U) * H_U at hB_fac
  have hu_add : u + S.card = 2 ^ r := by
    dsimp [u, U]
    rw [Finset.card_sdiff_add_card_eq_card hSD, hD_card]
  have hku_lt : 2 ^ (r - 1) + u < 2 ^ r :=
    (dyadic_five_eighths_bounds hr).2 u (by omega)
  have hfwd : ∀ P : F[X], P.natDegree ≤ 2 ^ (r - 1) → (∀ x ∈ S, P.eval x = w.eval x) →
      B = P * H_U ∧ P = B /ₘ H_U ∧ B.natDegree ≤ 2 ^ (r - 1) + u := by
    intro P hP_deg hP_ag
    have hPH_le : (P * H_U).natDegree ≤ 2 ^ (r - 1) + u := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [hHd]; omega
    have hB_eq_PH : B = P * H_U := by
      refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq D ?_ ?_ ?_
      · rw [hD_card]; exact degree_lt_of_natDegree_lt hB_lt
      · rw [hD_card]; exact degree_lt_of_natDegree_lt (lt_of_le_of_lt hPH_le hku_lt)
      · intro x hxD
        rw [hB_eval x hxD, Polynomial.eval_mul]
        by_cases hxS : x ∈ S
        · rw [hP_ag x hxS]
        · have hxU : x ∈ U := Finset.mem_sdiff.mpr ⟨hxD, hxS⟩
          have hHx : H_U.eval x = 0 := by
            rw [Polynomial.eval_prod]
            exact Finset.prod_eq_zero hxU (by simp)
          rw [hHx, mul_zero, mul_zero]
    have hP_eq_div : P = B /ₘ H_U := by
      rw [hB_eq_PH, (mul_divByMonic_cancel P hHm).2]
    exact ⟨hB_eq_PH, hP_eq_div, hB_eq_PH ▸ hPH_le⟩
  have hbwd : B.natDegree ≤ 2 ^ (r - 1) + u →
      (B /ₘ H_U).natDegree ≤ 2 ^ (r - 1) ∧ ∀ x ∈ S, (B /ₘ H_U).eval x = w.eval x := by
    intro hB_le
    let P := B /ₘ H_U
    have hP_deg : P.natDegree ≤ 2 ^ (r - 1) := by
      rcases eq_or_ne P 0 with hP0 | hPne
      · rw [hP0]; simp
      · have hmul_deg : B.natDegree = P.natDegree + u := by
          calc B.natDegree = (P * H_U).natDegree := congrArg Polynomial.natDegree hB_fac
            _ = P.natDegree + H_U.natDegree := Polynomial.natDegree_mul hPne hHm.ne_zero
            _ = P.natDegree + u := by rw [hHd]
        omega
    refine ⟨hP_deg, fun x hxS ↦ ?_⟩
    have hx_not_U : x ∉ U := fun hxU ↦ (Finset.mem_sdiff.mp hxU).2 hxS
    have hHx_ne : H_U.eval x ≠ 0 := by
      rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro y hyU
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
      exact fun hxy ↦ hx_not_U (hxy ▸ hyU)
    have hev : P.eval x * H_U.eval x = w.eval x * H_U.eval x := by
      calc P.eval x * H_U.eval x
          = (P * H_U).eval x := (@Polynomial.eval_mul F _ P H_U x).symm
        _ = B.eval x := congrArg (fun Q : F[X] ↦ Q.eval x) hB_fac.symm
        _ = w.eval x * H_U.eval x := hB_eval x (hSD hxS)
    exact mul_right_cancel₀ hHx_ne hev
  have hband_iff : B.natDegree ≤ 2 ^ (r - 1) + u ↔
      (∀ j : ℕ, 2 ^ (r - 1) + u < j → j < 2 ^ r → B.coeff j = 0) := by
    constructor
    · intro hle j hj_gt _
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle hj_gt)
    · intro hvan
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro j hj_gt
      by_cases hj_lt : j < 2 ^ r
      · exact hvan j hj_gt hj_lt
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hB_lt (not_lt.mp hj_lt))
  refine ⟨⟨fun ⟨P, hPd, hPa⟩ ↦ (hfwd P hPd hPa).2.2,
           fun hBle ↦ ⟨B /ₘ H_U, (hbwd hBle).1, (hbwd hBle).2⟩⟩,
          hband_iff,
          fun P hPd hPa ↦ ⟨(hfwd P hPd hPa).1, (hfwd P hPd hPa).2.1⟩,
          hbwd⟩

/-! ## Part 4: Universal Cyclic-Arc / Exterior-Window Bound (`L.card ≤ 1` Over Every Field) -/

private lemma natDegree_sum_lt {R ι : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X])
    {B : ℕ} (hB : 0 < B) (hf : ∀ i ∈ s, (f i).natDegree < B) :
    (∑ i ∈ s, f i).natDegree < B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      (max_lt (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))))

lemma dyadic_octant_identities {r : ℕ} (hr : 4 ≤ r) :
    0 < 2 ^ (r - 3) ∧
    2 ^ (r - 1) = 4 * 2 ^ (r - 3) ∧
    2 ^ r = 8 * 2 ^ (r - 3) := by
  have hq : 0 < 2 ^ (r - 3) := Nat.pos_of_ne_zero (by positivity)
  have hr1 : 2 ^ (r - 1) = 4 * 2 ^ (r - 3) := by
    have he : r - 1 = (r - 3) + 2 := by omega
    conv_lhs => rw [he, pow_add]
    ring
  have hr0 : 2 ^ r = 8 * 2 ^ (r - 3) := by
    have he : r = (r - 3) + 3 := by omega
    conv_lhs => rw [he, pow_add]
    ring
  exact ⟨hq, hr1, hr0⟩

/-- **Ambient Cyclic-Shift Uniqueness (`L.card ≤ 1` for arbitrary finite index type `ι`):**
Over any field `F`, if `2 ^ (r - 1) + s < 5 * 2 ^ (r - 3)` and every active exponent satisfies
`(m i + s) % (2 ^ r) < 5 * 2 ^ (r - 3)`, then at most **one** polynomial `P` of degree
`≤ 2 ^ (r - 1)` agrees with `∑ i, C (a i) * X ^ (m i) + R` on at least `5 * 2 ^ (r - 3)` points of
`D`. -/
theorem ambientListBound_le_one_of_cyclic_shift {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    {r : ℕ} {D : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (m : ι → ℕ) (a : ι → F) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1))
    {s : ℕ} (hs : 2 ^ (r - 1) + s < 5 * 2 ^ (r - 3))
    (hm_shift : ∀ i : ι, a i ≠ 0 → (m i + s) % (2 ^ r) < 5 * 2 ^ (r - 3))
    (L : Finset F[X])
    (hL : ∀ P ∈ L, P.natDegree ≤ 2 ^ (r - 1) ∧
      5 * 2 ^ (r - 3) ≤
        (D.filter fun x ↦ P.eval x = (∑ i, Polynomial.C (a i) * X ^ (m i) + R).eval x).card) :
    L.card ≤ 1 := by
  set A : ℕ := 5 * 2 ^ (r - 3)
  have hA_pos : 0 < A := Nat.pos_of_ne_zero (by dsimp [A]; positivity)
  set w : F[X] := ∑ i : ι, Polynomial.C (a i) * X ^ (m i) + R
  set W_s : F[X] :=
    (∑ i : ι, Polynomial.C (a i) * X ^ ((m i + s) % (2 ^ r))) + X ^ s * R
  have hWs_lt : W_s.natDegree < A := by
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
    · refine natDegree_sum_lt Finset.univ _ hA_pos (fun i _ ↦ ?_)
      by_cases hai : a i = 0
      · simp [hai, hA_pos]
      · refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le (a i) _) ?_
        exact lt_of_le_of_lt (Polynomial.natDegree_X_pow_le _) (hm_shift i hai)
    · have hXR : (X ^ s * R).natDegree ≤ s + R.natDegree := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        have hXs : (X ^ s : F[X]).natDegree ≤ s := Polynomial.natDegree_X_pow_le s
        omega
      dsimp [A]
      omega
  have hWs_eval : ∀ x ∈ D, W_s.eval x = x ^ s * w.eval x := by
    intro x hxD
    have hx_mod : ∀ i : ι, x ^ ((m i + s) % (2 ^ r)) = x ^ s * x ^ (m i) := by
      intro i
      have hdm := Nat.div_add_mod (m i + s) (2 ^ r)
      calc x ^ ((m i + s) % (2 ^ r))
          = 1 * x ^ ((m i + s) % (2 ^ r)) := (one_mul _).symm
        _ = (x ^ (2 ^ r)) ^ ((m i + s) / (2 ^ r)) * x ^ ((m i + s) % (2 ^ r)) := by
            rw [hD_pow x hxD, one_pow]
        _ = x ^ (2 ^ r * ((m i + s) / (2 ^ r)) + (m i + s) % (2 ^ r)) := by
            rw [pow_add, pow_mul]
        _ = x ^ (m i + s) := by rw [hdm]
        _ = x ^ s * x ^ (m i) := by rw [pow_add, mul_comm]
    simp only [W_s, w, Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hx_mod]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    ring
  have hP_eq : ∀ P ∈ L, X ^ s * P = W_s := by
    intro P hPm
    obtain ⟨hP_deg, hP_ag⟩ := hL P hPm
    set S_P := D.filter (fun x ↦ P.eval x = w.eval x)
    have hXP_lt : (X ^ s * P).natDegree < S_P.card := by
      have hle : (X ^ s * P).natDegree ≤ s + P.natDegree := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        have hXs : (X ^ s : F[X]).natDegree ≤ s := Polynomial.natDegree_X_pow_le s
        omega
      dsimp [A] at hs
      omega
    have hWs_SP : W_s.natDegree < S_P.card := lt_of_lt_of_le hWs_lt hP_ag
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq S_P
      (degree_lt_of_natDegree_lt hXP_lt) (degree_lt_of_natDegree_lt hWs_SP) ?_
    intro x hxS
    obtain ⟨hxD, hx_eq⟩ := Finset.mem_filter.mp hxS
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hx_eq, hWs_eval x hxD]
  refine Finset.card_le_one.mpr (fun P₁ h₁ P₂ h₂ ↦ ?_)
  have heq : (X : F[X]) ^ s * P₁ = (X : F[X]) ^ s * P₂ := (hP_eq P₁ h₁).trans (hP_eq P₂ h₂).symm
  exact mul_left_cancel₀ (Polynomial.monic_X_pow s).ne_zero heq

/-- **Universal Cyclic-Arc / Exterior-Window Bound (`MCAChallenge.NativeListBound ... 1`):**
For `w = ∑ i : Fin 3, C (a i) * X ^ (m i) + R` (`R.natDegree ≤ 2 ^ (r - 1)`), if some shift
`s < 2 ^ r` satisfies `2 ^ (r - 1) + s < 5 * 2 ^ (r - 3)` and maps every active exponent into
`[0, 5 * 2 ^ (r - 3))` modulo `2 ^ r`, then `NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3)) w 1`
holds over *every* field `F`. -/
theorem nativeListBound_le_one_of_cyclic_shift {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} {D : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (m : Fin 3 → ℕ) (a : Fin 3 → F) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1))
    {s : ℕ} (_hs_lt : s < 2 ^ r) (hs : 2 ^ (r - 1) + s < 5 * 2 ^ (r - 3))
    (hm_shift : ∀ i : Fin 3, a i ≠ 0 → (m i + s) % (2 ^ r) < 5 * 2 ^ (r - 3)) :
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3))
      (∑ i, Polynomial.C (a i) * X ^ (m i) + R) 1 := by
  intro L hL
  have hcard : L.card ≤ 1 :=
    ambientListBound_le_one_of_cyclic_shift hD_pow m a R hR hs hm_shift L
      (fun P hP ↦ ⟨(hL P hP).1.1, (hL P hP).2⟩)
  exact_mod_cast hcard

/-- Corollary 1 (`s = 0`): All high coefficients vanish (`∀ i, a i = 0`). -/
theorem nativeListBound_le_one_of_all_zero {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} (hr : 4 ≤ r) {D : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (m : Fin 3 → ℕ) (a : Fin 3 → F) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1))
    (ha0 : ∀ i : Fin 3, a i = 0) :
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3))
      (∑ i, Polynomial.C (a i) * X ^ (m i) + R) 1 := by
  obtain ⟨hq, hr1, hr0⟩ := dyadic_octant_identities hr
  exact nativeListBound_le_one_of_cyclic_shift hD_pow m a R hR
    (s := 0) (by omega) (by omega) (fun i hi ↦ absurd (ha0 i) hi)

/-- Corollary 2 (`s = 0`): Low-exterior window (`∀ i, a i ≠ 0 → m i < 5 * 2 ^ (r - 3)`). -/
theorem nativeListBound_le_one_of_low_window {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} (hr : 4 ≤ r) {D : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (m : Fin 3 → ℕ) (a : Fin 3 → F) (R : F[X]) (hR : R.natDegree ≤ 2 ^ (r - 1))
    (hlow : ∀ i : Fin 3, a i ≠ 0 → m i < 5 * 2 ^ (r - 3)) :
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3))
      (∑ i, Polynomial.C (a i) * X ^ (m i) + R) 1 := by
  obtain ⟨hq, hr1, hr0⟩ := dyadic_octant_identities hr
  refine nativeListBound_le_one_of_cyclic_shift hD_pow m a R hR
    (s := 0) (by omega) (by omega) (fun i hi ↦ ?_)
  have hmi := hlow i hi
  rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  exact hmi

/-- Corollary 3 (`s = 2 ^ r - m₀`): High-exterior window (`∃ m₀ > 7 * 2 ^ (r - 3), ∀ i, a i ≠ 0 → m₀ ≤ m i`). -/
theorem nativeListBound_le_one_of_high_window {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} (hr : 4 ≤ r) {D : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (m : Fin 3 → ℕ) (a : Fin 3 → F) (R : F[X])
    (hm_lt : ∀ i : Fin 3, m i < 2 ^ r) (hR : R.natDegree ≤ 2 ^ (r - 1))
    {m₀ : ℕ} (hm₀_gt : 7 * 2 ^ (r - 3) < m₀) (hhigh : ∀ i : Fin 3, a i ≠ 0 → m₀ ≤ m i) :
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3))
      (∑ i, Polynomial.C (a i) * X ^ (m i) + R) 1 := by
  obtain ⟨hq, hr1, hr0⟩ := dyadic_octant_identities hr
  by_cases hall0 : ∀ i : Fin 3, a i = 0
  · exact nativeListBound_le_one_of_all_zero hr hD_pow m a R hR hall0
  · push Not at hall0
    obtain ⟨i₀, hi₀⟩ := hall0
    have hm₀_lt : m₀ < 2 ^ r := lt_of_le_of_lt (hhigh i₀ hi₀) (hm_lt i₀)
    refine nativeListBound_le_one_of_cyclic_shift hD_pow m a R hR
      (s := 2 ^ r - m₀) (by omega) (by omega) (fun i hi ↦ ?_)
    have hmi_ge := hhigh i hi
    have hmi_lt := hm_lt i
    have hsum_eq : m i + (2 ^ r - m₀) = 2 ^ r + (m i - m₀) := by omega
    rw [hsum_eq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Corollary 4 (`s = 2 ^ r - cut`): Split wraparound gap `> 3 * 2 ^ (r - 3)`
(`∃ cut > 7 * 2 ^ (r - 3), ∀ i, a i ≠ 0 → m i + (2 ^ r - cut) < 5 * 2 ^ (r - 3) ∨ cut ≤ m i`). -/
theorem nativeListBound_le_one_of_split_wraparound {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} (hr : 4 ≤ r) {D : Finset F} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (m : Fin 3 → ℕ) (a : Fin 3 → F) (R : F[X])
    (hm_lt : ∀ i : Fin 3, m i < 2 ^ r) (hR : R.natDegree ≤ 2 ^ (r - 1))
    {cut : ℕ} (hcut_gt : 7 * 2 ^ (r - 3) < cut)
    (hsplit : ∀ i : Fin 3, a i ≠ 0 → m i + (2 ^ r - cut) < 5 * 2 ^ (r - 3) ∨ cut ≤ m i) :
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) (5 * 2 ^ (r - 3))
      (∑ i, Polynomial.C (a i) * X ^ (m i) + R) 1 := by
  obtain ⟨hq, hr1, hr0⟩ := dyadic_octant_identities hr
  refine nativeListBound_le_one_of_cyclic_shift hD_pow m a R hR
    (s := 2 ^ r - cut) (by omega) (by omega) (fun i hi ↦ ?_)
  have hmi_lt := hm_lt i
  rcases hsplit i hi with hlow_i | hhi_i
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact hlow_i
  · have hcut_lt : cut < 2 ^ r := lt_of_le_of_lt hhi_i hmi_lt
    have hsum_eq : m i + (2 ^ r - cut) = 2 ^ r + (m i - cut) := by omega
    rw [hsum_eq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## Part 5: Canonical Weierstrass–`CW*` Predicate & Reduction of `MCAChallenge.InteriorThree` -/

/-- Canonical active high-monomial configuration at dyadic exponent `r`:
`1 ≤ d ≤ 3` strictly increasing exponents in `(2 ^ (r - 1), 2 ^ r)` with all coefficients nonzero,
monic first active coefficient `b 0 = 1`, `m 0 ≤ 7 * 2 ^ (r - 3)`,
`5 * 2 ^ (r - 3) ≤ m (d - 1)`, and every adjacent high-exponent gap `≤ 3 * 2 ^ (r - 3)`. -/
def IsCanonicalHighConfig {F : Type*} [Zero F] [One F]
    (r d : ℕ) (m : Fin d → ℕ) (b : Fin d → F) : Prop :=
  1 ≤ d ∧ d ≤ 3 ∧
  StrictMono m ∧
  (∀ j : Fin d, 2 ^ (r - 1) < m j ∧ m j < 2 ^ r) ∧
  (∀ j : Fin d, b j ≠ 0) ∧
  (∀ h0 : 0 < d, b ⟨0, h0⟩ = 1) ∧
  (∀ h0 : 0 < d, m ⟨0, h0⟩ ≤ 7 * 2 ^ (r - 3)) ∧
  (∀ h0 : 0 < d, 5 * 2 ^ (r - 3) ≤ m ⟨d - 1, Nat.sub_lt h0 Nat.one_pos⟩) ∧
  (∀ (k : ℕ) (hk : k + 1 < d), m ⟨k + 1, hk⟩ - m ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ 3 * 2 ^ (r - 3))

/-- A disagreement complement `U ⊆ D` (`U.card ≤ 3 * 2 ^ (r - 3)`) whose monic locator
`H_U = ∏ x ∈ U, (X - C x)` satisfies `CW*` self-conjugacy, Weierstrass silent-band vanishing for
`w`, and the `γ`-shifted native circle boundary condition `(B /ₘ H_U)_0 + (B /ₘ H_U)_k = γ`. -/
def IsValidCWComplement {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (r : ℕ) (w : F[X]) (γ : F) (U : Finset F) : Prop :=
  U ⊆ D ∧
  U.card ≤ 3 * 2 ^ (r - 3) ∧
  let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  let B : F[X] := (w * H_U) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)
  (H_U.coeff 0) ^ ((2 ^ 31 - 1) + 1) = 1 ∧
  (∀ j ≤ U.card, H_U.coeff (U.card - j) = H_U.coeff 0 * (H_U.coeff j) ^ (2 ^ 31 - 1)) ∧
  B.natDegree ≤ 2 ^ (r - 1) + U.card ∧
  (∀ j : ℕ, 2 ^ (r - 1) + U.card < j → j < 2 ^ r → B.coeff j = 0) ∧
  (B /ₘ H_U).coeff 0 + (B /ₘ H_U).coeff (2 ^ (r - 1)) = γ

/-- **Strictly Simpler Canonical Sub-Lemma Target (`CanonicalInteriorCWBound K`):**
Over any field `F` of size `(2 ^ 31 - 1) ^ 2` and `4 ≤ r ≤ 31`, for every canonical active
`d`-monomial polynomial `w = ∑ j : Fin d, C (b j) * X ^ (m j)` (`1 ≤ d ≤ 3`, `b 0 = 1`, interior
window & no gap `> 3 * 2 ^ (r - 3)`) and scalar circle key `γ ∈ F`, at most `K * 2 ^ r`
complements `U ⊆ D` satisfy `IsValidCWComplement D r w γ U`. -/
def CanonicalInteriorCWBound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ (d : ℕ) (m : Fin d → ℕ) (b : Fin d → F) (γ : F),
        IsCanonicalHighConfig r d m b →
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰, IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U) →
            𝒰.card ≤ K * 2 ^ r

private lemma nat_le_K_two_pow_real {L_card K r : ℕ} (hle : L_card ≤ K * 2 ^ r) :
    (L_card : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ r := by
  have hcast : ((K * 2 ^ r : ℕ) : ℝ) = (K : ℝ) * (2 : ℝ) ^ r := by push_cast; ring
  rw [← hcast]
  exact Nat.cast_le.mpr hle

/-- **Main Canonical Reduction Theorem (`MCAChallenge.InteriorThree K` from `CanonicalInteriorCWBound K`):**
For any `1 ≤ K ≤ 2 ^ 20`, `CanonicalInteriorCWBound K` implies `MCAChallenge.InteriorThree K`. -/
theorem interiorThree_of_canonical_weierstrass_cw.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hCanon : CanonicalInteriorCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K := by
  refine ⟨hK_cap, ?_⟩
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m a R hm_range hR_deg L hL
  obtain ⟨hq, hr1, hr0⟩ := dyadic_octant_identities hr_lo
  have h1_le_Kn : 1 ≤ K * 2 ^ r := by
    have h2r : 1 ≤ 2 ^ r := by omega
    exact Nat.mul_le_mul hK_pos h2r
  let S_raw : Finset ℕ := (Finset.univ : Finset (Fin 3)).image m
  let coeffAt : ℕ → F := fun e ↦ ∑ i ∈ Finset.univ.filter (fun i : Fin 3 ↦ m i = e), a i
  let E_act : Finset ℕ := S_raw.filter (fun e ↦ coeffAt e ≠ 0)
  have hsum_raw :
      (∑ i : Fin 3, Polynomial.C (a i) * X ^ (m i)) =
        ∑ e ∈ S_raw, Polynomial.C (coeffAt e) * X ^ e := by
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin 3))) (t := S_raw)
      (fun i _ ↦ Finset.mem_image_of_mem m (Finset.mem_univ i))
      (fun i : Fin 3 ↦ (Polynomial.C (a i) * X ^ (m i) : F[X]))
    rw [← hfib]
    refine Finset.sum_congr rfl (fun e _ ↦ ?_)
    have hcongr :
        (∑ i ∈ Finset.univ.filter (fun i : Fin 3 ↦ m i = e),
          (Polynomial.C (a i) * X ^ (m i) : F[X])) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin 3 ↦ m i = e),
          (Polynomial.C (a i) * X ^ e : F[X]) := by
      refine Finset.sum_congr rfl (fun i hi ↦ ?_)
      rw [(Finset.mem_filter.mp hi).2]
    rw [hcongr, ← Finset.sum_mul, ← map_sum Polynomial.C]
  have hsum_act :
      (∑ e ∈ S_raw, Polynomial.C (coeffAt e) * X ^ e) =
        ∑ e ∈ E_act, Polynomial.C (coeffAt e) * X ^ e := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun e he_raw he_not ↦ ?_)
    have hc0 : coeffAt e = 0 := by
      by_contra hne
      exact he_not (Finset.mem_filter.mpr ⟨he_raw, hne⟩)
    simp [hc0]
  let d : ℕ := E_act.card
  have hd_le3 : d ≤ 3 := by
    calc d ≤ S_raw.card := Finset.card_filter_le _ _
      _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_image_le
      _ = 3 := by simp
  let iso : Fin d ≃o ↥E_act := E_act.orderIsoOfFin rfl
  let m' : Fin d → ℕ := fun j ↦ (iso j).1
  let c : Fin d → F := fun j ↦ coeffAt (m' j)
  have hm'_mono : StrictMono m' := fun i j hij ↦ iso.strictMono hij
  have hm'_mem : ∀ j : Fin d, m' j ∈ E_act := fun j ↦ (iso j).2
  have hm'_range : ∀ j : Fin d, 2 ^ (r - 1) < m' j ∧ m' j < 2 ^ r := by
    intro j
    have hraw : m' j ∈ S_raw := (Finset.mem_filter.mp (hm'_mem j)).1
    obtain ⟨i, _, hi_eq⟩ := Finset.mem_image.mp hraw
    rw [← hi_eq]
    exact hm_range i
  have hc_ne0 : ∀ j : Fin d, c j ≠ 0 := fun j ↦ (Finset.mem_filter.mp (hm'_mem j)).2
  have hsum_d :
      (∑ j : Fin d, Polynomial.C (c j) * X ^ (m' j)) =
        ∑ e ∈ E_act, Polynomial.C (coeffAt e) * X ^ e := by
    refine Finset.sum_bij (fun (j : Fin d) _ ↦ m' j) ?_ ?_ ?_ ?_
    · intro j _; exact hm'_mem j
    · intro j₁ _ j₂ _ heq; exact iso.injective (Subtype.ext heq)
    · intro e he; exact ⟨iso.symm ⟨e, he⟩, Finset.mem_univ _, by simp [m']⟩
    · intro j _; rfl
  have hw_eq :
      (∑ i : Fin 3, Polynomial.C (a i) * X ^ (m i) + R) =
        (∑ j : Fin d, Polynomial.C (c j) * X ^ (m' j) + R) := by
    rw [hsum_raw, hsum_act, hsum_d]
  have hL_d : ∀ P ∈ L, P.natDegree ≤ 2 ^ (r - 1) ∧
      5 * 2 ^ (r - 3) ≤
        (D.filter fun x ↦ P.eval x =
          (∑ j : Fin d, Polynomial.C (c j) * X ^ (m' j) + R).eval x).card := by
    intro P hPm
    rw [← hw_eq]
    exact ⟨(hL P hPm).1.1, (hL P hPm).2⟩
  rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
  · have hcard1 : L.card ≤ 1 :=
      ambientListBound_le_one_of_cyclic_shift hD_pow m' c R hR_deg
        (s := 0) (by omega) (fun j _ ↦ absurd j.2 (by omega)) L hL_d
    exact nat_le_K_two_pow_real (le_trans hcard1 h1_le_Kn)
  let j₀ : Fin d := ⟨0, hd_pos⟩
  let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd_pos Nat.one_pos⟩
  have hm'_ge_min : ∀ j : Fin d, m' j₀ ≤ m' j := by
    intro j
    rcases Nat.eq_zero_or_pos j.1 with hj0 | hj_pos
    · have hj_eq : j = j₀ := Fin.ext hj0
      rw [hj_eq]
    · exact le_of_lt (hm'_mono (Fin.mk_lt_mk.mpr hj_pos))
  have hm'_le_max : ∀ j : Fin d, m' j ≤ m' j_last := by
    intro j
    have hj_le : j.1 ≤ d - 1 := by have := j.2; omega
    rcases eq_or_lt_of_le hj_le with hjeq | hjlt
    · have hj_eq : j = j_last := Fin.ext hjeq
      rw [hj_eq]
    · exact le_of_lt (hm'_mono (Fin.mk_lt_mk.mpr hjlt))
  by_cases hmin_hi : m' j₀ ≤ 7 * 2 ^ (r - 3)
  · by_cases hmax_lo : 5 * 2 ^ (r - 3) ≤ m' j_last
    · by_cases hgap :
          ∀ (k : ℕ) (hk : k + 1 < d),
            m' ⟨k + 1, hk⟩ - m' ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ 3 * 2 ^ (r - 3)
      · set c₀ : F := c j₀
        have hc₀_ne : c₀ ≠ 0 := hc_ne0 j₀
        let b : Fin d → F := fun j ↦ c₀⁻¹ * c j
        let w_norm : F[X] := ∑ j : Fin d, Polynomial.C (b j) * X ^ (m' j)
        let γ : F := -c₀⁻¹ * (R.coeff 0 + R.coeff (2 ^ (r - 1)))
        have hcanon_cfg : IsCanonicalHighConfig r d m' b := by
          refine ⟨hd_pos, hd_le3, hm'_mono, hm'_range, ?_, ?_, ?_, ?_, hgap⟩
          · intro j; exact mul_ne_zero (inv_ne_zero hc₀_ne) (hc_ne0 j)
          · intro _; exact inv_mul_cancel₀ hc₀_ne
          · intro _; exact hmin_hi
          · intro _; exact hmax_lo
        let φ : F[X] → F[X] := fun P ↦ Polynomial.C c₀⁻¹ * (P - R)
        let uMap : F[X] → Finset F :=
          fun P ↦ D \ (D.filter fun x ↦ (φ P).eval x = w_norm.eval x)
        have hφ_props : ∀ P ∈ L,
            (φ P).natDegree ≤ 2 ^ (r - 1) ∧
            (φ P).coeff 0 + (φ P).coeff (2 ^ (r - 1)) = γ ∧
            5 * 2 ^ (r - 3) ≤ (D.filter fun x ↦ (φ P).eval x = w_norm.eval x).card := by
          intro P hPm
          obtain ⟨⟨hP_deg, hP_circ⟩, hP_ag⟩ := hL P hPm
          have hPR_deg : (φ P).natDegree ≤ 2 ^ (r - 1) := by
            refine le_trans (Polynomial.natDegree_C_mul_le c₀⁻¹ (P - R)) ?_
            exact le_trans (Polynomial.natDegree_sub_le P R) (max_le hP_deg hR_deg)
          have hφ_circ : (φ P).coeff 0 + (φ P).coeff (2 ^ (r - 1)) = γ := by
            dsimp [φ, γ]
            simp only [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
            linear_combination c₀⁻¹ * hP_circ
          have hsub_ag :
              (D.filter fun x ↦
                P.eval x = (∑ i : Fin 3, Polynomial.C (a i) * X ^ (m i) + R).eval x) ⊆
              (D.filter fun x ↦ (φ P).eval x = w_norm.eval x) := by
            intro x hx
            obtain ⟨hxD, hx_eq⟩ := Finset.mem_filter.mp hx
            rw [hw_eq] at hx_eq
            refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
            have hwn_eval : c₀⁻¹ * ((∑ j : Fin d, Polynomial.C (c j) * X ^ (m' j)).eval x) =
                w_norm.eval x := by
              simp only [w_norm, b, Polynomial.eval_finsetSum, Polynomial.eval_mul,
                Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ ↦ by ring)
            dsimp [φ]
            rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, hx_eq,
              Polynomial.eval_add, add_sub_cancel_right, hwn_eval]
          exact ⟨hPR_deg, hφ_circ, le_trans hP_ag (Finset.card_le_card hsub_ag)⟩
        set 𝒰 : Finset (Finset F) := L.image uMap
        have h𝒰_valid : ∀ U ∈ 𝒰, IsValidCWComplement D r w_norm γ U := by
          intro U hUm
          obtain ⟨P, hPm, rfl⟩ := Finset.mem_image.mp hUm
          obtain ⟨hQ_deg, hQ_circ, hSQ_card⟩ := hφ_props P hPm
          set S_Q := D.filter (fun x ↦ (φ P).eval x = w_norm.eval x)
          have hSQ_sub : S_Q ⊆ D := Finset.filter_subset _ D
          have hU_card_le : (D \ S_Q).card ≤ 3 * 2 ^ (r - 3) := by
            have hadd := Finset.card_sdiff_add_card_eq_card hSQ_sub
            omega
          obtain ⟨_, _, hc0_pow, _, hcw_rec⟩ :=
            complement_locator_cw_star hF hr_hi hD_pow hSQ_sub
          obtain ⟨_, hband_iff, hQb, _⟩ :=
            weierstrass_silent_band_iff hr_lo hD_card hD_pow hSQ_sub hSQ_card w_norm
          have hQ_ag : ∀ x ∈ S_Q, (φ P).eval x = w_norm.eval x :=
            fun x hx ↦ (Finset.mem_filter.mp hx).2
          obtain ⟨hB_eq, hQ_div⟩ := hQb (φ P) hQ_deg hQ_ag
          have hB_deg :
              ((w_norm * ∏ x ∈ D \ S_Q, (X - Polynomial.C x)) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)).natDegree ≤
                2 ^ (r - 1) + (D \ S_Q).card := by
            rw [hB_eq]
            refine le_trans Polynomial.natDegree_mul_le ?_
            rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
            simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
            omega
          have hB_van := hband_iff.mp hB_deg
          have hkey :
              (((w_norm * ∏ x ∈ D \ S_Q, (X - Polynomial.C x)) %ₘ
                  ((X : F[X]) ^ (2 ^ r) - 1)) /ₘ
                  (∏ x ∈ D \ S_Q, (X - Polynomial.C x))).coeff 0 +
              (((w_norm * ∏ x ∈ D \ S_Q, (X - Polynomial.C x)) %ₘ
                  ((X : F[X]) ^ (2 ^ r) - 1)) /ₘ
                  (∏ x ∈ D \ S_Q, (X - Polynomial.C x))).coeff (2 ^ (r - 1)) = γ := by
            rw [← hQ_div]
            exact hQ_circ
          exact ⟨Finset.sdiff_subset, hU_card_le, hc0_pow, hcw_rec, hB_deg, hB_van, hkey⟩
        have huMap_inj : Set.InjOn uMap L := by
          intro P₁ h₁ P₂ h₂ hu_eq
          obtain ⟨hQ1_deg, _, hSQ1_card⟩ := hφ_props P₁ h₁
          obtain ⟨hQ2_deg, _, _⟩ := hφ_props P₂ h₂
          set S₁ := D.filter (fun x ↦ (φ P₁).eval x = w_norm.eval x)
          set S₂ := D.filter (fun x ↦ (φ P₂).eval x = w_norm.eval x)
          have hS_eq : S₁ = S₂ := by
            have hd1 : D \ (D \ S₁) = S₁ := Finset.sdiff_sdiff_eq_self (Finset.filter_subset _ D)
            have hd2 : D \ (D \ S₂) = S₂ := Finset.sdiff_sdiff_eq_self (Finset.filter_subset _ D)
            calc S₁ = D \ (uMap P₁) := hd1.symm
              _ = D \ (uMap P₂) := by rw [hu_eq]
              _ = S₂ := hd2
          have hQ_eq : φ P₁ = φ P₂ :=
            ambient_unique_on_agreement hr_lo hSQ1_card hQ1_deg hQ2_deg
              (fun x hx ↦ (Finset.mem_filter.mp hx).2)
              (fun x hx ↦ by rw [hS_eq] at hx; exact (Finset.mem_filter.mp hx).2)
          have hsub_eq : P₁ - R = P₂ - R := by
            calc P₁ - R = (1 : F[X]) * (P₁ - R) := (one_mul _).symm
              _ = (Polynomial.C c₀ * Polynomial.C c₀⁻¹) * (P₁ - R) := by
                  rw [← Polynomial.C_mul, mul_inv_cancel₀ hc₀_ne, Polynomial.C_1]
              _ = Polynomial.C c₀ * (φ P₁) := by rw [mul_assoc]
              _ = Polynomial.C c₀ * (φ P₂) := by rw [hQ_eq]
              _ = (Polynomial.C c₀ * Polynomial.C c₀⁻¹) * (P₂ - R) := by rw [← mul_assoc]
              _ = P₂ - R := by rw [← Polynomial.C_mul, mul_inv_cancel₀ hc₀_ne, Polynomial.C_1, one_mul]
          exact sub_left_injective hsub_eq
        have hL_eq_𝒰 : L.card = 𝒰.card := (Finset.card_image_of_injOn huMap_inj).symm
        have h𝒰_le : 𝒰.card ≤ K * 2 ^ r :=
          hCanon F hF r hr_lo hr_hi D hD_card hD_pow d m' b γ hcanon_cfg 𝒰 h𝒰_valid
        exact nat_le_K_two_pow_real (hL_eq_𝒰 ▸ h𝒰_le)
      · push Not at hgap
        obtain ⟨k, hk, hgap_gt⟩ := hgap
        let idx_lo : Fin d := ⟨k, Nat.lt_of_succ_lt hk⟩
        let idx_hi : Fin d := ⟨k + 1, hk⟩
        have hgap_idx : 3 * 2 ^ (r - 3) < m' idx_hi - m' idx_lo := hgap_gt
        have hlo_gt : 2 ^ (r - 1) < m' idx_lo := (hm'_range idx_lo).1
        have hhi_lt : m' idx_hi < 2 ^ r := (hm'_range idx_hi).2
        have hcard1 : L.card ≤ 1 := by
          refine ambientListBound_le_one_of_cyclic_shift hD_pow m' c R hR_deg
            (s := 2 ^ r - m' idx_hi) (by omega) (fun j _ ↦ ?_) L hL_d
          by_cases hjk : j.1 ≤ k
          · have hmj_le : m' j ≤ m' idx_lo := by
              rcases eq_or_lt_of_le hjk with hjeq | hjlt
              · have hj_eq : j = idx_lo := Fin.ext hjeq
                rw [hj_eq]
              · exact le_of_lt (hm'_mono (Fin.mk_lt_mk.mpr hjlt))
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
          · have hmj_ge : m' idx_hi ≤ m' j := by
              have hge : k + 1 ≤ j.1 := by omega
              rcases eq_or_lt_of_le hge with hjeq | hjlt
              · have hj_eq : j = idx_hi := Fin.ext hjeq.symm
                rw [hj_eq]
              · exact le_of_lt (hm'_mono (Fin.mk_lt_mk.mpr hjlt))
            have hmj_lt : m' j < 2 ^ r := (hm'_range j).2
            have hsum_eq : m' j + (2 ^ r - m' idx_hi) = 2 ^ r + (m' j - m' idx_hi) := by omega
            rw [hsum_eq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            omega
        exact nat_le_K_two_pow_real (le_trans hcard1 h1_le_Kn)
    · have hcard1 : L.card ≤ 1 := by
        refine ambientListBound_le_one_of_cyclic_shift hD_pow m' c R hR_deg
          (s := 0) (by omega) (fun j _ ↦ ?_) L hL_d
        have hmj_le := hm'_le_max j
        have hmj_lt := (hm'_range j).2
        rw [Nat.add_zero, Nat.mod_eq_of_lt hmj_lt]
        omega
      exact nat_le_K_two_pow_real (le_trans hcard1 h1_le_Kn)
  · have hj0_lt : m' j₀ < 2 ^ r := (hm'_range j₀).2
    have hcard1 : L.card ≤ 1 := by
      refine ambientListBound_le_one_of_cyclic_shift hD_pow m' c R hR_deg
        (s := 2 ^ r - m' j₀) (by omega) (fun j _ ↦ ?_) L hL_d
      have hmj_ge := hm'_ge_min j
      have hmj_lt := (hm'_range j).2
      have hsum_eq : m' j + (2 ^ r - m' j₀) = 2 ^ r + (m' j - m' j₀) := by omega
      rw [hsum_eq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
    exact nat_le_K_two_pow_real (le_trans hcard1 h1_le_Kn)

/-! ## Part 6: Exhaustive Named Sub-Lemma Decomposition of `CanonicalInteriorCWBound` -/

/-- Parameter stratum for single-monomial (`d = 1`) two-block cubic & Wronskian vanishing
(`M-0934` + `Theorem W` `M-0958`): at `q = 2 ^ (r - 3)` (`5 ≤ r`), `1 ≤ δ < q`, and
`m = 5 * q + δ` or `m = 7 * q - δ`, writing `h = u + δ - 3 * q` when `3 * q - δ ≤ u`:
- `u < 2 * (q + δ)` encodes `q + h < 3 * δ`,
- `4 * u + 5 * δ < 15 * q` encodes `4 * h < 3 * q - δ` (`Theorem W` Wronskian obstruction),
- `u + 3 * δ < 5 * q` encodes `2 * h < 4 * (q - δ)` (`M-0934` degree-gap obstruction), and
- `3 * u < 8 * q` encodes `3 * h < 3 * δ - q` (`M-0934` low-`e` obstruction). -/
def InSingleWronskianStratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u < 2 * (2 ^ (r - 3) + δ) ∧
    (4 * u + 5 * δ < 15 * 2 ^ (r - 3) ∨
      u + 3 * δ < 5 * 2 ^ (r - 3) ∨
      3 * u < 8 * 2 ^ (r - 3))

/-- **Named Open Sub-Lemma 1 (`SingleMonomialWronskianVanishing` — Theorem W & `M-0934`):**
Across every dyadic `5 ≤ r ≤ 31` (`q = 2 ^ (r - 3)`), no complement `U ⊆ D` in the Wronskian /
two-block cubic vanishing regime (`U.card < 2 * (q + δ)` together with
`4 * U.card + 5 * δ < 15 * q ∨ U.card + 3 * δ < 5 * q ∨ 3 * U.card < 8 * q`) satisfies
`IsValidCWComplement D r (X ^ m) γ U` for either `m = 5 * q + δ` or `m = 7 * q - δ`. -/
def SingleMonomialWronskianVanishing.{u} : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 5 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ δ : ℕ, 1 ≤ δ → δ < 2 ^ (r - 3) →
        ∀ m : ℕ, (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) →
          ∀ (γ : F) (U : Finset F),
            U.card < 2 * (2 ^ (r - 3) + δ) →
            (4 * U.card + 5 * δ < 15 * 2 ^ (r - 3) ∨
              U.card + 3 * δ < 5 * 2 ^ (r - 3) ∨
              3 * U.card < 8 * 2 ^ (r - 3)) →
            ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U

/-- Parameter stratum for the Wronskian boundary Frobenius-inversion obstruction (`Theorem CW`,
`M-0958`): at `4 * h = 3 * q - δ` (`4 * u + 5 * δ = 15 * q`) with `q + h < 3 * δ`
(`u < 2 * (q + δ)`), `1 ≤ k = h - 2 * (q - δ)` (`5 * q < u + 3 * δ`), `4 * k + 1 ≤ h`
(`3 * u + 11 * δ < 17 * q`), and `(2 ^ 31 - 1) ^ j ≡ -1 (mod 3 * δ - q)`. -/
def InSingleFrobeniusBoundaryStratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u < 2 * (2 ^ (r - 3) + δ) ∧
    4 * u + 5 * δ = 15 * 2 ^ (r - 3) ∧
    5 * 2 ^ (r - 3) < u + 3 * δ ∧
    3 * u + 11 * δ < 17 * 2 ^ (r - 3) ∧
    (∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0)

/-- **Named Open Sub-Lemma 2 (`SingleMonomialFrobeniusBoundaryCWVanishing` — Theorem CW):**
Across every dyadic `5 ≤ r ≤ 31`, at the Wronskian boundary `4 * U.card + 5 * δ = 15 * 2 ^ (r - 3)`
(`4 * h = 3 * q - δ`), whenever `U.card < 2 * (2 ^ (r - 3) + δ)`,
`5 * 2 ^ (r - 3) < U.card + 3 * δ`, `3 * U.card + 11 * δ < 17 * 2 ^ (r - 3)` (`h ≥ 4 * k + 1`), and
some power of `2 ^ 31 - 1` is `-1` modulo `e = 3 * δ - 2 ^ (r - 3)`, no complement `U` satisfies
`IsValidCWComplement D r (X ^ m) γ U`. -/
def SingleMonomialFrobeniusBoundaryCWVanishing.{u} : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 5 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ δ : ℕ, 1 ≤ δ → δ < 2 ^ (r - 3) →
        ∀ m : ℕ, (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) →
          ∀ (γ : F) (U : Finset F),
            U.card < 2 * (2 ^ (r - 3) + δ) →
            4 * U.card + 5 * δ = 15 * 2 ^ (r - 3) →
            5 * 2 ^ (r - 3) < U.card + 3 * δ →
            3 * U.card + 11 * δ < 17 * 2 ^ (r - 3) →
            (∃ j : ℕ, ((2 ^ 31 - 1) ^ j + 1) % (3 * δ - 2 ^ (r - 3)) = 0) →
            ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U

/-- **Named Open Sub-Lemma 3 (`SingleMonomialResidualCWBound K`):**
For single-monomial interior exponents `5 * 2 ^ (r - 3) ≤ m ≤ 7 * 2 ^ (r - 3)` (`4 ≤ r ≤ 31`),
at most `K * 2 ^ r` complements `U ⊆ D` outside the Wronskian and Frobenius-boundary vanishing
strata satisfy `IsValidCWComplement D r (X ^ m) γ U`. -/
def SingleMonomialResidualCWBound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ m : ℕ, 5 * 2 ^ (r - 3) ≤ m → m ≤ 7 * 2 ^ (r - 3) → ∀ γ : F,
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r ((X : F[X]) ^ m) γ U ∧
            ¬ InSingleWronskianStratum r m U.card ∧
            ¬ InSingleFrobeniusBoundaryStratum r m U.card) →
          𝒰.card ≤ K * 2 ^ r

/-- **Named Open Sub-Lemma 4 (`MultiMonomialCanonicalCWBound K`):**
For genuine multi-monomial (`d ∈ {2, 3}`) canonical interior configurations, at most `K * 2 ^ r`
complements `U ⊆ D` satisfy `IsValidCWComplement D r (∑ j : Fin d, C (b j) * X ^ (m j)) γ U`. -/
def MultiMonomialCanonicalCWBound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ (d : ℕ) (m : Fin d → ℕ) (b : Fin d → F) (γ : F),
        2 ≤ d → IsCanonicalHighConfig r d m b →
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰, IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U) →
            𝒰.card ≤ K * 2 ^ r

/-- Exhaustive assembly of `CanonicalInteriorCWBound K` from the four named sub-lemmas. -/
theorem canonicalInteriorCWBound_of_named_sublemmas.{u} {K : ℕ}
    (hW : SingleMonomialWronskianVanishing.{u})
    (hCWStar : SingleMonomialFrobeniusBoundaryCWVanishing.{u})
    (hSingleRem : SingleMonomialResidualCWBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    CanonicalInteriorCWBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow d m b γ hcfg 𝒰 h𝒰
  by_cases hd2 : 2 ≤ d
  · exact hMulti F hF r hr_lo hr_hi D hD_card hD_pow d m b γ hd2 hcfg 𝒰 h𝒰
  · have hd1 : d = 1 := by have := hcfg.1; omega
    subst hd1
    let idx0 : Fin 1 := ⟨0, Nat.one_pos⟩
    have hb0 : b idx0 = 1 := hcfg.2.2.2.2.2.1 Nat.one_pos
    have hm_hi : m idx0 ≤ 7 * 2 ^ (r - 3) := hcfg.2.2.2.2.2.2.1 Nat.one_pos
    have hm_lo : 5 * 2 ^ (r - 3) ≤ m idx0 := hcfg.2.2.2.2.2.2.2.1 Nat.one_pos
    have hsum_one :
        (∑ j : Fin 1, Polynomial.C (b j) * (X : F[X]) ^ (m j)) = (X : F[X]) ^ (m idx0) := by
      rw [Fin.sum_univ_one]
      change Polynomial.C (b idx0) * (X : F[X]) ^ (m idx0) = (X : F[X]) ^ (m idx0)
      rw [hb0, map_one, one_mul]
    refine hSingleRem F hF r hr_lo hr_hi D hD_card hD_pow (m idx0) hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
    have hvalid : IsValidCWComplement D r ((X : F[X]) ^ (m idx0)) γ U := by
      have hv := h𝒰 U hUm
      rwa [hsum_one] at hv
    refine ⟨hvalid, ?_, ?_⟩
    · rintro ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hreg⟩
      exact hW F hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt (m idx0) hm_eq γ U hu_lt hreg hvalid
    · rintro ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu_lt, hbdry, hk_pos, hk_hi, hfrob⟩
      exact hCWStar F hF r hr5 hr_hi D hD_card hD_pow δ hδ1 hδ_lt (m idx0) hm_eq γ U
        hu_lt hbdry hk_pos hk_hi hfrob hvalid

/-- **Master Decomposed Reduction (`MCAChallenge.InteriorThree K` from Named Sub-Lemmas):**
Reduces `MCAChallenge.InteriorThree K` (`1 ≤ K ≤ 2 ^ 20`) across all dyadic `4 ≤ r ≤ 31` directly to
`SingleMonomialWronskianVanishing`, `SingleMonomialFrobeniusBoundaryCWVanishing`,
`SingleMonomialResidualCWBound K`, and `MultiMonomialCanonicalCWBound K`. -/
theorem interiorThree_of_named_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hW : SingleMonomialWronskianVanishing.{u})
    (hCWStar : SingleMonomialFrobeniusBoundaryCWVanishing.{u})
    (hSingleRem : SingleMonomialResidualCWBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_canonical_weierstrass_cw hK_pos hK_cap
    (canonicalInteriorCWBound_of_named_sublemmas hW hCWStar hSingleRem hMulti)

end InteriorThreeCanonicalReduction
