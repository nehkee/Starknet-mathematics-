import InteriorThree_LemmaCGBoundary
import InteriorThree_TheoremK0

/-!
# Theorem K0 removes the `k = 0` cells from the single-monomial residual

Target `LEMMA` (tier 3, `problem-3a-upper`). This module wires Theorem K0 (rukafe0x, result 29;
`InteriorThree_TheoremK0`) into the residual `SingleMonomialResidualAfterCGBound K` of
`InteriorThree_LemmaCGBoundary` (which itself sits on omarespejel's M-0998).

* `InSingleK0Stratum r m u`: `u + 3δ = 5q`, `D = 5q - 7δ ≥ 1`, `4D < 2(q - δ)` (so `h = 2(q - δ) > 4D`),
  for `m = 5q + δ` or `7q - δ`, `q = 2 ^ (r - 3)`, `5 ≤ r`.
* `ambient_and_native_vanishing_m31_k0_inner` / `_mirror`: list 0 there over M31. A member gives
  M-0998's two-block certificate `A³ + X^e B³ = (X^(e+f) A + B) Q` with `f = 2h`; then `Q ≠ 0` (else
  `3 ∣ e`), `deg Q + f ≤ 2h'` forces `h' = h` and `Q = q0` constant, and Theorem K0 excludes it.
* `SingleMonomialResidualAfterK0Bound K`: the residual with this stratum removed as well;
  `interiorThree_of_cwStar_qPrime_cg_k0_and_multi_sublemmas` reduces `MCAChallenge.InteriorThree K` to it
  and `MultiMonomialCanonicalCWBound K`.
-/

namespace InteriorThreeTheoremK0Residual

open Polynomial Finset InteriorThreeCanonicalReduction InteriorThreeTheoremW InteriorThreeBoundaryCW
  InteriorThreeTheoremCWStar InteriorThreeKummerPrimeDivisibility InteriorThreeM31OrbitSizeObstruction
  InteriorThreeLemmaCGBoundary

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

/-- **The `k = 0` cells with `h > 4D` are empty over M31** (inner exponent `m = 5q + δ`). -/
theorem ambient_and_native_vanishing_m31_k0_inner
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hk0 : h = 2 * (2 ^ (r - 3) - δ)) (hD1 : 1 ≤ 5 * 2 ^ (r - 3) - 7 * δ)
    (hD4 : 4 * (5 * 2 ^ (r - 3) - 7 * δ) < h)
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
    set q_oct := 2 ^ (r - 3)
    set m := 5 * q_oct + δ
    set S := D.filter fun x ↦ P.eval x = (Polynomial.C a * X ^ m + R).eval x
    have hSD : S ⊆ D := Finset.filter_subset _ _
    have hS_ge_5q : 5 * q_oct ≤ S.card := by omega
    have hP_ag : ∀ x ∈ S, P.eval x = (Polynomial.C a * X ^ m + R).eval x :=
      fun x hx ↦ (Finset.mem_filter.mp hx).2
    set h₀ := m - S.card
    have hh₀_le_h : h₀ ≤ h := by omega
    have hqh₀ : q_oct + h₀ < 3 * δ := by omega
    obtain ⟨h', A, B, Q, hh'_le_h₀, hAm, hAd, hBd, hB0, hQd, hident⟩ :=
      two_block_cubic_certificate hF hr_lo hr_hi hD_card hD_pow hSD hδ_pos hδ_lt ha hR hP_deg
        hS_ge_5q hP_ag hqh₀
    have hh'_le_h : h' ≤ h := le_trans hh'_le_h₀ hh₀_le_h
    have hndvd : ¬ (3 ∣ (3 * δ - q_oct)) :=
      not_dvd_three_sub_pow_two (by omega : 2 ^ (r - 3) < 3 * δ)
    have hrchar : ringChar F = 2 ^ 31 - 1 := mersenne_ext_ringChar hF
    have hq_le : q_oct ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) (by omega : r - 3 ≤ 28)
    have hBne : B ≠ 0 := fun h0 ↦ hB0 (by simp [h0])
    -- `Q ≠ 0`, else `A ^ 3 = - X ^ e B ^ 3` and `3 ∣ e`
    have hQne : Q ≠ 0 := by
      intro hQ0
      rw [hQ0, mul_zero] at hident
      have heq : (X : F[X]) ^ (3 * δ - q_oct) * B ^ 3 = -(A ^ 3) := by linear_combination hident
      have hdeg := congrArg natDegree heq
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero 3 hBne), natDegree_X_pow,
        natDegree_pow, natDegree_neg, natDegree_pow, hAd] at hdeg
      exact hndvd ⟨h' - B.natDegree, by omega⟩
    have hQdeg := hQd hQne
    have hh' : h' = h := by omega
    have hQ0deg : Q.natDegree = 0 := by omega
    subst hh'
    set q0 := Q.coeff 0 with hq0
    have hQC : Q = C q0 := eq_C_of_natDegree_eq_zero hQ0deg
    have hq0ne : q0 ≠ 0 := fun h0 ↦ hQne (by rw [hQC, h0, map_zero])
    have hident' : A ^ 3 + X ^ (2 * h' - (5 * q_oct - 7 * δ)) * B ^ 3 =
        C q0 * (X ^ (2 * h' - (5 * q_oct - 7 * δ) + 2 * h') * A + B) := by
      rw [show 2 * h' - (5 * q_oct - 7 * δ) = 3 * δ - q_oct by omega,
        show 3 * δ - q_oct + 2 * h' = 3 * δ - q_oct + 4 * (q_oct - δ) by omega]
      rw [hQC] at hident
      linear_combination hident
    exact TheoremK0.theoremK0_ringChar (by omega : 1 ≤ 5 * q_oct - 7 * δ) (by omega)
      (Or.inr (by rw [hrchar]; omega)) hAm hAd hBd hB0 hq0ne hident'
  refine ⟨hno_amb, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
    exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- The mirror `m = 7q - δ` of `ambient_and_native_vanishing_m31_k0_inner`, by Frobenius inversion
(adapted from M-0998). -/
theorem ambient_and_native_vanishing_m31_k0_mirror
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hk0 : h = 2 * (2 ^ (r - 3) - δ)) (hD1 : 1 ≤ 5 * 2 ^ (r - 3) - 7 * δ)
    (hD4 : 4 * (5 * 2 ^ (r - 3) - 7 * δ) < h)
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
  let q_oct : ℕ := 2 ^ (r - 3)
  let K : ℕ := 2 ^ (r - 1)
  have hr1 : K = 4 * q_oct := hr1_raw
  have hr0 : 2 ^ r = 8 * q_oct := hr0_raw
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
  have hinner := ambient_and_native_vanishing_m31_k0_inner hF hr_lo hr_hi
    hD_card hD_pow hδ_pos hδ_lt hh_le hqh hk0 hD1 hD4 hap_ne (conjRev R) (hconjRev_deg R)
  have hno_mirror :
      ¬ ∃ P : F[X], P.natDegree ≤ K ∧
        (5 * q_oct + δ) - h ≤
          (D.filter fun x ↦
            P.eval x = (Polynomial.C a * X ^ (7 * q_oct - δ) + R).eval x).card := by
    rintro ⟨P, hP_deg, hcard⟩
    apply hinner.1
    refine ⟨conjRev P, hconjRev_deg P, le_trans hcard (Finset.card_le_card ?_)⟩
    intro x hx
    obtain ⟨hxD, hx_eq⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
    have hxp_inv : x ^ p = x⁻¹ := (hinv x hxD).2
    have hx8q : x ^ (8 * q_oct) = 1 := by rw [← hr0]; exact hD_pow x hxD
    have hx_ne : x ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow (by omega : 8 * q_oct ≠ 0)] at hx8q
      exact zero_ne_one hx8q
    have hx_mirror_pow : x ^ K * (x ^ (7 * q_oct - δ)) ^ p = x ^ (5 * q_oct + δ) := by
      rw [pow_right_comm, hxp_inv]
      have hprod1 : (x⁻¹) ^ (7 * q_oct - δ) * x ^ (7 * q_oct - δ) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hx_ne, one_pow]
      have hexp_eq : K + 8 * q_oct = (5 * q_oct + δ) + (7 * q_oct - δ) := by omega
      calc x ^ K * (x⁻¹) ^ (7 * q_oct - δ)
          = x ^ K * 1 * (x⁻¹) ^ (7 * q_oct - δ) := by rw [mul_one]
        _ = x ^ K * x ^ (8 * q_oct) * (x⁻¹) ^ (7 * q_oct - δ) := by rw [hx8q]
        _ = x ^ (K + 8 * q_oct) * (x⁻¹) ^ (7 * q_oct - δ) := by rw [← pow_add]
        _ = (x ^ (5 * q_oct + δ) * x ^ (7 * q_oct - δ)) * (x⁻¹) ^ (7 * q_oct - δ) := by
            rw [hexp_eq, pow_add]
        _ = x ^ (5 * q_oct + δ) * ((x⁻¹) ^ (7 * q_oct - δ) * x ^ (7 * q_oct - δ)) := by ring
        _ = x ^ (5 * q_oct + δ) := by rw [hprod1, mul_one]
    rw [hconjRev_eval P hP_deg x hxD, hx_eq]
    have hfrob_add :
        ((Polynomial.C a * X ^ (7 * q_oct - δ) + R).eval x) ^ p =
          a ^ p * (x ^ (7 * q_oct - δ)) ^ p + (R.eval x) ^ p := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      have hm := map_add (frobenius F p) (a * x ^ (7 * q_oct - δ)) (R.eval x)
      change (a * x ^ (7 * q_oct - δ) + R.eval x) ^ p =
        (a * x ^ (7 * q_oct - δ)) ^ p + (R.eval x) ^ p at hm
      rw [hm, mul_pow]
    rw [hfrob_add, mul_add, ← mul_assoc (x ^ K), mul_comm (x ^ K) (a ^ p), mul_assoc (a ^ p),
      hx_mirror_pow, ← hconjRev_eval R hR x hxD]
    dsimp only [q_oct]
    simp
  refine ⟨hno_mirror, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
    exact hno_mirror ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- The `k = 0` stratum with `h > 4D`: `u + 3δ = 5q`, `D = 5q - 7δ ≥ 1`, `4D < 2(q - δ)`. -/
def InSingleK0Stratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u + 3 * δ = 5 * 2 ^ (r - 3) ∧
    1 ≤ 5 * 2 ^ (r - 3) - 7 * δ ∧
    4 * (5 * 2 ^ (r - 3) - 7 * δ) < 2 * (2 ^ (r - 3) - δ)

/-- **Every `k = 0` cell with `h > 4D` is empty over M31:** `¬ IsValidCWComplement D r (X ^ m) γ U`
on `InSingleK0Stratum`, at every dyadic `5 ≤ r ≤ 31`, by Theorem K0. -/
theorem singleMonomialK0Vanishing.{u} (F : Type u) [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2) {r : ℕ} (hr_hi : r ≤ 31) {D : Finset F}
    (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1) {m : ℕ} (γ : F) (U : Finset F)
    (hstrat : InSingleK0Stratum r m U.card) : ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U := by
  obtain ⟨hr5, δ, hδ1, hδ_lt, hm_eq, hu, hD1, hD4⟩ := hstrat
  intro hvalid
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
  let h : ℕ := 2 * (2 ^ (r - 3) - δ)
  have hh_le : h ≤ δ := by omega
  have hqh : 2 ^ (r - 3) + h < 3 * δ := by omega
  have hS_eq : (5 * 2 ^ (r - 3) + δ) - h = S.card := by omega
  rcases hm_eq with rfl | rfl
  · exact (ambient_and_native_vanishing_m31_k0_inner hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh rfl hD1 hD4 one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · exact (ambient_and_native_vanishing_m31_k0_mirror hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh rfl hD1 hD4 one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩

/-- The single-monomial residual after Theorem W, CW*, Lemma Q'_ℓ, the M31 boundary (Lemma CG) and the
`k = 0`, `h > 4D` cells (Theorem K0). -/
def SingleMonomialResidualAfterK0Bound.{u} (K : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ m : ℕ, 5 * 2 ^ (r - 3) ≤ m → m ≤ 7 * 2 ^ (r - 3) → ∀ γ : F,
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r ((X : F[X]) ^ m) γ U ∧
            ¬ InSingleWronskianStratum r m U.card ∧
            ¬ InSingleFullFrobeniusBoundaryStratum r m U.card ∧
            ¬ InSingleQPrimeBoundaryStratum r m U.card ∧
            ¬ InSingleCGBoundaryStratum r m U.card ∧
            ¬ InSingleK0Stratum r m U.card) →
          𝒰.card ≤ K * 2 ^ r

/-- `SingleMonomialResidualAfterK0Bound K` implies `SingleMonomialResidualAfterCGBound K`. -/
theorem singleMonomialResidualAfterCG_of_after_K0.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterK0Bound.{u} K) :
    SingleMonomialResidualAfterCGBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 h𝒰
  refine hRem F hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
  obtain ⟨hvalid, hnotW, hnotCWStar, hnotQP, hnotCG⟩ := h𝒰 U hUm
  exact ⟨hvalid, hnotW, hnotCWStar, hnotQP, hnotCG,
    fun hk ↦ singleMonomialK0Vanishing F hF hr_hi hD_card hD_pow γ U hk hvalid⟩

/-- **`MCAChallenge.InteriorThree K` reduced to the residual after Lemma CG and Theorem K0** and
`MultiMonomialCanonicalCWBound K` (`1 ≤ K ≤ 2 ^ 20`, every dyadic `4 ≤ r ≤ 31`). -/
theorem interiorThree_of_cwStar_qPrime_cg_k0_and_multi_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hRem : SingleMonomialResidualAfterK0Bound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_cwStar_qPrime_cg_and_multi_sublemmas hK_pos hK_cap
    (singleMonomialResidualAfterCG_of_after_K0 hRem) hMulti

end InteriorThreeTheoremK0Residual
