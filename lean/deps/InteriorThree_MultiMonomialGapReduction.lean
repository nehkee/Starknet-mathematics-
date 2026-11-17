import MCAChallenge
import InteriorThree_CanonicalReduction
import InteriorThree_TheoremW
import InteriorThree_BoundaryCW
import InteriorThree_TheoremCWStar

/-!
# Multi-Monomial Unwrapped Silent-Band Vanishing, Cardinality Floors & Critical Uniqueness

Building directly on `InteriorThree_CanonicalReduction`, `InteriorThree_TheoremW`,
`InteriorThree_BoundaryCW`, and `InteriorThree_TheoremCWStar`, the present file attacks the
multi-monomial canonical Weierstrass–`CW*` target `MultiMonomialCanonicalCWBound K` (`2 ≤ d ≤ 3`)
across **every dyadic exponent `4 ≤ r ≤ 31`** (`n = 2 ^ r`, `4q = 2 ^ (r - 1)`):

1. **Section 1 — Unwrapped Silent-Band Product Identity (`silentBand_unwrapped_coeff_eq_zero`):**
   - Proves `coeff_modByMonic_X_pow_sub_one`: for any polynomial `P` with `P.natDegree < 2 * n`
     (`0 < n`) and any `k < n`, `(P %ₘ (X ^ n - 1)).coeff k = P.coeff k + P.coeff (n + k)`.
   - For `w = ∑ j : Fin d, C (b j) * X ^ (m j)` with `∀ j, m j < 2 ^ r` and monic complement
     locator `H_U := ∏ x ∈ U, (X - C x)` (`H_U.natDegree = U.card`), `(w * H_U).natDegree <
     2 ^ r + U.card`, so **zero wrapped-around terms ever reach degree `≥ U.card`**!
   - Deduces `silentBand_unwrapped_coeff_eq_zero`: for EVERY `IsValidCWComplement D r w γ U` and
     every `k` with `2 ^ (r - 1) + U.card < k` and `k < 2 ^ r`, `(w * H_U).coeff k = 0` in ordinary
     unwrapped `F[X]`.

2. **Section 2 — Three Universal Support-Gap Vanishing Theorems (`0` Valid Complements Over Every Field):**
   - **Right-Edge Vanishing (`not_isValidCWComplement_of_card_lt_top_codim`):**
     `U.card < 2 ^ r - m ⟨d - 1, _⟩` forces `(w * H_U).coeff (m ⟨d - 1, _⟩ + U.card) = b ⟨d - 1, _⟩ ≠ 0`.
   - **Left-Edge Vanishing (`not_isValidCWComplement_of_card_lt_bot_offset`):**
     `U.card < m ⟨0, _⟩ - 2 ^ (r - 1)` forces `(w * H_U).coeff (m ⟨0, _⟩) = b ⟨0, _⟩ * H_U.coeff 0 ≠ 0`.
   - **Internal Adjacent-Gap Vanishing (`not_isValidCWComplement_of_card_lt_adjacent_gap`):**
     `U.card < m ⟨j + 1, _⟩ - m ⟨j, _⟩` forces `(w * H_U).coeff (m ⟨j, _⟩ + U.card) = b ⟨j, _⟩ ≠ 0`.
   - Plus field-free `MCAChallenge.NativeListBound ... 0` corollaries (`nativeListBound_zero_of_support_gap`).

3. **Section 3 — Telescoped Multi-Monomial Cardinality Floor (`multiMonomial_card_floor`):**
   - Summing the left-edge, internal adjacent-gap, and right-edge bounds proves unconditionally for
     every `IsValidCWComplement D r w γ U` (`1 ≤ r`):
     **`2 ^ (r - 1) ≤ (d + 1) * U.card`**.
   - Specializes to binomials (`d = 2`: `2 ^ (r - 1) ≤ 3 * U.card`, ruling out agreement `> 5n / 6`)
     and trinomials (`d = 3`: `2 ^ (r - 3) ≤ U.card`, ruling out agreement `> 7n / 8`), together with
     field-free `NativeListBound = 0` corollaries across all `4 ≤ r`.

4. **Section 4 — Binomial (`d = 2`) Silent-Band + `CW*` Self-Reciprocal Zero-Gaps & Critical Uniqueness:**
   - Proves upper-tail (`binomial_locator_coeff_eq_zero_of_upper_silent`) and lower-tail
     (`binomial_locator_coeff_eq_zero_of_lower_silent`) coefficient-vanishing bands on `H_U`.
   - Combines with `CW*` self-reciprocity (`cw_star_locator_coeff_eq_zero_iff`:
     `H_U.coeff i = 0 ↔ H_U.coeff (U.card - i) = 0`) to double the zero-coefficient bands on `H_U`.
   - At the critical adjacent-gap boundary `U.card = m 1 - m 0`:
     - `binomial_critical_gap_const_coeff` pins `H_U.coeff 0 = -b 0 * (b 1)⁻¹` unconditionally;
     - when `U.card < 2 * max (m 0 - 2 ^ (r - 1)) (2 ^ r - m 1)`,
       `binomial_critical_gap_pure_binomial_unique` proves `H_U = X ^ U.card - C (b 0 * (b 1)⁻¹)`
       uniquely (`U₁ = U₂`, hence `≤ 1` valid complement!), AND forces **`(m 1 - m 0) ∣ 2 ^ r`**
       whenever `∀ x ∈ D, x ^ (2 ^ r) = 1` (`0` complements for every non-dyadic gap `m 1 - m 0`!).

5. **Section 5 — Narrowed Multi-Monomial Predicates & Master `MCAChallenge.InteriorThree K` Reductions:**
   - Defines `InConnectedMultiMonomialBand`, `InCriticalBinomialPureStratum`,
     `MultiMonomialConnectedCWBound K`, and `MultiMonomialStrictInteriorCWBound K`.
   - Proves `multiMonomialCanonicalCWBound_of_connectedBand`,
     `multiMonomialCanonicalCWBound_of_strictInterior`,
     `interiorThree_of_singleNonFrobenius_and_connectedMultiMonomial`, and
     `interiorThree_of_singleNonFrobenius_and_strictMultiMonomial`.
-/

namespace InteriorThreeMultiMonomial

open Polynomial Finset InteriorThreeCanonicalReduction InteriorThreeTheoremCWStar

universe u

/-! ## Section 1: Unwrapped Silent-Band Product Identity -/

private lemma coeff_X_pow_mul_ite {R : Type*} [Semiring R] (P : R[X]) :
    ∀ (n d : ℕ), ((X : R[X]) ^ n * P).coeff d = if n ≤ d then P.coeff (d - n) else 0
  | 0, d => by simp
  | n + 1, 0 => by
    rw [pow_succ', mul_assoc, Polynomial.coeff_X_mul_zero]
    simp
  | n + 1, d + 1 => by
    rw [pow_succ', mul_assoc, Polynomial.coeff_X_mul, coeff_X_pow_mul_ite P n d]
    by_cases h : n ≤ d
    · have h1 : n + 1 ≤ d + 1 := Nat.succ_le_succ h
      simp [h, h1]
    · have h1 : ¬ (n + 1 ≤ d + 1) := fun hle => h (Nat.le_of_succ_le_succ hle)
      simp [h, h1]

/-- For every `0 < n`, `(X : F[X]) ^ n - 1` is monic of `natDegree = n` and `degree = n`. -/
theorem monic_and_natDegree_X_pow_sub_one {F : Type*} [Field F] {n : ℕ} (hn : 0 < n) :
    ((X : F[X]) ^ n - 1).Monic ∧
    ((X : F[X]) ^ n - 1).natDegree = n ∧
    ((X : F[X]) ^ n - 1).degree = (n : WithBot ℕ) := by
  set M : F[X] := (X : F[X]) ^ n - 1
  have hle : M.natDegree ≤ n := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact Polynomial.natDegree_X_pow_le n
    · simp
  have hcn : M.coeff n = 1 := by
    dsimp [M]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
    have hne : n ≠ 0 := hn.ne'
    simp only [↓reduceIte, hne, sub_zero]
  have hge : n ≤ M.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcn]; exact one_ne_zero)
  have hdeg : M.natDegree = n := le_antisymm hle hge
  have hmonic : M.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hcn]
  have hdeg_wb : M.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
  exact ⟨hmonic, hdeg, hdeg_wb⟩

private lemma truncRange_coeff_and_degree {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (f : ℕ → F) :
    let S : F[X] := ∑ i ∈ Finset.range n, Polynomial.C (f i) * X ^ i
    (∀ d : ℕ, S.coeff d = if d < n then f d else 0) ∧
    S.degree < (n : WithBot ℕ) := by
  set S : F[X] := ∑ i ∈ Finset.range n, Polynomial.C (f i) * X ^ i
  have hcoeff : ∀ d : ℕ, S.coeff d = if d < n then f d else 0 := by
    intro d
    dsimp [S]
    rw [Polynomial.finsetSum_coeff]
    by_cases hd : d < n
    · simp only [hd, ↓reduceIte]
      rw [Finset.sum_eq_single d]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp only [↓reduceIte, mul_one]
      · intro i _ hid
        have hdi : d ≠ i := hid.symm
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp only [hdi, ↓reduceIte, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hd) hnot
    · simp only [hd, ↓reduceIte]
      rw [Finset.sum_eq_zero]
      intro i hi
      have hi_lt : i < n := Finset.mem_range.mp hi
      have hdi : d ≠ i := by omega
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp only [hdi, ↓reduceIte, mul_zero]
  have hdeg : S.degree < (n : WithBot ℕ) := by
    rcases eq_or_ne S 0 with h0 | hne
    · rw [h0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe n
    · have hnd_le : S.natDegree ≤ n - 1 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd_gt
        have hnot_lt : ¬ (d < n) := by omega
        rw [hcoeff d]
        simp only [hnot_lt, ↓reduceIte]
      rw [Polynomial.degree_eq_natDegree hne]
      exact WithBot.coe_lt_coe.mpr (Nat.lt_of_le_of_lt hnd_le (Nat.sub_lt hn Nat.one_pos))
  exact ⟨hcoeff, hdeg⟩

/-- **Cyclic Reduction Formula Modulo `X ^ n - 1` (`coeff_modByMonic_X_pow_sub_one`):**
For any polynomial `P : F[X]` with `P.natDegree < 2 * n` (`0 < n`) and any `k < n`,
`(P %ₘ (X ^ n - 1)).coeff k = P.coeff k + P.coeff (n + k)`. -/
theorem coeff_modByMonic_X_pow_sub_one {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (P : F[X]) (hP : P.natDegree < 2 * n) {k : ℕ} (hk : k < n) :
    (P %ₘ ((X : F[X]) ^ n - 1)).coeff k = P.coeff k + P.coeff (n + k) := by
  obtain ⟨hMm, _, hMdeg⟩ := monic_and_natDegree_X_pow_sub_one (F := F) hn
  set M : F[X] := (X : F[X]) ^ n - 1
  obtain ⟨hR_coeff, hR_deg⟩ :=
    truncRange_coeff_and_degree hn (fun i => P.coeff i + P.coeff (n + i))
  obtain ⟨hQ_coeff, _⟩ :=
    truncRange_coeff_and_degree hn (fun i => P.coeff (n + i))
  set R_rem : F[X] := ∑ i ∈ Finset.range n, Polynomial.C (P.coeff i + P.coeff (n + i)) * X ^ i
  set Q_quot : F[X] := ∑ i ∈ Finset.range n, Polynomial.C (P.coeff (n + i)) * X ^ i
  have hR_c : ∀ d : ℕ, R_rem.coeff d = if d < n then P.coeff d + P.coeff (n + d) else 0 :=
    hR_coeff
  have hQ_c : ∀ d : ℕ, Q_quot.coeff d = if d < n then P.coeff (n + d) else 0 :=
    hQ_coeff
  have hdecomp : P = R_rem + M * Q_quot := by
    ext d
    have hMQ : M * Q_quot = (X : F[X]) ^ n * Q_quot - Q_quot := by
      dsimp [M]; ring
    rw [Polynomial.coeff_add, hMQ, Polynomial.coeff_sub, coeff_X_pow_mul_ite, hR_c d, hQ_c d]
    by_cases hd : d < n
    · have hnot_le : ¬ (n ≤ d) := by omega
      simp only [hd, hnot_le, ↓reduceIte]
      ring
    · have hle : n ≤ d := by omega
      simp only [hd, hle, ↓reduceIte, zero_add, sub_zero]
      rw [hQ_c (d - n)]
      by_cases hd2 : d - n < n
      · simp only [hd2, ↓reduceIte]
        congr 1; omega
      · simp only [hd2, ↓reduceIte]
        have hlt_d : P.natDegree < d := lt_of_lt_of_le hP (by omega : 2 * n ≤ d)
        exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt_d
  have hdiv := Polynomial.modByMonic_add_div P M
  have hdiff_eq : P %ₘ M - R_rem = M * (Q_quot - P /ₘ M) := by
    calc P %ₘ M - R_rem
        = (P - M * (P /ₘ M)) - R_rem := by rw [eq_sub_of_add_eq hdiv]
      _ = (R_rem + M * Q_quot - M * (P /ₘ M)) - R_rem := by rw [← hdecomp]
      _ = M * (Q_quot - P /ₘ M) := by ring
  have hQ_sub_zero : Q_quot - P /ₘ M = 0 := by
    by_contra hne
    have hmod_lt : (P %ₘ M).degree < (n : WithBot ℕ) := by
      rw [← hMdeg]
      exact Polynomial.degree_modByMonic_lt P hMm
    have hlhs_lt : (P %ₘ M - R_rem).degree < (n : WithBot ℕ) :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hmod_lt hR_deg)
    have hrhs_ge : (n : WithBot ℕ) ≤ (M * (Q_quot - P /ₘ M)).degree := by
      rw [Polynomial.degree_mul, hMdeg]
      exact le_add_of_nonneg_right (Polynomial.zero_le_degree_iff.mpr hne)
    rw [hdiff_eq] at hlhs_lt
    exact not_lt_of_ge hrhs_ge hlhs_lt
  have hrem_eq : P %ₘ M = R_rem := by
    apply sub_eq_zero.mp
    rw [hdiff_eq, hQ_sub_zero, mul_zero]
  rw [hrem_eq, hR_c k]
  simp only [hk, ↓reduceIte]

/-- Basic degree, monicity, leading-coefficient, and constant-term package for the monic locator
`H_U := ∏ x ∈ U, (X - C x)`. -/
theorem locator_monic_natDegree_and_coeff_zero {F : Type*} [Field F] [DecidableEq F]
    (U : Finset F) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    H_U.Monic ∧
    H_U.natDegree = U.card ∧
    H_U.coeff U.card = 1 ∧
    ((0 : F) ∉ U → H_U.coeff 0 ≠ 0) ∧
    (∀ z : F, z ∈ U ↔ H_U.eval z = 0) := by
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  have hHm : H_U.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)
  have hHd : H_U.natDegree = U.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ ↦ Polynomial.monic_X_sub_C x)]
    simp
  have hHtop : H_U.coeff U.card = 1 := by
    rw [← hHd]; exact hHm.leadingCoeff
  have heval_iff : ∀ z : F, z ∈ U ↔ H_U.eval z = 0 := by
    intro z
    rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
    exact ⟨fun hz => ⟨z, hz, rfl⟩, fun ⟨x, hx, hzx⟩ => hzx ▸ hx⟩
  have hc0_ne : (0 : F) ∉ U → H_U.coeff 0 ≠ 0 := by
    intro h0_not h0_eq
    have hev0 : H_U.eval 0 = H_U.coeff 0 := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
      simp
    exact h0_not ((heval_iff 0).mpr (hev0.trans h0_eq))
  exact ⟨hHm, hHd, hHtop, hc0_ne, heval_iff⟩

/-- Explicit coefficient expansion of `(∑ j : Fin d, C (b j) * X ^ (m j)) * H`. -/
theorem sum_monomial_mul_coeff {F : Type*} [Field F] {d : ℕ}
    (m : Fin d → ℕ) (b : Fin d → F) (H : F[X]) (k : ℕ) :
    ((∑ j : Fin d, Polynomial.C (b j) * (X : F[X]) ^ (m j)) * H).coeff k =
      ∑ j : Fin d, if m j ≤ k then b j * H.coeff (k - m j) else 0 := by
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [mul_assoc, Polynomial.coeff_C_mul, coeff_X_pow_mul_ite]
  split_ifs <;> ring

private lemma sum_monomial_natDegree_le_pred {F : Type*} [Field F] {d N : ℕ}
    (hN : 0 < N) (m : Fin d → ℕ) (b : Fin d → F) (hm : ∀ j : Fin d, m j < N) :
    (∑ j : Fin d, Polynomial.C (b j) * (X : F[X]) ^ (m j)).natDegree ≤ N - 1 := by
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun j _ ↦ ?_⟩
  have hmj := hm j
  exact le_trans (Polynomial.natDegree_C_mul_le _ _)
    (le_trans (Polynomial.natDegree_X_pow_le (m j)) (by omega))

/-- **No-Wraparound Identity Above `U.card` (`unwrapped_mod_coeff_eq`):**
Whenever `∀ j : Fin d, m j < 2 ^ r` and `U.card ≤ k` with `k < 2 ^ r`, no wrapped-around term of
`w * H_U` modulo `X ^ (2 ^ r) - 1` reaches degree `k` (`(w * H_U).natDegree < 2 ^ r + U.card`), so
`((w * H_U) %ₘ (X ^ (2 ^ r) - 1)).coeff k = (w * H_U).coeff k`. -/
theorem unwrapped_mod_coeff_eq {F : Type*} [Field F] [DecidableEq F]
    {r d : ℕ} {m : Fin d → ℕ} (hm_lt : ∀ j : Fin d, m j < 2 ^ r)
    (b : Fin d → F) (U : Finset F) {k : ℕ} (hk_lo : U.card ≤ k) (hk_hi : k < 2 ^ r) :
    let w : F[X] := ∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    ((w * H_U) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)).coeff k = (w * H_U).coeff k := by
  intro w H_U
  have hn : 0 < 2 ^ r := Nat.pos_of_ne_zero (by positivity)
  obtain ⟨_, hHd, _, _, _⟩ := locator_monic_natDegree_and_coeff_zero U
  have hHd' : H_U.natDegree = U.card := hHd
  have hw_le : w.natDegree ≤ 2 ^ r - 1 := sum_monomial_natDegree_le_pred hn m b hm_lt
  have hwH_lt : (w * H_U).natDegree < 2 ^ r + U.card := by
    have hle : (w * H_U).natDegree ≤ w.natDegree + H_U.natDegree := Polynomial.natDegree_mul_le
    rw [hHd'] at hle
    omega
  have hwH_lt2 : (w * H_U).natDegree < 2 * 2 ^ r := by omega
  rw [coeff_modByMonic_X_pow_sub_one hn (w * H_U) hwH_lt2 hk_hi]
  have hwrap_zero : (w * H_U).coeff (2 ^ r + k) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (w * H_U).natDegree < 2 ^ r + k)
  rw [hwrap_zero, add_zero]

/-- **Unwrapped Silent-Band Product Identity (`silentBand_unwrapped_coeff_eq_zero`):**
For any `U` satisfying `IsValidCWComplement D r w γ U` with
`w = ∑ j : Fin d, C (b j) * X ^ (m j)` and `∀ j : Fin d, m j < 2 ^ r`, for EVERY `k` in the silent
band `2 ^ (r - 1) + U.card < k` and `k < 2 ^ r`:
1. `((w * H_U).coeff k) = 0` in ordinary unwrapped `F[X]` (zero modular wraparound!), and
2. `∑ j : Fin d, (if m j ≤ k then b j * H_U.coeff (k - m j) else 0) = 0`. -/
theorem silentBand_unwrapped_coeff_eq_zero {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r d : ℕ} {m : Fin d → ℕ} (hm_lt : ∀ j : Fin d, m j < 2 ^ r)
    {b : Fin d → F} {γ : F} {U : Finset F}
    (hvalid : IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U)
    {k : ℕ} (hk_lo : 2 ^ (r - 1) + U.card < k) (hk_hi : k < 2 ^ r) :
    let w : F[X] := ∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    (w * H_U).coeff k = 0 ∧
    (∑ j : Fin d, if m j ≤ k then b j * H_U.coeff (k - m j) else 0) = 0 := by
  obtain ⟨_, _, _, _, _, hB_van, _⟩ := hvalid
  have hmod_zero := hB_van k hk_lo hk_hi
  have hu_le_k : U.card ≤ k := le_of_lt (lt_of_le_of_lt (Nat.le_add_left _ _) hk_lo)
  have hunwrap := unwrapped_mod_coeff_eq hm_lt b U hu_le_k hk_hi
  have hwH_zero : ((∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) *
      ∏ x ∈ U, (X - Polynomial.C x)).coeff k = 0 := by
    rwa [← hunwrap]
  refine ⟨hwH_zero, ?_⟩
  rw [← sum_monomial_mul_coeff]
  exact hwH_zero

/-! ## Section 2: Three Universal Support-Gap Vanishing Theorems (Over Every Field) -/

/-- Pure-field right-edge silent-band obstruction: if `U.card < 2 ^ r - m ⟨d - 1, _⟩`, the silent
band cannot vanish at `k = m ⟨d - 1, _⟩ + U.card` over **any** field `F`. -/
theorem false_of_silentBand_lt_top_codim {F : Type*} [Field F] [DecidableEq F]
    {r d : ℕ} (hd : 0 < d) {m : Fin d → ℕ} {b : Fin d → F}
    (hm_mono : StrictMono m)
    (hm_range : ∀ j : Fin d, 2 ^ (r - 1) < m j ∧ m j < 2 ^ r)
    (hb_ne : ∀ j : Fin d, b j ≠ 0)
    {U : Finset F}
    (hvan : ∀ k : ℕ, 2 ^ (r - 1) + U.card < k → k < 2 ^ r →
      (((∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) *
        ∏ x ∈ U, (X - Polynomial.C x)) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)).coeff k = 0)
    (hu_lt : U.card < 2 ^ r - m ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩) :
    False := by
  let j_top : Fin d := ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩
  change U.card < 2 ^ r - m j_top at hu_lt
  set k : ℕ := m j_top + U.card
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  obtain ⟨_, hHd, hHtop, _, _⟩ := locator_monic_natDegree_and_coeff_zero U
  have hHd' : H_U.natDegree = U.card := hHd
  have hHtop' : H_U.coeff U.card = 1 := hHtop
  have htop_lo : 2 ^ (r - 1) < m j_top := (hm_range j_top).1
  have htop_hi : m j_top < 2 ^ r := (hm_range j_top).2
  have hk_lo : 2 ^ (r - 1) + U.card < k := by omega
  have hu_le_k : U.card ≤ k := by omega
  have hk_hi : k < 2 ^ r := by omega
  have hmod0 := hvan k hk_lo hk_hi
  rw [unwrapped_mod_coeff_eq (fun j => (hm_range j).2) b U hu_le_k hk_hi,
    sum_monomial_mul_coeff] at hmod0
  rw [Finset.sum_eq_single j_top] at hmod0
  · have hm_le : m j_top ≤ k := by omega
    have hsub : k - m j_top = U.card := by omega
    simp only [hm_le, ↓reduceIte, hsub] at hmod0
    change b j_top * H_U.coeff U.card = 0 at hmod0
    rw [hHtop', mul_one] at hmod0
    exact hb_ne j_top hmod0
  · intro j _ hj_ne
    have hj_lt : j < j_top := by
      apply Fin.mk_lt_mk.mpr
      have := j.2
      have hne_val : j.1 ≠ d - 1 := fun heq => hj_ne (Fin.ext heq)
      omega
    have hmj_lt : m j < m j_top := hm_mono hj_lt
    by_cases hle : m j ≤ k
    · simp only [hle, ↓reduceIte]
      have hcoeff0 : H_U.coeff (k - m j) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hHd']; omega)
      change b j * H_U.coeff (k - m j) = 0
      rw [hcoeff0, mul_zero]
    · simp only [hle, ↓reduceIte]
  · intro hnot
    exact absurd (Finset.mem_univ j_top) hnot

/-- Pure-field left-edge silent-band obstruction: if `(0 : F) ∉ U` (or `H_U.coeff 0 ≠ 0`) and
`U.card < m ⟨0, _⟩ - 2 ^ (r - 1)`, the silent band cannot vanish at `k = m ⟨0, _⟩`. -/
theorem false_of_silentBand_lt_bot_offset {F : Type*} [Field F] [DecidableEq F]
    {r d : ℕ} (hd : 0 < d) {m : Fin d → ℕ} {b : Fin d → F}
    (hm_mono : StrictMono m)
    (hm_range : ∀ j : Fin d, 2 ^ (r - 1) < m j ∧ m j < 2 ^ r)
    (hb_ne : ∀ j : Fin d, b j ≠ 0)
    {U : Finset F}
    (hc0_ne : (∏ x ∈ U, (X - Polynomial.C x)).coeff 0 ≠ 0)
    (hvan : ∀ k : ℕ, 2 ^ (r - 1) + U.card < k → k < 2 ^ r →
      (((∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) *
        ∏ x ∈ U, (X - Polynomial.C x)) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)).coeff k = 0)
    (hu_lt : U.card < m ⟨0, hd⟩ - 2 ^ (r - 1)) :
    False := by
  let j_bot : Fin d := ⟨0, hd⟩
  change U.card < m j_bot - 2 ^ (r - 1) at hu_lt
  set k : ℕ := m j_bot
  have hbot_lo : 2 ^ (r - 1) < m j_bot := (hm_range j_bot).1
  have hbot_hi : m j_bot < 2 ^ r := (hm_range j_bot).2
  have hk_lo : 2 ^ (r - 1) + U.card < k := by omega
  have hu_le_k : U.card ≤ k := le_of_lt (lt_of_le_of_lt (Nat.le_add_left _ _) hk_lo)
  have hmod0 := hvan k hk_lo hbot_hi
  rw [unwrapped_mod_coeff_eq (fun j => (hm_range j).2) b U hu_le_k hbot_hi,
    sum_monomial_mul_coeff] at hmod0
  rw [Finset.sum_eq_single j_bot] at hmod0
  · have hm_le : m j_bot ≤ k := le_rfl
    have hsub : k - m j_bot = 0 := Nat.sub_self _
    simp only [hm_le, ↓reduceIte, hsub] at hmod0
    exact mul_ne_zero (hb_ne j_bot) hc0_ne hmod0
  · intro j _ hj_ne
    have hj_gt : j_bot < j := by
      apply Fin.mk_lt_mk.mpr
      have hne_val : j.1 ≠ 0 := fun heq => hj_ne (Fin.ext heq)
      omega
    have hmj_gt : k < m j := hm_mono hj_gt
    have hnot_le : ¬ (m j ≤ k) := by omega
    simp only [hnot_le, ↓reduceIte]
  · intro hnot
    exact absurd (Finset.mem_univ j_bot) hnot

/-- Pure-field internal adjacent-gap silent-band obstruction: if
`U.card < m ⟨j + 1, hj⟩ - m ⟨j, _⟩`, the silent band cannot vanish at `k = m ⟨j, _⟩ + U.card`. -/
theorem false_of_silentBand_lt_adjacent_gap {F : Type*} [Field F] [DecidableEq F]
    {r d : ℕ} {m : Fin d → ℕ} {b : Fin d → F}
    (hm_mono : StrictMono m)
    (hm_range : ∀ i : Fin d, 2 ^ (r - 1) < m i ∧ m i < 2 ^ r)
    (hb_ne : ∀ i : Fin d, b i ≠ 0)
    {U : Finset F}
    (hvan : ∀ k : ℕ, 2 ^ (r - 1) + U.card < k → k < 2 ^ r →
      (((∑ i : Fin d, Polynomial.C (b i) * X ^ (m i)) *
        ∏ x ∈ U, (X - Polynomial.C x)) %ₘ ((X : F[X]) ^ (2 ^ r) - 1)).coeff k = 0)
    {j : ℕ} (hj : j + 1 < d)
    (hu_lt : U.card < m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩) :
    False := by
  let idx_lo : Fin d := ⟨j, Nat.lt_of_succ_lt hj⟩
  let idx_hi : Fin d := ⟨j + 1, hj⟩
  change U.card < m idx_hi - m idx_lo at hu_lt
  set k : ℕ := m idx_lo + U.card
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  obtain ⟨_, hHd, hHtop, _, _⟩ := locator_monic_natDegree_and_coeff_zero U
  have hHd' : H_U.natDegree = U.card := hHd
  have hHtop' : H_U.coeff U.card = 1 := hHtop
  have hlo_gt : 2 ^ (r - 1) < m idx_lo := (hm_range idx_lo).1
  have hlo_lt_hi : m idx_lo < m idx_hi := hm_mono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
  have hhi_lt : m idx_hi < 2 ^ r := (hm_range idx_hi).2
  have hk_lo : 2 ^ (r - 1) + U.card < k := by omega
  have hu_le_k : U.card ≤ k := by omega
  have hk_lt_hi : k < m idx_hi := by omega
  have hk_hi : k < 2 ^ r := by omega
  have hmod0 := hvan k hk_lo hk_hi
  rw [unwrapped_mod_coeff_eq (fun i => (hm_range i).2) b U hu_le_k hk_hi,
    sum_monomial_mul_coeff] at hmod0
  rw [Finset.sum_eq_single idx_lo] at hmod0
  · have hm_le : m idx_lo ≤ k := by omega
    have hsub : k - m idx_lo = U.card := by omega
    simp only [hm_le, ↓reduceIte, hsub] at hmod0
    change b idx_lo * H_U.coeff U.card = 0 at hmod0
    rw [hHtop', mul_one] at hmod0
    exact hb_ne idx_lo hmod0
  · intro i _ hi_ne
    by_cases hij : i.1 < j
    · have hmi_lt : m i < m idx_lo := hm_mono (Fin.mk_lt_mk.mpr hij)
      by_cases hle : m i ≤ k
      · simp only [hle, ↓reduceIte]
        have hcoeff0 : H_U.coeff (k - m i) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hHd']; omega)
        change b i * H_U.coeff (k - m i) = 0
        rw [hcoeff0, mul_zero]
      · simp only [hle, ↓reduceIte]
    · have hij_ge : j + 1 ≤ i.1 := by
        have hne_val : i.1 ≠ j := fun heq => hi_ne (Fin.ext heq)
        omega
      have hmi_ge : m idx_hi ≤ m i := hm_mono.monotone (Fin.mk_le_mk.mpr hij_ge)
      have hnot_le : ¬ (m i ≤ k) := by omega
      simp only [hnot_le, ↓reduceIte]
  · intro hnot
    exact absurd (Finset.mem_univ idx_lo) hnot

/-- **1. Right-Edge Support-Gap Vanishing (`not_isValidCWComplement_of_card_lt_top_codim`):**
For any canonical high configuration `IsCanonicalHighConfig r d m b`, if
`U.card < 2 ^ r - m ⟨d - 1, _⟩`, then `¬ IsValidCWComplement D r w γ U`. -/
theorem not_isValidCWComplement_of_card_lt_top_codim {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r d : ℕ} {m : Fin d → ℕ} {b : Fin d → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r d m b)
    (hu_lt : U.card < 2 ^ r - m ⟨d - 1, Nat.sub_lt hcfg.1 Nat.one_pos⟩) :
    ¬ IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U := by
  intro hvalid
  obtain ⟨_, _, _, _, _, hB_van, _⟩ := hvalid
  exact false_of_silentBand_lt_top_codim hcfg.1 hcfg.2.2.1 hcfg.2.2.2.1 hcfg.2.2.2.2.1 hB_van hu_lt

/-- **2. Left-Edge Support-Gap Vanishing (`not_isValidCWComplement_of_card_lt_bot_offset`):**
For any canonical high configuration `IsCanonicalHighConfig r d m b`, if
`U.card < m ⟨0, _⟩ - 2 ^ (r - 1)`, then `¬ IsValidCWComplement D r w γ U`. -/
theorem not_isValidCWComplement_of_card_lt_bot_offset {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r d : ℕ} {m : Fin d → ℕ} {b : Fin d → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r d m b)
    (hu_lt : U.card < m ⟨0, hcfg.1⟩ - 2 ^ (r - 1)) :
    ¬ IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U := by
  intro hvalid
  obtain ⟨_, _, hc0_pow, _, _, hB_van, _⟩ := hvalid
  have hc0_ne : (∏ x ∈ U, (X - Polynomial.C x)).coeff 0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at hc0_pow
    exact zero_ne_one hc0_pow
  exact false_of_silentBand_lt_bot_offset hcfg.1 hcfg.2.2.1 hcfg.2.2.2.1 hcfg.2.2.2.2.1
    hc0_ne hB_van hu_lt

/-- **3. Internal Adjacent-Gap Vanishing (`not_isValidCWComplement_of_card_lt_adjacent_gap`):**
For any canonical high configuration `IsCanonicalHighConfig r d m b` and any `j + 1 < d`, if
`U.card < m ⟨j + 1, hj⟩ - m ⟨j, _⟩`, then `¬ IsValidCWComplement D r w γ U`. -/
theorem not_isValidCWComplement_of_card_lt_adjacent_gap {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r d : ℕ} {m : Fin d → ℕ} {b : Fin d → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r d m b)
    {j : ℕ} (hj : j + 1 < d)
    (hu_lt : U.card < m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩) :
    ¬ IsValidCWComplement D r (∑ i : Fin d, Polynomial.C (b i) * X ^ (m i)) γ U := by
  intro hvalid
  obtain ⟨_, _, _, _, _, hB_van, _⟩ := hvalid
  exact false_of_silentBand_lt_adjacent_gap hcfg.2.2.1 hcfg.2.2.2.1 hcfg.2.2.2.2.1 hB_van hj hu_lt

/-- **Field-Free `NativeListBound = 0` Support-Gap Vanishing (`nativeListBound_zero_of_support_gap`):**
Over **every** field `F` (`4 ≤ r`, `D.card = 2 ^ r`, `∀ x ∈ D, x ^ (2 ^ r) = 1`), for any
`w = ∑ j : Fin d, C (b j) * X ^ (m j) + R` (`1 ≤ d`, `StrictMono m`, `2 ^ (r - 1) < m j < 2 ^ r`,
`b j ≠ 0`, `R.natDegree ≤ 2 ^ (r - 1)`) and agreement threshold `A` (`5 * 2 ^ (r - 3) ≤ A ≤ 2 ^ r`),
whenever `2 ^ r - A` is strictly below the left-edge offset, right-edge codimension, or any internal
adjacent exponent gap, **zero** ambient or native circle codewords agree with `w` on `A` points! -/
theorem nativeListBound_zero_of_support_gap {F : Type*} [Field F] [DecidableEq F]
    {r d : ℕ} (hr : 4 ≤ r) (hd : 0 < d)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {m : Fin d → ℕ} {b : Fin d → F} (R : F[X])
    (hm_mono : StrictMono m)
    (hm_range : ∀ j : Fin d, 2 ^ (r - 1) < m j ∧ m j < 2 ^ r)
    (hb_ne : ∀ j : Fin d, b j ≠ 0)
    (hR : R.natDegree ≤ 2 ^ (r - 1))
    {A : ℕ} (hA_lo : 5 * 2 ^ (r - 3) ≤ A) (hA_hi : A ≤ 2 ^ r)
    (hgap : 2 ^ r - A < m ⟨0, hd⟩ - 2 ^ (r - 1) ∨
            2 ^ r - A < 2 ^ r - m ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ ∨
            ∃ (j : ℕ) (hj : j + 1 < d),
              2 ^ r - A < m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        A ≤ (D.filter fun x ↦
          P.eval x = (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) A
      (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j) + R) 0 := by
  set w_hi : F[X] := ∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)
  have hno_amb :
      ¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        A ≤ (D.filter fun x ↦ P.eval x = (w_hi + R).eval x).card := by
    rintro ⟨P, hP_deg, hS_ge⟩
    set S : Finset F := D.filter fun x ↦ P.eval x = (w_hi + R).eval x
    have hSD : S ⊆ D := Finset.filter_subset _ D
    have hS_5q : 5 * 2 ^ (r - 3) ≤ S.card := le_trans hA_lo hS_ge
    set U : Finset F := D \ S
    have hU_le : U.card ≤ 2 ^ r - A := by
      have hsdiff : U.card + S.card = 2 ^ r :=
        (Finset.card_sdiff_add_card_eq_card hSD).trans hD_card
      omega
    have hPR_deg : (P - R).natDegree ≤ 2 ^ (r - 1) :=
      le_trans (Polynomial.natDegree_sub_le P R) (max_le hP_deg hR)
    have hPR_ag : ∀ x ∈ S, (P - R).eval x = w_hi.eval x := by
      intro x hxS
      have hx_eq := (Finset.mem_filter.mp hxS).2
      rw [Polynomial.eval_sub, hx_eq, Polynomial.eval_add, add_sub_cancel_right]
    obtain ⟨hiff, hband_iff, _, _⟩ := weierstrass_silent_band_iff hr hD_card hD_pow hSD hS_5q w_hi
    have hB_van := hband_iff.mp (hiff.mp ⟨P - R, hPR_deg, hPR_ag⟩)
    obtain ⟨h0_notD, _, _, _, _⟩ := dyadicSubgroup_properties hD_card hD_pow
    have h0_notU : (0 : F) ∉ U := fun h0 => h0_notD (Finset.sdiff_subset h0)
    obtain ⟨_, _, _, hc0_fn, _⟩ := locator_monic_natDegree_and_coeff_zero U
    rcases hgap with hbot | htop | ⟨j, hj, hadj⟩
    · exact false_of_silentBand_lt_bot_offset hd hm_mono hm_range hb_ne (hc0_fn h0_notU) hB_van
        (lt_of_le_of_lt hU_le hbot)
    · exact false_of_silentBand_lt_top_codim hd hm_mono hm_range hb_ne hB_van
        (lt_of_le_of_lt hU_le htop)
    · exact false_of_silentBand_lt_adjacent_gap hm_mono hm_range hb_ne hB_van hj
        (lt_of_le_of_lt hU_le hadj)
  refine ⟨hno_amb, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hPm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hPm
    exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-! ## Section 3: Telescoped Multi-Monomial Cardinality Floor (`multiMonomial_card_floor`) -/

private lemma prefix_offset_le_mul {d u B : ℕ} {m : Fin d → ℕ}
    (hm_mono : StrictMono m)
    (hm_gt : ∀ j : Fin d, B < m j)
    (hbot : ∀ hd : 0 < d, m ⟨0, hd⟩ - B ≤ u)
    (hadj : ∀ (j : ℕ) (hj : j + 1 < d), m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ u) :
    ∀ (k : ℕ) (hk : k < d), m ⟨k, hk⟩ - B ≤ (k + 1) * u
  | 0, hk => by
    rw [Nat.zero_add, one_mul]
    exact hbot hk
  | k + 1, hk1 => by
    have hk : k < d := Nat.lt_of_succ_lt hk1
    have hih := prefix_offset_le_mul hm_mono hm_gt hbot hadj k hk
    have hstep := hadj k hk1
    have hlt : m ⟨k, hk⟩ < m ⟨k + 1, hk1⟩ := hm_mono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
    have hB_lt : B < m ⟨k, hk⟩ := hm_gt ⟨k, hk⟩
    have hmul : (k + 1 + 1) * u = (k + 1) * u + u := by ring
    omega

/-- Pure-arithmetic telescoping lemma: if `B < m 0 < ... < m (d - 1) < 2 * B` and all `d + 1`
consecutive intervals have length `≤ u`, then `B ≤ (d + 1) * u`. -/
theorem telescope_interval_floor {r d u : ℕ} (hr : 1 ≤ r) (hd : 0 < d) {m : Fin d → ℕ}
    (hm_mono : StrictMono m)
    (hm_range : ∀ j : Fin d, 2 ^ (r - 1) < m j ∧ m j < 2 ^ r)
    (hbot : m ⟨0, hd⟩ - 2 ^ (r - 1) ≤ u)
    (hadj : ∀ (j : ℕ) (hj : j + 1 < d), m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ u)
    (htop : 2 ^ r - m ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ ≤ u) :
    2 ^ (r - 1) ≤ (d + 1) * u := by
  have h2r : 2 ^ r = 2 ^ (r - 1) + 2 ^ (r - 1) := by
    have he : r = (r - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    ring
  have hpref := prefix_offset_le_mul hm_mono (fun j => (hm_range j).1) (fun _ => hbot) hadj
    (d - 1) (Nat.sub_lt hd Nat.one_pos)
  have hd_sub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  rw [hd_sub] at hpref
  have hlast_lo := (hm_range ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩).1
  have hlast_hi := (hm_range ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩).2
  have hmul : (d + 1) * u = d * u + u := by ring
  omega

/-- **Telescoped Multi-Monomial Cardinality Floor (`multiMonomial_card_floor`):**
For EVERY `1 ≤ r` (hence all `4 ≤ r ≤ 31`), EVERY canonical configuration
`IsCanonicalHighConfig r d m b`, and EVERY valid complement
`IsValidCWComplement D r (∑ j : Fin d, C (b j) * X ^ (m j)) γ U`:
1. `m ⟨0, _⟩ - 2 ^ (r - 1) ≤ U.card`,
2. `∀ j (hj : j + 1 < d), m ⟨j + 1, hj⟩ - m ⟨j, _⟩ ≤ U.card`,
3. `2 ^ r - m ⟨d - 1, _⟩ ≤ U.card`, and
4. **`2 ^ (r - 1) ≤ (d + 1) * U.card`**! -/
theorem multiMonomial_card_floor {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r d : ℕ} (hr : 1 ≤ r) {m : Fin d → ℕ} {b : Fin d → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r d m b)
    (hvalid : IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U) :
    m ⟨0, hcfg.1⟩ - 2 ^ (r - 1) ≤ U.card ∧
    (∀ (j : ℕ) (hj : j + 1 < d), m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ U.card) ∧
    2 ^ r - m ⟨d - 1, Nat.sub_lt hcfg.1 Nat.one_pos⟩ ≤ U.card ∧
    2 ^ (r - 1) ≤ (d + 1) * U.card := by
  have hbot : m ⟨0, hcfg.1⟩ - 2 ^ (r - 1) ≤ U.card := by
    by_contra hlt
    exact not_isValidCWComplement_of_card_lt_bot_offset hcfg (Nat.lt_of_not_ge hlt) hvalid
  have hadj : ∀ (j : ℕ) (hj : j + 1 < d),
      m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ U.card := by
    intro j hj
    by_contra hlt
    exact not_isValidCWComplement_of_card_lt_adjacent_gap hcfg hj (Nat.lt_of_not_ge hlt) hvalid
  have htop : 2 ^ r - m ⟨d - 1, Nat.sub_lt hcfg.1 Nat.one_pos⟩ ≤ U.card := by
    by_contra hlt
    exact not_isValidCWComplement_of_card_lt_top_codim hcfg (Nat.lt_of_not_ge hlt) hvalid
  exact ⟨hbot, hadj, htop,
    telescope_interval_floor hr hcfg.1 hcfg.2.2.1 hcfg.2.2.2.1 hbot hadj htop⟩

/-- **Binomial (`d = 2`) Cardinality Floor (`2 ^ (r - 1) ≤ 3 * U.card`):**
Every valid complement for a canonical binomial (`d = 2`) satisfies `2 ^ (r - 1) ≤ 3 * U.card`;
equivalently, `3 * U.card < 2 ^ (r - 1)` is unconditionally impossible! -/
theorem binomial_card_floor {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r : ℕ} (hr : 1 ≤ r) {m : Fin 2 → ℕ} {b : Fin 2 → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r 2 m b)
    (hvalid : IsValidCWComplement D r (∑ j : Fin 2, Polynomial.C (b j) * X ^ (m j)) γ U) :
    2 ^ (r - 1) ≤ 3 * U.card :=
  (multiMonomial_card_floor hr hcfg hvalid).2.2.2

theorem not_isValidCWComplement_binomial_of_three_mul_card_lt
    {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r : ℕ} (hr : 1 ≤ r) {m : Fin 2 → ℕ} {b : Fin 2 → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r 2 m b)
    (hu_lt : 3 * U.card < 2 ^ (r - 1)) :
    ¬ IsValidCWComplement D r (∑ j : Fin 2, Polynomial.C (b j) * X ^ (m j)) γ U :=
  fun hvalid => not_lt_of_ge (binomial_card_floor hr hcfg hvalid) hu_lt

/-- **Trinomial (`d = 3`) Cardinality Floor (`2 ^ (r - 3) ≤ U.card`):**
Every valid complement for a canonical trinomial (`d = 3`, `3 ≤ r`) satisfies
`2 ^ (r - 3) ≤ U.card` (ruling out every complement of size `< n / 8`, i.e. agreement `> 7n / 8`)! -/
theorem trinomial_card_floor {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r : ℕ} (hr : 3 ≤ r) {m : Fin 3 → ℕ} {b : Fin 3 → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r 3 m b)
    (hvalid : IsValidCWComplement D r (∑ j : Fin 3, Polynomial.C (b j) * X ^ (m j)) γ U) :
    2 ^ (r - 3) ≤ U.card := by
  have h4 := (multiMonomial_card_floor (by omega : 1 ≤ r) hcfg hvalid).2.2.2
  have hr1 : 2 ^ (r - 1) = 4 * 2 ^ (r - 3) := by
    have he : r - 1 = (r - 3) + 2 := by omega
    conv_lhs => rw [he, pow_add]
    ring
  omega

theorem not_isValidCWComplement_trinomial_of_card_lt_octant
    {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r : ℕ} (hr : 3 ≤ r) {m : Fin 3 → ℕ} {b : Fin 3 → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r 3 m b)
    (hu_lt : U.card < 2 ^ (r - 3)) :
    ¬ IsValidCWComplement D r (∑ j : Fin 3, Polynomial.C (b j) * X ^ (m j)) γ U :=
  fun hvalid => not_lt_of_ge (trinomial_card_floor hr hcfg hvalid) hu_lt

/-- **Field-Free `NativeListBound = 0` Floor Corollary (`nativeListBound_zero_of_card_floor`):**
Over **every** field `F` (`4 ≤ r`, `1 ≤ d`), if `(d + 1) * (2 ^ r - A) < 2 ^ (r - 1)` (`A ≤ 2 ^ r`,
so `5 * 2 ^ (r - 3) ≤ A` automatically when `d ≤ 3`), then **zero** ambient or native circle
codewords agree with `∑ j : Fin d, C (b j) * X ^ (m j) + R` on `A` points of `D`! -/
theorem nativeListBound_zero_of_card_floor {F : Type*} [Field F] [DecidableEq F]
    {r d : ℕ} (hr : 4 ≤ r) (hd : 0 < d)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {m : Fin d → ℕ} {b : Fin d → F} (R : F[X])
    (hm_mono : StrictMono m)
    (hm_range : ∀ j : Fin d, 2 ^ (r - 1) < m j ∧ m j < 2 ^ r)
    (hb_ne : ∀ j : Fin d, b j ≠ 0)
    (hR : R.natDegree ≤ 2 ^ (r - 1))
    {A : ℕ} (hA_lo : 5 * 2 ^ (r - 3) ≤ A) (hA_hi : A ≤ 2 ^ r)
    (hfloor_lt : (d + 1) * (2 ^ r - A) < 2 ^ (r - 1)) :
    (¬ ∃ P : F[X], P.natDegree ≤ 2 ^ (r - 1) ∧
        A ≤ (D.filter fun x ↦
          P.eval x = (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j) + R).eval x).card) ∧
    MCAChallenge.NativeListBound D (2 ^ (r - 1)) A
      (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j) + R) 0 := by
  have hgap :
      2 ^ r - A < m ⟨0, hd⟩ - 2 ^ (r - 1) ∨
      2 ^ r - A < 2 ^ r - m ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ ∨
      ∃ (j : ℕ) (hj : j + 1 < d),
        2 ^ r - A < m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩ := by
    by_contra hnot
    push Not at hnot
    obtain ⟨hbot, htop, hadj⟩ := hnot
    have hge := telescope_interval_floor (by omega : 1 ≤ r) hd hm_mono hm_range hbot hadj htop
    omega
  exact nativeListBound_zero_of_support_gap hr hd hD_card hD_pow R hm_mono hm_range hb_ne hR
    hA_lo hA_hi hgap

/-! ## Section 4: Binomial (`d = 2`) Silent-Band + `CW*` Zero-Gap & Critical Uniqueness -/

/-- Explicit unwrapped silent-band sum for a 2-monomial polynomial `C b₀ * X ^ m₀ + C b₁ * X ^ m₁`. -/
theorem binomial_silentBand_coeff_eq_zero {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ} (hm₁_lt : m₁ < 2 ^ r) (hm₀_lt_m₁ : m₀ < m₁)
    {b₀ b₁ γ : F} {U : Finset F}
    (hvalid : IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U)
    {k : ℕ} (hk_lo : 2 ^ (r - 1) + U.card < k) (hk_hi : k < 2 ^ r) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    ((Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) * H_U).coeff k = 0 ∧
    (if m₀ ≤ k then b₀ * H_U.coeff (k - m₀) else 0) +
      (if m₁ ≤ k then b₁ * H_U.coeff (k - m₁) else 0) = 0 := by
  let mVec : Fin 2 → ℕ := ![m₀, m₁]
  let bVec : Fin 2 → F := ![b₀, b₁]
  have hm_lt : ∀ j : Fin 2, mVec j < 2 ^ r := by
    intro j; fin_cases j <;> dsimp [mVec] <;> omega
  have hsum_eq :
      (∑ j : Fin 2, Polynomial.C (bVec j) * (X : F[X]) ^ (mVec j)) =
        Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁ := by
    rw [Fin.sum_univ_two]; rfl
  have hvalid' : IsValidCWComplement D r
      (∑ j : Fin 2, Polynomial.C (bVec j) * (X : F[X]) ^ (mVec j)) γ U := by
    rwa [hsum_eq]
  obtain ⟨hwH0, hsum0⟩ := silentBand_unwrapped_coeff_eq_zero hm_lt hvalid' hk_lo hk_hi
  rw [hsum_eq] at hwH0
  rw [Fin.sum_univ_two] at hsum0
  exact ⟨hwH0, hsum0⟩

private lemma binomial_support_bounds {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ}
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) {U : Finset F}
    (hvalid : IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U) :
    m₀ - 2 ^ (r - 1) ≤ U.card ∧
    m₁ - m₀ ≤ U.card ∧
    2 ^ r - m₁ ≤ U.card := by
  let mVec : Fin 2 → ℕ := ![m₀, m₁]
  let bVec : Fin 2 → F := ![b₀, b₁]
  have hm_mono : StrictMono mVec := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (lt_irrefl _)
    · exact hm₀_lt_m₁
    · exact absurd hij (not_lt_of_ge (by decide))
    · exact absurd hij (lt_irrefl _)
  have hm_range : ∀ j : Fin 2, 2 ^ (r - 1) < mVec j ∧ mVec j < 2 ^ r := by
    intro j; fin_cases j <;> dsimp [mVec] <;> exact ⟨by omega, by omega⟩
  have hb_ne : ∀ j : Fin 2, bVec j ≠ 0 := by
    intro j; fin_cases j <;> dsimp [bVec] <;> assumption
  have hsum_eq :
      (∑ j : Fin 2, Polynomial.C (bVec j) * (X : F[X]) ^ (mVec j)) =
        Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁ := by
    rw [Fin.sum_univ_two]; rfl
  obtain ⟨_, _, hc0_pow, _, _, hB_van, _⟩ := hvalid
  rw [← hsum_eq] at hB_van
  have hc0_ne : (∏ x ∈ U, (X - Polynomial.C x)).coeff 0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at hc0_pow
    exact zero_ne_one hc0_pow
  refine ⟨?_, ?_, ?_⟩
  · by_contra hlt
    exact false_of_silentBand_lt_bot_offset (by decide : 0 < 2) hm_mono hm_range hb_ne hc0_ne
      hB_van (by dsimp [mVec]; omega)
  · by_contra hlt
    exact false_of_silentBand_lt_adjacent_gap hm_mono hm_range hb_ne hB_van
      (j := 0) (by decide : 0 + 1 < 2)
      (by dsimp [mVec]; omega)
  · by_contra hlt
    exact false_of_silentBand_lt_top_codim (by decide : 0 < 2) hm_mono hm_range hb_ne
      hB_van (by dsimp [mVec]; omega)

/-- **Upper-Tail Binomial Zero Gap (`binomial_locator_coeff_eq_zero_of_upper_silent`):**
For every `k` with `m₀ + U.card < k` and `k < 2 ^ r`, `(C b₀ * X ^ m₀ * H_U).coeff k = 0`, forcing
`H_U.coeff (k - m₁) = 0` (equivalently `H_U.coeff i = 0` whenever `U.card + 1 ≤ i + (m₁ - m₀)` and
`m₁ + i < 2 ^ r`). -/
theorem binomial_locator_coeff_eq_zero_of_upper_silent {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ}
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) {U : Finset F}
    (hvalid : IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    (∀ k : ℕ, m₀ + U.card < k → k < 2 ^ r → H_U.coeff (k - m₁) = 0) ∧
    (∀ i : ℕ, U.card + 1 ≤ i + (m₁ - m₀) → m₁ + i < 2 ^ r → H_U.coeff i = 0) := by
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  obtain ⟨_, hHd, _, _, _⟩ := locator_monic_natDegree_and_coeff_zero U
  obtain ⟨_, hadj_le, _⟩ := binomial_support_bounds hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hvalid
  have hk_thm : ∀ k : ℕ, m₀ + U.card < k → k < 2 ^ r → H_U.coeff (k - m₁) = 0 := by
    intro k hk_gt hk_lt
    have hk_lo : 2 ^ (r - 1) + U.card < k := by omega
    obtain ⟨_, hsum⟩ := binomial_silentBand_coeff_eq_zero hm₁_lt hm₀_lt_m₁ hvalid hk_lo hk_lt
    have hm₀_le : m₀ ≤ k := by omega
    have hm₁_le : m₁ ≤ k := by omega
    simp only [hm₀_le, hm₁_le, ↓reduceIte] at hsum
    have hc0 : H_U.coeff (k - m₀) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hHd]; omega)
    rw [hc0, mul_zero, zero_add] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left hb₁
  refine ⟨hk_thm, fun i hi_lo hi_hi ↦ ?_⟩
  have h := hk_thm (m₁ + i) (by omega) hi_hi
  rwa [Nat.add_sub_cancel_left] at h

/-- **Lower-Tail Binomial Zero Gap (`binomial_locator_coeff_eq_zero_of_lower_silent`):**
For every `k` with `2 ^ (r - 1) + U.card < k` and `k < m₁`, `(C b₁ * X ^ m₁ * H_U).coeff k = 0`,
forcing `H_U.coeff (k - m₀) = 0` (equivalently `H_U.coeff i = 0` whenever
`2 ^ (r - 1) + U.card < m₀ + i` and `i < m₁ - m₀`). -/
theorem binomial_locator_coeff_eq_zero_of_lower_silent {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ}
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) {U : Finset F}
    (hvalid : IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    (∀ k : ℕ, 2 ^ (r - 1) + U.card < k → k < m₁ → H_U.coeff (k - m₀) = 0) ∧
    (∀ i : ℕ, 2 ^ (r - 1) + U.card < m₀ + i → i < m₁ - m₀ → H_U.coeff i = 0) := by
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  obtain ⟨hbot_le, _, _⟩ := binomial_support_bounds hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hvalid
  have hk_thm : ∀ k : ℕ, 2 ^ (r - 1) + U.card < k → k < m₁ → H_U.coeff (k - m₀) = 0 := by
    intro k hk_lo hk_lt_m₁
    have hk_lt : k < 2 ^ r := by omega
    obtain ⟨_, hsum⟩ := binomial_silentBand_coeff_eq_zero hm₁_lt hm₀_lt_m₁ hvalid hk_lo hk_lt
    have hm₀_le : m₀ ≤ k := by omega
    have hm₁_not_le : ¬ (m₁ ≤ k) := by omega
    simp only [hm₀_le, hm₁_not_le, ↓reduceIte, add_zero] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left hb₀
  refine ⟨hk_thm, fun i hi_lo hi_hi ↦ ?_⟩
  have h := hk_thm (m₀ + i) hi_lo (by omega)
  rwa [Nat.add_sub_cancel_left] at h

/-- **`CW*` Self-Reciprocal Zero-Coefficient Equivalence (`cw_star_locator_coeff_eq_zero_iff`):**
For ANY `IsValidCWComplement D r w γ U` and any `i ≤ U.card`,
`H_U.coeff i = 0 ↔ H_U.coeff (U.card - i) = 0`. -/
theorem cw_star_locator_coeff_eq_zero_iff {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r : ℕ} {w : F[X]} {γ : F} {U : Finset F}
    (hvalid : IsValidCWComplement D r w γ U) {i : ℕ} (hi : i ≤ U.card) :
    (∏ x ∈ U, (X - Polynomial.C x)).coeff i = 0 ↔
      (∏ x ∈ U, (X - Polynomial.C x)).coeff (U.card - i) = 0 := by
  obtain ⟨_, _, hc0_pow, hcw_rec, _, _, _⟩ := hvalid
  set H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
  have hc0_ne : H_U.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by decide)] at hc0_pow
    exact zero_ne_one hc0_pow
  constructor
  · intro hi0
    rw [hcw_rec i hi, hi0, zero_pow (by decide), mul_zero]
  · intro hsub0
    have hrec_rev := hcw_rec (U.card - i) (Nat.sub_le U.card i)
    rw [Nat.sub_sub_self hi, hsub0, zero_pow (by decide), mul_zero] at hrec_rev
    exact hrec_rev

/-- **`CW*` Self-Reciprocal Reflected Binomial Zero Bands (`binomial_locator_reflected_zero_gaps`):**
Reflecting the upper-tail and lower-tail binomial zero gaps via `cw_star_locator_coeff_eq_zero_iff`
yields two complementary zero bands on `H_U`:
1. `H_U.coeff j = 0` whenever `j < m₁ - m₀` and `m₁ + U.card < 2 ^ r + j` (reflected upper tail),
2. `H_U.coeff j = 0` whenever `U.card + 1 ≤ j + (m₁ - m₀)`, `j ≤ U.card`, and
   `2 ^ (r - 1) + j < m₀` (reflected lower tail). -/
theorem binomial_locator_reflected_zero_gaps {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ}
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) {U : Finset F}
    (hvalid : IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    (∀ j : ℕ, j < m₁ - m₀ → m₁ + U.card < 2 ^ r + j → H_U.coeff j = 0) ∧
    (∀ j : ℕ, U.card + 1 ≤ j + (m₁ - m₀) → j ≤ U.card → 2 ^ (r - 1) + j < m₀ →
      H_U.coeff j = 0) := by
  obtain ⟨_, hadj_le, _⟩ := binomial_support_bounds hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hvalid
  obtain ⟨_, hup_i⟩ :=
    binomial_locator_coeff_eq_zero_of_upper_silent hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hvalid
  obtain ⟨_, hlo_i⟩ :=
    binomial_locator_coeff_eq_zero_of_lower_silent hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hvalid
  refine ⟨fun j hj_lt hj_sum ↦ ?_, fun j hj_lo hj_le hj_bot ↦ ?_⟩
  · have hj_le_u : j ≤ U.card := by omega
    rw [cw_star_locator_coeff_eq_zero_iff hvalid hj_le_u]
    exact hup_i (U.card - j) (by omega) (by omega)
  · rw [cw_star_locator_coeff_eq_zero_iff hvalid hj_le]
    exact hlo_i (U.card - j) (by omega) (by omega)

/-- **Unconditional Constant-Term & Circle-Norm Pinning at Critical Gap `U.card = m₁ - m₀`:**
Whenever `U.card = m₁ - m₀`, evaluating the silent band at `k = m₁ = m₀ + U.card` forces
`b₀ + b₁ * H_U.coeff 0 = 0`, i.e. `H_U.coeff 0 = -b₀ * b₁⁻¹` uniquely, AND
`(b₀ * b₁⁻¹) ^ ((2 ^ 31 - 1) + 1) = 1`! -/
theorem binomial_critical_gap_const_coeff {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ}
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₁ : b₁ ≠ 0) {U : Finset F}
    (hvalid : IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U)
    (hcrit : U.card = m₁ - m₀) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    b₀ + b₁ * H_U.coeff 0 = 0 ∧
    H_U.coeff 0 = -b₀ * b₁⁻¹ ∧
    (b₀ * b₁⁻¹) ^ ((2 ^ 31 - 1) + 1) = 1 := by
  intro H_U
  obtain ⟨_, _, hHtop, _, _⟩ := locator_monic_natDegree_and_coeff_zero U
  have hHtop' : H_U.coeff U.card = 1 := hHtop
  have hc0_pow : (H_U.coeff 0) ^ ((2 ^ 31 - 1) + 1) = 1 := hvalid.2.2.1
  have hk_lo : 2 ^ (r - 1) + U.card < m₁ := by omega
  obtain ⟨_, hsum⟩ := binomial_silentBand_coeff_eq_zero hm₁_lt hm₀_lt_m₁ hvalid hk_lo hm₁_lt
  have hm₀_le : m₀ ≤ m₁ := le_of_lt hm₀_lt_m₁
  have hsub : m₁ - m₀ = U.card := hcrit.symm
  simp only [hm₀_le, le_rfl, ↓reduceIte, hsub, Nat.sub_self] at hsum
  change b₀ * H_U.coeff U.card + b₁ * H_U.coeff 0 = 0 at hsum
  rw [hHtop', mul_one] at hsum
  have hc0_eq : H_U.coeff 0 = -b₀ * b₁⁻¹ := by
    apply mul_left_cancel₀ hb₁
    calc b₁ * H_U.coeff 0 = -b₀ := by linear_combination hsum
      _ = -b₀ * (b₁ * b₁⁻¹) := by rw [mul_inv_cancel₀ hb₁, mul_one]
      _ = b₁ * (-b₀ * b₁⁻¹) := by ring
  have hnorm : (b₀ * b₁⁻¹) ^ ((2 ^ 31 - 1) + 1) = 1 := by
    have hneg_even : (-1 : F) ^ ((2 ^ 31 - 1) + 1) = 1 := by
      have hev : (2 ^ 31 - 1) + 1 = 2 * 2 ^ 30 := by decide
      rw [hev, pow_mul, neg_one_sq, one_pow]
    calc (b₀ * b₁⁻¹) ^ ((2 ^ 31 - 1) + 1)
        = (-1 : F) ^ ((2 ^ 31 - 1) + 1) * (-b₀ * b₁⁻¹) ^ ((2 ^ 31 - 1) + 1) := by
            rw [← mul_pow]; congr 1; ring
      _ = 1 * (H_U.coeff 0) ^ ((2 ^ 31 - 1) + 1) := by rw [hneg_even, ← hc0_eq]
      _ = 1 := by rw [one_mul, hc0_pow]
  exact ⟨hsum, hc0_eq, hnorm⟩

private lemma pure_binomial_locator_dvd_domain {F : Type*} [Field F] [DecidableEq F]
    {D U : Finset F} {n u : ℕ} (hn : 0 < n) (hu_pos : 0 < u)
    (hUD : U ⊆ D) (hD_pow : ∀ x ∈ D, x ^ n = 1) (hU_card : U.card = u)
    {c : F} (hH_eq : (∏ x ∈ U, (X - Polynomial.C x)) = (X : F[X]) ^ u - Polynomial.C c) :
    u ∣ n := by
  obtain ⟨_, _, _, _, heval_iff⟩ := locator_monic_natDegree_and_coeff_zero U
  have hU_nonempty : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₀, hx₀U⟩ := hU_nonempty
  have hx₀_pow_n : x₀ ^ n = 1 := hD_pow x₀ (hUD hx₀U)
  have hx₀_ne : x₀ ≠ 0 := fun h0 => by
    rw [h0, zero_pow hn.ne'] at hx₀_pow_n
    exact zero_ne_one hx₀_pow_n
  have hx_pow_u : ∀ x ∈ U, x ^ u = c := by
    intro x hxU
    have hev0 := (heval_iff x).mp hxU
    rw [hH_eq, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hev0
    exact sub_eq_zero.mp hev0
  have hc_eq : c = x₀ ^ u := (hx_pow_u x₀ hx₀U).symm
  have hc_ne : c ≠ 0 := by rw [hc_eq]; exact pow_ne_zero u hx₀_ne
  set V : Finset F := U.image (fun x => x * x₀⁻¹)
  have hinj : Set.InjOn (fun x : F => x * x₀⁻¹) (U : Set F) := by
    intro x₁ _ x₂ _ heq
    exact mul_right_cancel₀ (inv_ne_zero hx₀_ne) heq
  have hV_card : V.card = u := by
    rw [Finset.card_image_of_injOn hinj, hU_card]
  set g : ℕ := Nat.gcd u n
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right u hn
  have hV_pow_g : ∀ y ∈ V, y ^ g = 1 := by
    intro y hyV
    obtain ⟨x, hxU, rfl⟩ := Finset.mem_image.mp hyV
    have hx_pow_n : x ^ n = 1 := hD_pow x (hUD hxU)
    have hx_ne : x ≠ 0 := fun h0 => by
      rw [h0, zero_pow hn.ne'] at hx_pow_n
      exact zero_ne_one hx_pow_n
    have hy_ne : x * x₀⁻¹ ≠ 0 := mul_ne_zero hx_ne (inv_ne_zero hx₀_ne)
    have hy_u : (x * x₀⁻¹) ^ u = 1 := by
      rw [mul_pow, inv_pow, hx_pow_u x hxU, ← hc_eq, mul_inv_cancel₀ hc_ne]
    have hy_n : (x * x₀⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hx_pow_n, hx₀_pow_n, inv_one, mul_one]
    have hbez : ((g : ℕ) : ℤ) = (u : ℤ) * u.gcdA n + (n : ℤ) * u.gcdB n :=
      Nat.gcd_eq_gcd_ab u n
    calc (x * x₀⁻¹) ^ g
        = (x * x₀⁻¹) ^ ((g : ℕ) : ℤ) := (zpow_natCast _ g).symm
      _ = (x * x₀⁻¹) ^ ((u : ℤ) * u.gcdA n + (n : ℤ) * u.gcdB n) := by rw [hbez]
      _ = ((x * x₀⁻¹) ^ (u : ℤ)) ^ (u.gcdA n) * ((x * x₀⁻¹) ^ (n : ℤ)) ^ (u.gcdB n) := by
          rw [zpow_add₀ hy_ne, zpow_mul, zpow_mul]
      _ = 1 := by rw [zpow_natCast, zpow_natCast, hy_u, hy_n, one_zpow, one_zpow, mul_one]
  obtain ⟨hMg_m, hMg_d, hMg_wb⟩ := monic_and_natDegree_X_pow_sub_one (F := F) hg_pos
  have hu_le_g : u ≤ g := by
    by_contra hlt
    have hg_lt_V : g < V.card := by omega
    have hMg_zero : ((X : F[X]) ^ g - 1) = 0 := by
      refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq V ?_ ?_ ?_
      · rw [hMg_wb]; exact WithBot.coe_lt_coe.mpr hg_lt_V
      · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe V.card
      · intro y hyV
        simp [hV_pow_g y hyV]
    exact hMg_m.ne_zero hMg_zero
  have hg_dvd_u : g ∣ u := Nat.gcd_dvd_left u n
  have hg_le_u : g ≤ u := Nat.le_of_dvd hu_pos hg_dvd_u
  have hg_eq_u : g = u := le_antisymm hg_le_u hu_le_g
  rw [← hg_eq_u]
  exact Nat.gcd_dvd_right u n

/-- **Critical Binomial Pure-Binomial Locator & Dyadic-Gap Uniqueness
(`binomial_critical_gap_pure_binomial_unique`):**
At the critical adjacent-gap boundary `U.card = m₁ - m₀`, whenever
`U.card < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁)`:
1. Every interior coefficient `1 ≤ i ≤ U.card - 1` of `H_U` vanishes, forcing the exact pure
   binomial **`H_U = X ^ U.card - C (b₀ * b₁⁻¹)`**!
2. If `∀ x ∈ D, x ^ (2 ^ r) = 1`, then **`(m₁ - m₀) ∣ 2 ^ r`** (`0` valid complements whenever
   `m₁ - m₀` is not a power of `2`!).
3. Any other valid complement `U'` with `U'.card = m₁ - m₀` satisfies **`U' = U`**! -/
theorem binomial_critical_gap_pure_binomial_unique {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ}
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) {U : Finset F}
    (hvalid : IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U)
    (hcrit : U.card = m₁ - m₀)
    (hcov : U.card < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁)) :
    let H_U : F[X] := ∏ x ∈ U, (X - Polynomial.C x)
    H_U = (X : F[X]) ^ U.card - Polynomial.C (b₀ * b₁⁻¹) ∧
    ((∀ x ∈ D, x ^ (2 ^ r) = 1) → (m₁ - m₀) ∣ 2 ^ r) ∧
    (∀ U' : Finset F,
      IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U' →
      U'.card = m₁ - m₀ → U' = U) := by
  have hpure : ∀ V : Finset F,
      IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ V →
      V.card = m₁ - m₀ →
      (∏ x ∈ V, (X - Polynomial.C x)) = (X : F[X]) ^ (m₁ - m₀) - Polynomial.C (b₀ * b₁⁻¹) := by
    intro V hV hV_card
    have hV_cov : V.card < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁) := by omega
    obtain ⟨_, hVd, hVtop, _, _⟩ := locator_monic_natDegree_and_coeff_zero V
    obtain ⟨_, hc0_eq, _⟩ := binomial_critical_gap_const_coeff hm₀_lo hm₀_lt_m₁ hm₁_lt hb₁ hV hV_card
    obtain ⟨_, hup_dir⟩ :=
      binomial_locator_coeff_eq_zero_of_upper_silent hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hV
    obtain ⟨_, hlo_dir⟩ :=
      binomial_locator_coeff_eq_zero_of_lower_silent hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hV
    obtain ⟨hup_ref, hlo_ref⟩ :=
      binomial_locator_reflected_zero_gaps hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁ hV
    have hint_zero : ∀ i : ℕ, 1 ≤ i → i < V.card →
        (∏ x ∈ V, (X - Polynomial.C x)).coeff i = 0 := by
      intro i hi1 hi_lt
      have hcov_or : V.card < 2 * (m₀ - 2 ^ (r - 1)) ∨ V.card < 2 * (2 ^ r - m₁) := by
        rcases le_total (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁) with hle | hle
        · right; rw [max_eq_right hle] at hV_cov; exact hV_cov
        · left; rw [max_eq_left hle] at hV_cov; exact hV_cov
      rcases hcov_or with hα | hβ
      · by_cases hi_low : i < m₀ - 2 ^ (r - 1)
        · exact hlo_ref i (by omega) (by omega) (by omega)
        · exact hlo_dir i (by omega) (by omega)
      · by_cases hi_low : i < 2 ^ r - m₁
        · exact hup_dir i (by omega) (by omega)
        · exact hup_ref i (by omega) (by omega)
    ext d
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · have hne : (0 : ℕ) ≠ m₁ - m₀ := by omega
      simp only [hne, ↓reduceIte, hc0_eq, zero_sub]
      ring
    · simp only [hd_pos.ne', ↓reduceIte, sub_zero]
      rcases lt_trichotomy d V.card with hd_lt | rfl | hd_gt
      · have hne : d ≠ m₁ - m₀ := by omega
        simp only [hne, ↓reduceIte]
        exact hint_zero d hd_pos hd_lt
      · simp only [hV_card, ↓reduceIte]
        rw [← hV_card]
        exact hVtop
      · have hne : d ≠ m₁ - m₀ := by omega
        simp only [hne, ↓reduceIte]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hVd]; exact hd_gt)
  have hHU_eq : (∏ x ∈ U, (X - Polynomial.C x)) =
      (X : F[X]) ^ U.card - Polynomial.C (b₀ * b₁⁻¹) := by
    rw [hcrit]
    exact hpure U hvalid hcrit
  refine ⟨hHU_eq, fun hD_pow ↦ ?_, fun U' hU' hU'_card ↦ ?_⟩
  · have hn : 0 < 2 ^ r := Nat.pos_of_ne_zero (by positivity)
    exact pure_binomial_locator_dvd_domain hn (by omega : 0 < m₁ - m₀) hvalid.1 hD_pow hcrit
      (hpure U hvalid hcrit)
  · have hloc_eq : (∏ x ∈ U', (X - Polynomial.C x)) = (∏ x ∈ U, (X - Polynomial.C x)) := by
      rw [hpure U' hU' hU'_card, hpure U hvalid hcrit]
    obtain ⟨_, _, _, _, hev_U'⟩ := locator_monic_natDegree_and_coeff_zero U'
    obtain ⟨_, _, _, _, hev_U⟩ := locator_monic_natDegree_and_coeff_zero U
    ext z
    rw [hev_U' z, hev_U z, hloc_eq]

/-- **Non-Dyadic Critical Binomial Gap Vanishing
(`not_isValidCWComplement_binomial_critical_of_not_dvd_two_pow`):**
Whenever `¬ ((m₁ - m₀) ∣ 2 ^ r)` and `m₁ - m₀ < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁)`, **zero**
valid complements have `U.card = m₁ - m₀`! -/
theorem not_isValidCWComplement_binomial_critical_of_not_dvd_two_pow
    {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0) {U : Finset F}
    (hcrit : U.card = m₁ - m₀)
    (hcov : U.card < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁))
    (hndvd : ¬ ((m₁ - m₀) ∣ 2 ^ r)) :
    ¬ IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U :=
  fun hvalid => hndvd
    ((binomial_critical_gap_pure_binomial_unique hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁
      hvalid hcrit hcov).2.1 hD_pow)

/-- **At Most `1` Valid Complement in the Critical Binomial Boundary Stratum:**
For ANY binomial `C b₀ * X ^ m₀ + C b₁ * X ^ m₁` with
`m₁ - m₀ < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁)`, at most **one** complement `U` satisfies
`IsValidCWComplement` with `U.card = m₁ - m₀`. -/
theorem card_le_one_binomial_critical_gap {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r m₀ m₁ : ℕ}
    (hm₀_lo : 2 ^ (r - 1) < m₀) (hm₀_lt_m₁ : m₀ < m₁) (hm₁_lt : m₁ < 2 ^ r)
    {b₀ b₁ γ : F} (hb₀ : b₀ ≠ 0) (hb₁ : b₁ ≠ 0)
    (hcov : m₁ - m₀ < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁))
    (𝒰_crit : Finset (Finset F))
    (h𝒰 : ∀ U ∈ 𝒰_crit,
      IsValidCWComplement D r (Polynomial.C b₀ * X ^ m₀ + Polynomial.C b₁ * X ^ m₁) γ U ∧
      U.card = m₁ - m₀) :
    𝒰_crit.card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun U₁ h₁ U₂ h₂ ↦ ?_)
  obtain ⟨hv₁, hc₁⟩ := h𝒰 U₁ h₁
  obtain ⟨hv₂, hc₂⟩ := h𝒰 U₂ h₂
  exact (binomial_critical_gap_pure_binomial_unique hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁
    hv₂ hc₂ (by omega)).2.2 U₁ hv₁ hc₁

/-! ## Section 5: Narrowed Multi-Monomial Predicates & Master `MCAChallenge.InteriorThree` Reductions -/

/-- **Connected Multi-Monomial Support Band (`InConnectedMultiMonomialBand`):**
Simultaneously enforces the telescoped cardinality floor `2 ^ (r - 1) ≤ (d + 1) * u`, the left-edge
offset floor `m 0 - 2 ^ (r - 1) ≤ u`, the right-edge codimension floor `2 ^ r - m (d - 1) ≤ u`,
and every internal adjacent-gap floor `m (j + 1) - m j ≤ u`. -/
def InConnectedMultiMonomialBand (r d : ℕ) (m : Fin d → ℕ) (u : ℕ) : Prop :=
  2 ^ (r - 1) ≤ (d + 1) * u ∧
  (∀ hd : 0 < d, m ⟨0, hd⟩ - 2 ^ (r - 1) ≤ u) ∧
  (∀ hd : 0 < d, 2 ^ r - m ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ ≤ u) ∧
  (∀ (j : ℕ) (hj : j + 1 < d), m ⟨j + 1, hj⟩ - m ⟨j, Nat.lt_of_succ_lt hj⟩ ≤ u)

/-- **Critical Binomial Pure-Binomial Boundary Stratum (`InCriticalBinomialPureStratum`):**
For `d = 2`, `u = m 1 - m 0` with `u < 2 * max (m 0 - 2 ^ (r - 1)) (2 ^ r - m 1)`, where `H_U` is
uniquely pinned to `X ^ u - C (b 0 * (b 1)⁻¹)` (`0` complements if `¬ ((m 1 - m 0) ∣ 2 ^ r)` and
`≤ 1` complement unconditionally). -/
def InCriticalBinomialPureStratum (r d : ℕ) (m : Fin d → ℕ) (u : ℕ) : Prop :=
  ∃ hd2 : d = 2,
    let m₀ := m ⟨0, by omega⟩
    let m₁ := m ⟨1, by omega⟩
    u = m₁ - m₀ ∧
    u < 2 * max (m₀ - 2 ^ (r - 1)) (2 ^ r - m₁)

/-- Every valid complement of a canonical configuration (`1 ≤ r`) lies in
`InConnectedMultiMonomialBand r d m U.card`. -/
theorem isValidCWComplement_inConnectedMultiMonomialBand {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r d : ℕ} (hr : 1 ≤ r) {m : Fin d → ℕ} {b : Fin d → F} {γ : F} {U : Finset F}
    (hcfg : IsCanonicalHighConfig r d m b)
    (hvalid : IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U) :
    InConnectedMultiMonomialBand r d m U.card := by
  obtain ⟨hbot, hadj, htop, hfloor⟩ := multiMonomial_card_floor hr hcfg hvalid
  exact ⟨hfloor, fun _ => hbot, fun _ => htop, hadj⟩

/-- At most `1` valid complement lies in `InCriticalBinomialPureStratum r d m U.card`, and `0`
whenever `d = 2` and `¬ ((m 1 - m 0) ∣ 2 ^ r)`. -/
theorem criticalBinomialPureStratum_card_le_one {F : Type*} [Field F] [DecidableEq F]
    {D : Finset F} {r d : ℕ} (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {m : Fin d → ℕ} {b : Fin d → F} {γ : F}
    (hcfg : IsCanonicalHighConfig r d m b)
    (𝒰 : Finset (Finset F))
    (h𝒰 : ∀ U ∈ 𝒰,
      IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U ∧
      InCriticalBinomialPureStratum r d m U.card) :
    𝒰.card ≤ 1 ∧
    (∀ hd2 : d = 2, ¬ ((m ⟨1, by omega⟩ - m ⟨0, by omega⟩) ∣ 2 ^ r) → 𝒰 = ∅) := by
  by_cases hne : 𝒰.Nonempty
  · obtain ⟨U₀, hU₀m⟩ := hne
    obtain ⟨hv₀, hd2, hcrit₀, hcov₀⟩ := h𝒰 U₀ hU₀m
    subst hd2
    change U₀.card = m 1 - m 0 at hcrit₀
    change U₀.card < 2 * max (m 0 - 2 ^ (r - 1)) (2 ^ r - m 1) at hcov₀
    have hm₀_lo : 2 ^ (r - 1) < m 0 := (hcfg.2.2.2.1 0).1
    have hm₀_lt_m₁ : m 0 < m 1 := hcfg.2.2.1 (by decide : (0 : Fin 2) < 1)
    have hm₁_lt : m 1 < 2 ^ r := (hcfg.2.2.2.1 1).2
    have hb₀ : b 0 ≠ 0 := hcfg.2.2.2.2.1 0
    have hb₁ : b 1 ≠ 0 := hcfg.2.2.2.2.1 1
    have hsum_two :
        (∑ j : Fin 2, Polynomial.C (b j) * (X : F[X]) ^ (m j)) =
          Polynomial.C (b 0) * X ^ (m 0) + Polynomial.C (b 1) * X ^ (m 1) := by
      rw [Fin.sum_univ_two]
    have hv₀' : IsValidCWComplement D r
        (Polynomial.C (b 0) * X ^ (m 0) + Polynomial.C (b 1) * X ^ (m 1)) γ U₀ := by
      rwa [← hsum_two]
    have hdvd : (m 1 - m 0) ∣ 2 ^ r :=
      (binomial_critical_gap_pure_binomial_unique hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁
        hv₀' hcrit₀ hcov₀).2.1 hD_pow
    have hle1 : 𝒰.card ≤ 1 := by
      refine card_le_one_binomial_critical_gap (D := D) (γ := γ) hm₀_lo hm₀_lt_m₁ hm₁_lt hb₀ hb₁
        (hcrit₀ ▸ hcov₀) 𝒰 (fun U hUm ↦ ?_)
      obtain ⟨hv, _, hc, _⟩ := h𝒰 U hUm
      rw [hsum_two] at hv
      exact ⟨hv, hc⟩
    exact ⟨hle1, fun _ hndvd => absurd hdvd hndvd⟩
  · have hemp : 𝒰 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hemp, Finset.card_empty]
    exact ⟨Nat.zero_le 1, fun _ _ => rfl⟩

/-- **Narrowed Sub-Lemma Target 4a (`MultiMonomialConnectedCWBound K`):**
Restricts `MultiMonomialCanonicalCWBound K` (`2 ≤ d ≤ 3`) strictly to complements inside
`InConnectedMultiMonomialBand r d m U.card` and outside non-dyadic critical binomial strata, with
zero loss in `K`. -/
def MultiMonomialConnectedCWBound.{v} (K : ℕ) : Prop :=
  ∀ (F : Type v) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ (d : ℕ) (m : Fin d → ℕ) (b : Fin d → F) (γ : F),
        2 ≤ d → IsCanonicalHighConfig r d m b →
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U ∧
            InConnectedMultiMonomialBand r d m U.card ∧
            (∀ hd2 : d = 2,
              InCriticalBinomialPureStratum r d m U.card →
              (m ⟨1, by omega⟩ - m ⟨0, by omega⟩) ∣ 2 ^ r)) →
          𝒰.card ≤ K * 2 ^ r

/-- **Narrowed Sub-Lemma Target 4b (`MultiMonomialStrictInteriorCWBound K`):**
Excludes **all** `InCriticalBinomialPureStratum r d m U.card` complements (`≤ 1` uniquely-pinned
pure-binomial locator) by bounding the strict-interior remainder by `K * 2 ^ r - 1`. -/
def MultiMonomialStrictInteriorCWBound.{v} (K : ℕ) : Prop :=
  ∀ (F : Type v) [Field F] [DecidableEq F], Nat.card F = (2 ^ 31 - 1) ^ 2 →
    ∀ r : ℕ, 4 ≤ r → r ≤ 31 → ∀ D : Finset F, D.card = 2 ^ r → (∀ x ∈ D, x ^ (2 ^ r) = 1) →
      ∀ (d : ℕ) (m : Fin d → ℕ) (b : Fin d → F) (γ : F),
        2 ≤ d → IsCanonicalHighConfig r d m b →
        ∀ 𝒰 : Finset (Finset F),
          (∀ U ∈ 𝒰,
            IsValidCWComplement D r (∑ j : Fin d, Polynomial.C (b j) * X ^ (m j)) γ U ∧
            InConnectedMultiMonomialBand r d m U.card ∧
            ¬ InCriticalBinomialPureStratum r d m U.card) →
          𝒰.card ≤ K * 2 ^ r - 1

/-- **Composable Reduction (`multiMonomialCanonicalCWBound_of_connectedBand`):**
`MultiMonomialConnectedCWBound K` implies `MultiMonomialCanonicalCWBound K` across all `K`. -/
theorem multiMonomialCanonicalCWBound_of_connectedBand {K : ℕ}
    (hConn : MultiMonomialConnectedCWBound.{u} K) :
    MultiMonomialCanonicalCWBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow d m b γ hd2 hcfg 𝒰 h𝒰
  refine hConn F hF r hr_lo hr_hi D hD_card hD_pow d m b γ hd2 hcfg 𝒰 (fun U hUm ↦ ?_)
  have hv := h𝒰 U hUm
  refine ⟨hv, isValidCWComplement_inConnectedMultiMonomialBand (by omega : 1 ≤ r) hcfg hv, ?_⟩
  intro hd2_eq hcrit
  by_contra hndvd
  have hemp := (criticalBinomialPureStratum_card_le_one hD_pow hcfg {U}
    (fun V hVm => by rw [Finset.mem_singleton.mp hVm]; exact ⟨hv, hcrit⟩)).2 hd2_eq hndvd
  exact Finset.singleton_ne_empty U hemp

/-- **Composable Reduction (`multiMonomialCanonicalCWBound_of_strictInterior`):**
For any `1 ≤ K`, `MultiMonomialStrictInteriorCWBound K` implies `MultiMonomialCanonicalCWBound K`
by splitting off the `≤ 1` critical pure-binomial stratum! -/
theorem multiMonomialCanonicalCWBound_of_strictInterior {K : ℕ}
    (hK_pos : 1 ≤ K)
    (hStrict : MultiMonomialStrictInteriorCWBound.{u} K) :
    MultiMonomialCanonicalCWBound.{u} K := by
  classical
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow d m b γ hd2 hcfg 𝒰 h𝒰
  set 𝒰_crit := 𝒰.filter (fun U ↦ InCriticalBinomialPureStratum r d m U.card)
  set 𝒰_rem := 𝒰.filter (fun U ↦ ¬ InCriticalBinomialPureStratum r d m U.card)
  have hdis : Disjoint 𝒰_crit 𝒰_rem :=
    Finset.disjoint_filter.mpr (fun _ _ hc hnc => hnc hc)
  have hunion : 𝒰_crit ∪ 𝒰_rem = 𝒰 := by
    ext U
    simp only [Finset.mem_union, Finset.mem_filter, 𝒰_crit, 𝒰_rem]
    by_cases hc : InCriticalBinomialPureStratum r d m U.card <;> simp [hc]
  have hcrit_le1 : 𝒰_crit.card ≤ 1 :=
    (criticalBinomialPureStratum_card_le_one hD_pow hcfg 𝒰_crit
      (fun U hUm => ⟨h𝒰 U (Finset.mem_filter.mp hUm).1, (Finset.mem_filter.mp hUm).2⟩)).1
  have hrem_le : 𝒰_rem.card ≤ K * 2 ^ r - 1 := by
    refine hStrict F hF r hr_lo hr_hi D hD_card hD_pow d m b γ hd2 hcfg 𝒰_rem (fun U hUm ↦ ?_)
    obtain ⟨hU_in, hnot_crit⟩ := Finset.mem_filter.mp hUm
    have hv := h𝒰 U hU_in
    exact ⟨hv, isValidCWComplement_inConnectedMultiMonomialBand (by omega : 1 ≤ r) hcfg hv, hnot_crit⟩
  have hKn_pos : 1 ≤ K * 2 ^ r := Nat.mul_le_mul hK_pos Nat.one_le_two_pow
  have hcard_split : 𝒰.card = 𝒰_crit.card + 𝒰_rem.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdis]
  omega

/-- **Master `MCAChallenge.InteriorThree K` Reduction via `MultiMonomialConnectedCWBound K`:**
Composes `InteriorThreeTheoremCWStar.interiorThree_of_nonFrobenius_and_multi_sublemmas` with
`multiMonomialCanonicalCWBound_of_connectedBand` across all `1 ≤ K ≤ 2 ^ 20` and `4 ≤ r ≤ 31`. -/
theorem interiorThree_of_singleNonFrobenius_and_connectedMultiMonomial {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hNonFrob : SingleMonomialNonFrobeniusCWBound.{u} K)
    (hMultiConn : MultiMonomialConnectedCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_nonFrobenius_and_multi_sublemmas
    hK_pos
    hK_cap
    hNonFrob
    (multiMonomialCanonicalCWBound_of_connectedBand hMultiConn)

/-- **Master `MCAChallenge.InteriorThree K` Reduction via `MultiMonomialStrictInteriorCWBound K`:**
Composes `InteriorThreeTheoremCWStar.interiorThree_of_nonFrobenius_and_multi_sublemmas` with
`multiMonomialCanonicalCWBound_of_strictInterior` across all `1 ≤ K ≤ 2 ^ 20` and `4 ≤ r ≤ 31`. -/
theorem interiorThree_of_singleNonFrobenius_and_strictMultiMonomial {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hNonFrob : SingleMonomialNonFrobeniusCWBound.{u} K)
    (hMultiStrict : MultiMonomialStrictInteriorCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_nonFrobenius_and_multi_sublemmas
    hK_pos
    hK_cap
    hNonFrob
    (multiMonomialCanonicalCWBound_of_strictInterior hK_pos hMultiStrict)

end InteriorThreeMultiMonomial
