import InteriorThree_TheoremK0
import InteriorThree_TheoremK0Residual

/-!
# Theorem K0 for `3D < h` (result 29 proves `4D < h`)

Target `LEMMA` (tier 3, `problem-3a-upper`). The `k = 0` cell identity
`A ^ 3 + X ^ e B ^ 3 = q0 (X ^ (e + 2h) A + B)`, `e = 2h - D`, has no solution with `A` monic of degree `h`,
`deg B ≤ h`, `B(0) ≠ 0`, `q0 ≠ 0`, once `1 ≤ D` and `3D < h` (characteristic `0` or above `4h`).

The proof is the one of `InteriorThree_TheoremK0` with one change: the truncation `a` of `A` below `h - D`
is only known to have degree `≤ max(D, h/4)` (the window `D < j < h - D` kills `A_j` unless `4j = h`). Then
`4L0θa - θL0·a` has degree `≤ D + max(D, h/4) < h - D` as soon as `3D < h`, so it vanishes; `4 deg a = deg L0 ≤ D`
follows, and the rest (`a⁴ = q0 L0`, `4a³A_high = q0 c X^D` of degree `≤ 7D/4 < h - D`, `A = X^h + a0`) is unchanged.

The second part wires it into the residual: `InSingleK0StrongStratum` (`u + 3δ = 5q`, `D = 5q - 7δ ≥ 1`,
`3D < 2(q - δ)`, i.e. `13q/19 < δ < 5q/7`) contains the `4D` stratum of `InteriorThree_TheoremK0Residual`
and is empty over M31, and `interiorThree_of_cwStar_qPrime_cg_k0s_and_multi_sublemmas` reduces
`MCAChallenge.InteriorThree K` to `SingleMonomialResidualAfterK0StrongBound K` and the multi-monomial bound.
-/

namespace TheoremK0Strong

open Polynomial LemmaCG TheoremK0

variable {K : Type*} [Field K]

/-- **Theorem K0, strengthened to `3D < h`** (result 29 asks `4D < h`). Let `1 ≤ D`, `3D < h`, `e = 2h - D`, and let every positive
integer up to `4h` be nonzero in `K`. Then no `A` monic of degree `h`, `B` of degree `≤ h` with
`B(0) ≠ 0`, and `q0 ≠ 0` satisfy `A ^ 3 + X ^ e B ^ 3 = q0 (X ^ (e + 2h) A + B)`. -/
theorem theoremK0_strong {A B : K[X]} {q0 : K} {h D : ℕ} (hD1 : 1 ≤ D) (hDh : 3 * D < h)
    (hchar : ∀ n, 0 < n → n ≤ 4 * h → (n : K) ≠ 0)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hq0 : q0 ≠ 0)
    (hident : A ^ 3 + X ^ (2 * h - D) * B ^ 3 = C q0 * (X ^ (2 * h - D + 2 * h) * A + B)) : False := by
  set e := 2 * h - D with he
  set R : K[X] := C q0 * X ^ (2 * h) * A - B ^ 3 with hR
  have hA3 : A ^ 3 = C q0 * B + X ^ e * R := by
    rw [hR]; rw [pow_add] at hident; linear_combination hident
  have hBR : B ^ 3 + R = C q0 * X ^ (2 * h) * A := by rw [hR]; ring
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hchar 2 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by exact_mod_cast hchar 4 (by omega) (by omega)
  have hA0 : A.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (eval 0) hA3
    simp only [eval_pow, eval_add, eval_mul, eval_C, eval_X, ← coeff_zero_eq_eval_zero, h0,
      zero_pow (by omega : e ≠ 0), zero_pow (by norm_num : 3 ≠ 0), zero_mul, add_zero] at this
    exact mul_ne_zero hq0 (by rw [coeff_zero_eq_eval_zero]; exact hB0) this.symm
  have hAne : A ≠ 0 := hAm.ne_zero
  -- degrees of `R` and `B`
  have hRdeg : R.natDegree ≤ h + D := by
    by_cases hR0 : R = 0
    · rw [hR0, natDegree_zero]; omega
    have h1 : (X ^ e * R).natDegree ≤ 3 * h := by
      have : X ^ e * R = A ^ 3 - C q0 * B := by linear_combination -hA3
      rw [this]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [natDegree_pow, hAd]
      · exact (natDegree_C_mul_le _ _).trans (by omega)
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hR0, natDegree_X_pow] at h1
    omega
  have hBdeg : B.natDegree = h := by
    have h1 : (C q0 * X ^ (2 * h) * A).natDegree = 3 * h := by
      rw [natDegree_mul (by simp [hq0]) hAne, natDegree_C_mul_X_pow _ _ hq0, hAd]; ring
    have h2' : (B ^ 3).natDegree = 3 * h := by
      have : B ^ 3 = C q0 * X ^ (2 * h) * A - R := by linear_combination hBR
      rw [this, natDegree_sub_eq_left_of_natDegree_lt (by rw [h1]; omega), h1]
    rw [natDegree_pow] at h2'; omega
  have hBne : B ≠ 0 := by rintro rfl; simp at hB0
  -- Lemma S
  have hθ : 3 * B ^ 2 * theta B + theta R = C q0 * X ^ (2 * h) * (C ((2 * h : ℕ) : K) * A + theta A) := by
    have e1 : theta (B ^ 3) = 3 * B ^ 2 * theta B := by
      rw [show B ^ 3 = B * (B * B) by ring, theta_mul, theta_mul]; ring
    have e2 : theta (C q0 * X ^ (2 * h) * A) =
        C q0 * X ^ (2 * h) * (C ((2 * h : ℕ) : K) * A + theta A) := by
      rw [mul_assoc, theta_C_mul, theta_mul, theta_X_pow]; ring
    have := congrArg theta hBR
    rw [theta_add, e1, e2] at this
    exact this
  set M : K[X] := 3 * A * theta B - B * theta A - C ((2 * h : ℕ) : K) * (A * B) with hM
  have hBM : B ^ 2 * M = (C ((2 * h : ℕ) : K) * A + theta A) * R - A * theta R := by
    rw [hM]; linear_combination A * hθ - (theta A + C ((2 * h : ℕ) : K) * A) * hBR
  have hMdeg : M.natDegree ≤ D := by
    by_cases hM0 : M = 0
    · rw [hM0, natDegree_zero]; omega
    have h1 : (B ^ 2 * M).natDegree ≤ 2 * h + D := by
      rw [hBM]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · have hX : (C ((2 * h : ℕ) : K) * A + theta A).natDegree ≤ h :=
          (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hAd.le)
            ((natDegree_theta_le A).trans hAd.le))
        exact natDegree_mul_le.trans ((add_le_add hX hRdeg).trans (by omega))
      · exact natDegree_mul_le.trans (add_le_add hAd.le ((natDegree_theta_le R).trans hRdeg)) |>.trans
          (by omega)
    rw [natDegree_mul (pow_ne_zero 2 hBne) hM0, natDegree_pow, hBdeg] at h1
    omega
  have hqB : C q0 * B = A ^ 3 - X ^ e * R := by linear_combination -hA3
  have hθqB : C q0 * theta B = 3 * A ^ 2 * theta A - theta (X ^ e * R) := by
    have e3 : theta (A ^ 3) = 3 * A ^ 2 * theta A := by
      rw [show A ^ 3 = A * (A * A) by ring, theta_mul, theta_mul]; ring
    rw [← theta_C_mul, hqB, theta_sub, e3]
  have hS : X ^ e ∣ M - 2 * theta (A * B) + C ((2 * h : ℕ) : K) * (A * B) := by
    have hid : C q0 * (M - 2 * theta (A * B) + C ((2 * h : ℕ) : K) * (A * B)) =
        3 * theta A * (X ^ e * R) - A * theta (X ^ e * R) := by
      rw [hM, theta_mul]; linear_combination A * hθqB - 3 * theta A * hqB
    have hd : X ^ e ∣ C q0 * (M - 2 * theta (A * B) + C ((2 * h : ℕ) : K) * (A * B)) := by
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
        (dvd_mul_of_dvd_right (X_pow_dvd_theta (dvd_mul_right _ _)) _)
    have hinv : (C q0⁻¹ * C q0 : K[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hq0, C_1]
    have := dvd_mul_of_dvd_right hd (C q0⁻¹)
    rwa [← mul_assoc, hinv, one_mul] at this
  have hAB : ∀ j, D < j → j < e → j ≠ h → (A * B).coeff j = 0 := by
    intro j hj1 hj2 h3
    have hc := (X_pow_dvd_iff.mp hS) j hj2
    rw [coeff_add, coeff_sub, coeff_eq_zero_of_natDegree_lt (hMdeg.trans_lt hj1), coeff_ofNat_mul,
      coeff_theta, coeff_C_mul] at hc
    have hne : (2 * ((h : K) - j)) ≠ 0 := by
      refine mul_ne_zero h2 ?_
      rcases Nat.lt_or_gt_of_ne h3 with hl | hl
      · have := hchar (h - j) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; exact this
      · have := hchar (j - h) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; intro h0; exact this (by linear_combination -h0)
    have : (2 * ((h : K) - j)) * (A * B).coeff j = 0 := by push_cast at hc; linear_combination hc
    exact (mul_eq_zero.mp this).resolve_left hne
  -- `AB ≡ Λ = L0 + c X ^ h (mod X ^ e)`
  set L0 := lowPart (D + 1) (A * B) with hL0
  set c := (A * B).coeff h with hcdef
  set Λ : K[X] := L0 + C c * X ^ h with hΛ
  have hABΛ : X ^ e ∣ A * B - Λ := by
    rw [X_pow_dvd_iff]; intro i hi
    rw [coeff_sub, hΛ, coeff_add, hL0, coeff_lowPart, coeff_C_mul_X_pow]
    by_cases h1 : i < D + 1
    · rw [ite_eq_left h1, ite_eq_right (by omega : i ≠ h)]; ring
    · rw [ite_eq_right h1]
      by_cases h2 : i = h
      · rw [ite_eq_left h2, h2]; ring
      · rw [ite_eq_right h2, hAB i (by omega) hi h2]; ring
  have h4th : X ^ e ∣ A ^ 4 - C q0 * Λ := by
    have : A ^ 4 - C q0 * Λ = C q0 * (A * B - Λ) + X ^ e * (A * R) := by
      linear_combination A * hA3
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hABΛ _) (dvd_mul_right _ _)
  have hW : X ^ e ∣ 4 * Λ * theta A - theta Λ * A := by
    have hd := X_pow_dvd_wronski_of_fourth h4th
    have hinv : (C q0⁻¹ * C q0 : K[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hq0, C_1]
    have := dvd_mul_of_dvd_right hd (C q0⁻¹)
    rwa [← mul_assoc, hinv, one_mul] at this
  have hL0_0 : L0.coeff 0 ≠ 0 := by
    rw [hL0, coeff_lowPart, ite_eq_left (by omega), coeff_zero_eq_eval_zero, eval_mul,
      ← coeff_zero_eq_eval_zero]
    exact mul_ne_zero hA0 hB0
  have hL0ne : L0 ≠ 0 := fun h0 => hL0_0 (by rw [h0, coeff_zero])
  have hL0deg : L0.natDegree ≤ D := natDegree_lowPart_le D _
  set P : K[X] := 4 * L0 * theta A - theta L0 * A with hP
  set G : K[X] := 4 * theta A - C (h : K) * A with hG
  have hWsplit : 4 * Λ * theta A - theta Λ * A = P + C c * X ^ h * G := by
    rw [hΛ, theta_add, theta_C_mul, theta_X_pow, hP, hG]; ring
  have hPdeg : P.natDegree ≤ D + h := natDegree_wronski4_le hL0deg hAd.le
  by_cases hc : c = 0
  · -- `c = 0`: `P = 0`, but its top coefficient is not
    have hP0 : P = 0 := by
      have hdv : X ^ e ∣ P := by
        have := hW; rw [hWsplit, hc, map_zero, zero_mul, zero_mul, add_zero] at this; exact this
      exact eq_zero_of_dvd_of_natDegree_lt hdv (by rw [natDegree_X_pow]; omega)
    have htop := coeff_wronski4_top (p := L0) (q := A)
    rw [← hP, hP0, coeff_zero, hAd, hAm.leadingCoeff, mul_one] at htop
    have hm : (4 * (h : K) - L0.natDegree) ≠ 0 := by
      have := hchar (4 * h - L0.natDegree) (by omega) (by omega)
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; exact this
    exact mul_ne_zero hm (mt leadingCoeff_eq_zero.mp hL0ne) htop.symm
  -- `c ≠ 0`
  have hWdvd := hW
  rw [hWsplit] at hWdvd
  have hcX : ∀ i, (C c * X ^ h * G).coeff i = if h ≤ i then c * G.coeff (i - h) else 0 := by
    intro i; rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']; split_ifs <;> simp
  have hPh : X ^ h ∣ P := by
    rw [X_pow_dvd_iff]; intro i hi
    have := (X_pow_dvd_iff.mp hWdvd) i (by omega)
    rw [coeff_add, hcX, ite_eq_right (by omega : ¬ h ≤ i), add_zero] at this; exact this
  have hGj : ∀ j, D < j → j < h - D → G.coeff j = 0 := by
    intro j hj1 hj2
    have := (X_pow_dvd_iff.mp hWdvd) (h + j) (by omega)
    rw [coeff_add, hcX, ite_eq_left (by omega : h ≤ h + j),
      coeff_eq_zero_of_natDegree_lt (hPdeg.trans_lt (by omega)), zero_add,
      show h + j - h = j by omega] at this
    exact (mul_eq_zero.mp this).resolve_left hc
  have hAj : ∀ j, D < j → j < h - D → h < 4 * j → A.coeff j = 0 := by
    intro j hj1 hj2 hj3
    have := hGj j hj1 hj2
    rw [hG, coeff_sub, coeff_ofNat_mul, coeff_theta, coeff_C_mul] at this
    have hm : ((4 * j - h : ℕ) : K) ≠ 0 := hchar _ (by omega) (by omega)
    rw [Nat.cast_sub (by omega)] at hm; push_cast at hm
    have : ((4 : K) * j - h) * A.coeff j = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left hm
  -- the truncation `a` of `A` below `h - D`
  set a := lowPart (h - D) A with ha
  have hadeg : a.natDegree ≤ max D (h / 4) := by
    rw [natDegree_le_iff_coeff_eq_zero]; intro i hi
    have hi' := max_lt_iff.mp hi
    rw [ha, coeff_lowPart]; split_ifs with h1
    · exact hAj i (by omega) h1 (by omega)
    · rfl
  have hadeg' : a.natDegree ≤ h := hadeg.trans (max_le (by omega) (by omega))
  have hAa : X ^ (h - D) ∣ A - a := X_pow_dvd_sub_lowPart _ _
  have hE0 : 4 * L0 * theta a - theta L0 * a = 0 := by
    have hd : X ^ (h - D) ∣ 4 * L0 * theta a - theta L0 * a := by
      have : 4 * L0 * theta a - theta L0 * a =
          P - (4 * L0 * theta (A - a) - theta L0 * (A - a)) := by rw [hP, theta_sub]; ring
      rw [this]
      exact dvd_sub ((pow_dvd_pow X (by omega)).trans hPh) (X_pow_dvd_wronski4 hAa)
    refine eq_zero_of_dvd_of_natDegree_lt hd ?_
    rw [natDegree_X_pow]
    refine (natDegree_wronski4_le hL0deg hadeg).trans_lt ?_
    rcases le_total D (h / 4) with hle | hle
    · rw [max_eq_right hle]; omega
    · rw [max_eq_left hle]; omega
  have ha0 : a.coeff 0 = A.coeff 0 := by rw [ha, coeff_lowPart, ite_eq_left (by omega)]
  have hane : a ≠ 0 := fun h0 => hA0 (by rw [← ha0, h0, coeff_zero])
  have h4a : 4 * a.natDegree = L0.natDegree := by
    have htop := coeff_wronski4_top (p := L0) (q := a)
    rw [hE0, coeff_zero] at htop
    by_contra hne
    have hm : (4 * (a.natDegree : K) - L0.natDegree) ≠ 0 := by
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · have := hchar (L0.natDegree - 4 * a.natDegree) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; push_cast at this
        intro h0; exact this (by linear_combination -h0)
      · have := hchar (4 * a.natDegree - L0.natDegree) (by omega) (by omega)
        rw [Nat.cast_sub hl.le] at this; push_cast at this; exact this
    exact mul_ne_zero (mul_ne_zero hm (mt leadingCoeff_eq_zero.mp hL0ne))
      (mt leadingCoeff_eq_zero.mp hane) htop.symm
  obtain ⟨Ah, hAh⟩ := hAa
  have hA_eq : A = a + X ^ (h - D) * Ah := by linear_combination hAh
  have hAhdeg : Ah.natDegree ≤ D := by
    by_cases hAh0 : Ah = 0
    · rw [hAh0, natDegree_zero]; omega
    have h1 : (A - a).natDegree ≤ h :=
      (natDegree_sub_le _ _).trans (max_le hAd.le hadeg')
    rw [hAh, natDegree_mul (pow_ne_zero _ X_ne_zero) hAh0, natDegree_X_pow] at h1
    omega
  obtain ⟨Z, hZ⟩ := h4th
  have hph : (X : K[X]) ^ h = X ^ (h - D) * X ^ D := by rw [← pow_add]; congr 1; omega
  have hpe : (X : K[X]) ^ e = X ^ (h - D) * X ^ h := by rw [← pow_add]; congr 1; omega
  have hZ' : (a + X ^ (h - D) * Ah) ^ 4 - C q0 * (L0 + C c * X ^ h) = X ^ e * Z := by
    rw [← hA_eq, ← hΛ]; exact hZ
  have key : a ^ 4 - C q0 * L0 = X ^ (h - D) * (X ^ h * Z - Ah * (4 * a ^ 3 +
      6 * a ^ 2 * (X ^ (h - D) * Ah) + 4 * a * (X ^ (h - D) * Ah) ^ 2 + (X ^ (h - D) * Ah) ^ 3) +
      C q0 * C c * X ^ D) := by
    linear_combination hZ' + C q0 * C c * hph + Z * hpe
  have ha4 : a ^ 4 = C q0 * L0 := by
    have hd : X ^ (h - D) ∣ a ^ 4 - C q0 * L0 := ⟨_, key⟩
    have h0 := eq_zero_of_dvd_of_natDegree_lt hd (by
      rw [natDegree_X_pow]
      refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · exact (natDegree_pow_le).trans_lt (by omega)
      · exact (natDegree_C_mul_le _ _).trans_lt (by omega))
    linear_combination h0
  have inner : X ^ h * Z - Ah * (4 * a ^ 3 + 6 * a ^ 2 * (X ^ (h - D) * Ah) +
      4 * a * (X ^ (h - D) * Ah) ^ 2 + (X ^ (h - D) * Ah) ^ 3) + C q0 * C c * X ^ D = 0 := by
    have : X ^ (h - D) * (X ^ h * Z - Ah * (4 * a ^ 3 + 6 * a ^ 2 * (X ^ (h - D) * Ah) +
        4 * a * (X ^ (h - D) * Ah) ^ 2 + (X ^ (h - D) * Ah) ^ 3) + C q0 * C c * X ^ D) = 0 := by
      rw [← key, ha4, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ X_ne_zero)
  have hlin : 4 * a ^ 3 * Ah - C q0 * C c * X ^ D = 0 := by
    have hd : X ^ (h - D) ∣ 4 * a ^ 3 * Ah - C q0 * C c * X ^ D :=
      ⟨X ^ D * Z - Ah * (6 * a ^ 2 * Ah + 4 * a * X ^ (h - D) * Ah ^ 2 +
        X ^ (h - D) * X ^ (h - D) * Ah ^ 3), by linear_combination -inner + Z * hph⟩
    refine eq_zero_of_dvd_of_natDegree_lt hd ?_
    rw [natDegree_X_pow]
    refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · refine natDegree_mul_le.trans_lt ?_
      have : (4 * a ^ 3).natDegree ≤ 3 * a.natDegree :=
        natDegree_mul_le.trans (by simp)
      omega
    · rw [← C_mul]; exact (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  -- `a` is constant
  have h4Ah : a ^ 3 * (4 * Ah) = C q0 * C c * X ^ D := by linear_combination hlin
  have hcopX : IsCoprime (X : K[X]) a :=
    (irreducible_X.coprime_iff_not_dvd).mpr (by rw [X_dvd_iff, ha0]; exact hA0)
  have hqc : C q0 * C c * X ^ D ≠ 0 := by
    rw [← C_mul]; exact mul_ne_zero (by simp [hq0, hc]) (pow_ne_zero _ X_ne_zero)
  have hne4 : 4 * Ah ≠ 0 := by intro h0; rw [h0, mul_zero] at h4Ah; exact hqc h4Ah.symm
  have hdv : X ^ D ∣ 4 * Ah :=
    (hcopX.pow (m := D) (n := 3)).dvd_of_dvd_mul_left (by rw [h4Ah]; exact dvd_mul_left _ _)
  have hdeg4 : D ≤ (4 * Ah).natDegree := by
    have := natDegree_le_of_dvd hdv hne4; rwa [natDegree_X_pow] at this
  have hda0 : a.natDegree = 0 := by
    have := congrArg natDegree h4Ah
    rw [natDegree_mul (pow_ne_zero 3 hane) hne4, natDegree_pow, ← C_mul,
      natDegree_C_mul_X_pow _ _ (mul_ne_zero hq0 hc)] at this
    omega
  have haC : a = C (A.coeff 0) := by rw [eq_C_of_natDegree_eq_zero hda0, ha0]
  have ha3 : a ^ 3 = C (A.coeff 0 ^ 3) := by rw [haC, C_pow]
  have hAhC : Ah = C (Ah.coeff D) * X ^ D := by
    ext i
    rw [coeff_C_mul_X_pow]
    split_ifs with hi
    · rw [hi]
    · have := congrArg (fun p => p.coeff i) h4Ah
      rw [ha3, coeff_C_mul, coeff_ofNat_mul, ← C_mul, coeff_C_mul_X_pow, ite_eq_right hi] at this
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hA0))).resolve_left h4
  generalize hκ : Ah.coeff D = κ at hAhC
  have h1 : A = C (A.coeff 0) + C κ * X ^ h := by
    conv_lhs => rw [hA_eq]
    rw [haC, hAhC, hph]; ring
  have h2 : A.coeff h = 1 := by rw [← hAd]; exact hAm
  have h3 : κ = 1 := by
    have h2' := h2
    rw [h1, coeff_add, coeff_C, coeff_C_mul_X_pow, ite_eq_left rfl, ite_eq_right (by omega : h ≠ 0),
      zero_add] at h2'
    exact h2'
  have hAform : A = X ^ h + C (A.coeff 0) := by
    conv_lhs => rw [h1]
    rw [h3, map_one, one_mul]; ring
  exact final_step hD1 (by omega) hq0 hBd hAform hA3 hBR


/-- **Theorem K0 for `3D < h`**, with result 29's characteristic hypothesis: characteristic `0` or above `4h`. -/
theorem theoremK0_strong_ringChar {A B : K[X]} {q0 : K} {h D : ℕ} (hD1 : 1 ≤ D) (hDh : 3 * D < h)
    (hchar : ringChar K = 0 ∨ 4 * h < ringChar K)
    (hAm : A.Monic) (hAd : A.natDegree = h) (hBd : B.natDegree ≤ h) (hB0 : B.eval 0 ≠ 0)
    (hq0 : q0 ≠ 0)
    (hident : A ^ 3 + X ^ (2 * h - D) * B ^ 3 = C q0 * (X ^ (2 * h - D + 2 * h) * A + B)) : False :=
  theoremK0_strong hD1 hDh (fun _ h0 h1 => natCast_ne_zero_of_char hchar h0 h1) hAm hAd hBd hB0 hq0 hident

end TheoremK0Strong

namespace InteriorThreeTheoremK0Strong

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

/-- **The `k = 0` cells with `h > 3D` are empty over M31** (inner exponent `m = 5q + δ`). -/
theorem ambient_and_native_vanishing_m31_k0s_inner
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hk0 : h = 2 * (2 ^ (r - 3) - δ)) (hD1 : 1 ≤ 5 * 2 ^ (r - 3) - 7 * δ)
    (hD4 : 3 * (5 * 2 ^ (r - 3) - 7 * δ) < h)
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
    exact TheoremK0Strong.theoremK0_strong_ringChar (by omega : 1 ≤ 5 * q_oct - 7 * δ) (by omega)
      (Or.inr (by rw [hrchar]; omega)) hAm hAd hBd hB0 hq0ne hident'
  refine ⟨hno_amb, fun L hL ↦ ?_⟩
  have hL_empty : L = ∅ := by
    by_contra hne
    obtain ⟨P, hP_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨hP_nat, hP_ag⟩ := hL P hP_mem
    exact hno_amb ⟨P, hP_nat.1, hP_ag⟩
  rw [hL_empty, Finset.card_empty, Nat.cast_zero]

/-- The mirror `m = 7q - δ` of `ambient_and_native_vanishing_m31_k0s_inner`, by Frobenius inversion
(adapted from M-0998). -/
theorem ambient_and_native_vanishing_m31_k0s_mirror
    {F : Type*} [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2)
    {r : ℕ} (hr_lo : 5 ≤ r) (hr_hi : r ≤ 31)
    {D : Finset F} (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1)
    {δ h : ℕ} (hδ_pos : 1 ≤ δ) (hδ_lt : δ < 2 ^ (r - 3)) (hh_le : h ≤ δ)
    (hqh : 2 ^ (r - 3) + h < 3 * δ)
    (hk0 : h = 2 * (2 ^ (r - 3) - δ)) (hD1 : 1 ≤ 5 * 2 ^ (r - 3) - 7 * δ)
    (hD4 : 3 * (5 * 2 ^ (r - 3) - 7 * δ) < h)
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
  have hinner := ambient_and_native_vanishing_m31_k0s_inner hF hr_lo hr_hi
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

/-- The `k = 0` stratum with `h > 3D`: `u + 3δ = 5q`, `D = 5q - 7δ ≥ 1`, `3D < 2(q - δ)`. -/
def InSingleK0StrongStratum (r m u : ℕ) : Prop :=
  5 ≤ r ∧
  ∃ δ : ℕ, 1 ≤ δ ∧ δ < 2 ^ (r - 3) ∧
    (m = 5 * 2 ^ (r - 3) + δ ∨ m = 7 * 2 ^ (r - 3) - δ) ∧
    u + 3 * δ = 5 * 2 ^ (r - 3) ∧
    1 ≤ 5 * 2 ^ (r - 3) - 7 * δ ∧
    3 * (5 * 2 ^ (r - 3) - 7 * δ) < 2 * (2 ^ (r - 3) - δ)

/-- **Every `k = 0` cell with `h > 3D` is empty over M31:** `¬ IsValidCWComplement D r (X ^ m) γ U`
on `InSingleK0StrongStratum`, at every dyadic `5 ≤ r ≤ 31`, by Theorem K0. -/
theorem singleMonomialK0StrongVanishing.{u} (F : Type u) [Field F] [DecidableEq F]
    (hF : Nat.card F = (2 ^ 31 - 1) ^ 2) {r : ℕ} (hr_hi : r ≤ 31) {D : Finset F}
    (hD_card : D.card = 2 ^ r) (hD_pow : ∀ x ∈ D, x ^ (2 ^ r) = 1) {m : ℕ} (γ : F) (U : Finset F)
    (hstrat : InSingleK0StrongStratum r m U.card) : ¬ IsValidCWComplement D r ((X : F[X]) ^ m) γ U := by
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
  · exact (ambient_and_native_vanishing_m31_k0s_inner hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh rfl hD1 hD4 one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩
  · exact (ambient_and_native_vanishing_m31_k0s_mirror hF hr5 hr_hi
      hD_card hD_pow hδ1 hδ_lt hh_le hqh rfl hD1 hD4 one_ne_zero 0 (by simp)).1
      ⟨P, hP_deg, by rw [hS_eq]; exact hS_filt⟩

/-- The single-monomial residual after Theorem W, CW*, Lemma Q'_ℓ, the M31 boundary (Lemma CG) and the
`k = 0`, `h > 3D` cells (Theorem K0). -/
def SingleMonomialResidualAfterK0StrongBound.{u} (K : ℕ) : Prop :=
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
            ¬ InSingleK0StrongStratum r m U.card) →
          𝒰.card ≤ K * 2 ^ r

/-- `SingleMonomialResidualAfterK0StrongBound K` implies `SingleMonomialResidualAfterCGBound K`. -/
theorem singleMonomialResidualAfterCG_of_after_K0Strong.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterK0StrongBound.{u} K) :
    SingleMonomialResidualAfterCGBound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 h𝒰
  refine hRem F hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
  obtain ⟨hvalid, hnotW, hnotCWStar, hnotQP, hnotCG⟩ := h𝒰 U hUm
  exact ⟨hvalid, hnotW, hnotCWStar, hnotQP, hnotCG,
    fun hk ↦ singleMonomialK0StrongVanishing F hF hr_hi hD_card hD_pow γ U hk hvalid⟩

/-- **`MCAChallenge.InteriorThree K` reduced to the residual after Lemma CG and Theorem K0** and
`MultiMonomialCanonicalCWBound K` (`1 ≤ K ≤ 2 ^ 20`, every dyadic `4 ≤ r ≤ 31`). -/
theorem interiorThree_of_cwStar_qPrime_cg_k0s_and_multi_sublemmas.{u} {K : ℕ}
    (hK_pos : 1 ≤ K) (hK_cap : K ≤ 2 ^ 20)
    (hRem : SingleMonomialResidualAfterK0StrongBound.{u} K)
    (hMulti : MultiMonomialCanonicalCWBound.{u} K) :
    MCAChallenge.InteriorThree.{u} K :=
  interiorThree_of_cwStar_qPrime_cg_and_multi_sublemmas hK_pos hK_cap
    (singleMonomialResidualAfterCG_of_after_K0Strong hRem) hMulti


/-- The `4D < h` stratum of `InteriorThree_TheoremK0Residual` lies inside the `3D < h` stratum. -/
theorem inSingleK0StrongStratum_of_K0 {r m u : ℕ}
    (hs : InteriorThreeTheoremK0Residual.InSingleK0Stratum r m u) : InSingleK0StrongStratum r m u := by
  obtain ⟨hr5, δ, hδ1, hδ_lt, hm, hu, hD1, hD4⟩ := hs
  exact ⟨hr5, δ, hδ1, hδ_lt, hm, hu, hD1, by omega⟩

/-- `SingleMonomialResidualAfterK0StrongBound K` implies `SingleMonomialResidualAfterK0Bound K`. -/
theorem singleMonomialResidualAfterK0_of_after_K0Strong.{u} {K : ℕ}
    (hRem : SingleMonomialResidualAfterK0StrongBound.{u} K) :
    InteriorThreeTheoremK0Residual.SingleMonomialResidualAfterK0Bound.{u} K := by
  intro F _ _ hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 h𝒰
  refine hRem F hF r hr_lo hr_hi D hD_card hD_pow m hm_lo hm_hi γ 𝒰 (fun U hUm ↦ ?_)
  obtain ⟨hvalid, hnotW, hnotCWStar, hnotQP, hnotCG, _⟩ := h𝒰 U hUm
  exact ⟨hvalid, hnotW, hnotCWStar, hnotQP, hnotCG,
    fun hk ↦ singleMonomialK0StrongVanishing F hF hr_hi hD_card hD_pow γ U hk hvalid⟩

end InteriorThreeTheoremK0Strong
